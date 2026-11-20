// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Initializable} from "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import {Ownable2StepUpgradeable} from "@openzeppelin/contracts-upgradeable/access/Ownable2StepUpgradeable.sol";
import {PausableUpgradeable} from "@openzeppelin/contracts-upgradeable/utils/PausableUpgradeable.sol";
import {UUPSUpgradeable} from "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import {EIP712Upgradeable} from "@openzeppelin/contracts-upgradeable/utils/cryptography/EIP712Upgradeable.sol";
import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {IMergeDeciderVerifier, NovaDeciderProof} from "./interfaces/INovaDeciderVerifier.sol";
import {Groth16Proof, IJoinSplitVerifier, IRageExitVerifier} from "./interfaces/IPrivateProofVerifier.sol";
import {ITokenRegistry} from "./interfaces/ITokenRegistry.sol";
import {ITokenStop} from "./interfaces/ITokenStop.sol";
import {CommitmentLedger} from "./CommitmentLedger.sol";
import {ZERC20} from "./ZERC20.sol";
import {FeeSchedule} from "./libs/FeeSchedule.sol";
import {Protocol} from "./libs/Protocol.sol";

/// @title Verifier
/// @dev UUPS proxy; future implementations must retain this namespace. Upgrades are owner-only.
/// @notice Verifies JoinSplit, Rage Exit and Merge proofs, spends nullifiers, mints public withdrawals,
///         and appends output notes. Public-signal order is outputs first, exactly as emitted by Circom.
///         Transact and merge also need an EIP-712 attestation of the same statement from an attester
///         (a TEE that re-checks the witness), so a circuit soundness bug alone cannot move funds. Rage
///         exit stays permissionless as the escape hatch.
contract Verifier layout at erc7201("zerc20.storage.Verifier")
    is
    Initializable,
    Ownable2StepUpgradeable,
    PausableUpgradeable,
    ReentrancyGuardTransient,
    UUPSUpgradeable,
    EIP712Upgradeable,
    ITokenStop
{
    using FeeSchedule for FeeSchedule.Schedule;

    /// @dev EIP-712 statements an attester signs: exactly the public statement of each proof.
    bytes32 private constant TRANSACT_TYPEHASH = keccak256(
        "Transact(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256 nullifier0,"
        "uint256 nullifier1,uint256 withdrawRecipient,uint256 withdrawAmount,uint256 withdrawIntent,uint256 noteHash1,"
        "uint256 noteHash2)"
    );
    bytes32 private constant MERGE_TYPEHASH = keccak256(
        "Merge(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256[] nullifiers,"
        "uint256 noteHash,uint256 fee,uint256 feeRecipient)"
    );

    struct TransactSignals {
        uint256 tokenId;
        uint256 chainId;
        uint256 commitmentRoot;
        uint256 aspRoot;
        uint256 nullifier0;
        uint256 nullifier1;
        uint256 withdrawRecipient;
        uint256 withdrawAmount;
        // How the withdrawal is paid out (`Protocol.UNWRAP_INTENT` or 0); zero without a withdrawal.
        uint256 withdrawIntent;
        uint256 noteHash1;
        uint256 noteHash2;
    }

    struct TransactRequest {
        uint64 rootIndex;
        Groth16Proof proof;
        TransactSignals publicSignals;
        // An attester's EIP-712 signature over `publicSignals` (`Transact`).
        bytes attestation;
    }

    /// @dev One folded step per nullifier, in order; `noteHash` is the merged output note, worth the inputs less
    ///      `fee`, which is minted publicly to `feeRecipient` (the relayer that sends it; zero for none).
    struct MergeRequest {
        uint64 rootIndex;
        uint256 tokenId;
        uint256 commitmentRoot;
        uint256 aspRoot;
        uint256 noteHash;
        uint256 fee;
        uint256 feeRecipient;
        uint256[] nullifiers;
        NovaDeciderProof proof;
        // An attester's EIP-712 signature over the merge statement (`Merge`).
        bytes attestation;
    }

    /// @dev The deposit is authenticated on the ledger hash chain, not against a proved root:
    ///      `commitments` are the deposit and every later commitment before `checkpointIndex`, and
    ///      `prevHashChain` is the chain right before the deposit (see `CommitmentLedger.verifySegment`).
    struct RageExitRequest {
        uint64 checkpointIndex;
        uint256 prevHashChain;
        uint256[4][] commitments;
        uint256 nullifier;
        Groth16Proof proof;
    }

    /// @dev Complete project-owned storage. Append new fields at the end only.
    /// @custom:storage-location erc7201:zerc20.storage.Verifier
    struct VerifierStorage {
        ITokenRegistry factory;
        CommitmentLedger ledger;
        IJoinSplitVerifier joinSplitVerifier;
        IRageExitVerifier rageExitVerifier;
        IMergeDeciderVerifier mergeVerifier;
        mapping(uint256 nullifier => bool) nullifierUsed;
        // The only account that may publish ASP roots.
        address aspPublisher;
        // Bumped from 1 each time the publisher is set. Only roots published in the current epoch are
        // accepted, so a root never published (epoch 0) never is.
        uint64 aspEpoch;
        // The root published last. Wallets prove against it, so every spend shows the same root.
        uint256 latestAspRoot;
        mapping(uint256 aspRoot => uint64 epoch) aspRootEpoch;
        // Keys allowed to attest transact / merge statements (1-of-N).
        mapping(address attester => bool) attesters;
        // Per-token stop of private operations (transact / rageExit / merge), and through `tokenStopped` of every
        // balance change of the token itself, fee claims included.
        mapping(uint32 tokenId => bool) tokenPaused;
        // Per-token withdrawal fee schedule. A token with no schedule charges no fee.
        mapping(uint32 tokenId => FeeSchedule.Schedule) fees;
        // Fees are minted to this contract and owed to the recipient recorded at settlement.
        mapping(uint32 tokenId => mapping(address recipient => uint256)) accruedFees;
    }

    VerifierStorage private _verifierStorage;

    event AspRootPublished(uint256 indexed aspRoot);
    event AspPublisherSet(address indexed publisher);
    event AttesterSet(address indexed attester, bool allowed);
    event NullifierSpent(uint256 indexed nullifier);
    event Transacted(
        address indexed caller,
        uint32 indexed tokenId,
        uint256 indexed commitmentRoot,
        address withdrawRecipient,
        uint256 withdrawAmount,
        uint256 feeAmount,
        uint256 noteHash1,
        uint256 noteHash2,
        uint64 noteIndex1,
        uint64 noteIndex2
    );
    event Merged(
        address indexed caller,
        uint32 indexed tokenId,
        uint256 indexed commitmentRoot,
        uint256 inputCount,
        uint256 noteHash,
        uint64 noteIndex
    );
    event RageExited(
        address indexed caller, uint32 indexed tokenId, address recipient, uint256 amount, uint256 nullifier
    );
    event TokenPausedUpdated(uint32 indexed tokenId, bool paused);
    event FeeSet(uint32 indexed tokenId, address indexed recipient, uint256 tierCount);
    event FeeAccrued(uint32 indexed tokenId, address indexed recipient, uint256 amount);
    event FeesClaimed(uint32 indexed tokenId, address indexed recipient, uint256 amount);
    event JoinSplitVerifierSet(IJoinSplitVerifier verifier);
    event RageExitVerifierSet(IRageExitVerifier verifier);
    event MergeVerifierSet(IMergeDeciderVerifier verifier);

    error Unauthorized(address caller);
    error InvalidField(uint256 value);
    error InvalidAmount(uint256 amount);
    error InvalidAddress(uint256 value);
    error InvalidChainId(uint256 actual, uint256 expected);
    error UnregisteredToken(uint256 tokenId);
    error UnprovedRoot(uint64 index, uint256 root);
    error UnacceptedAspRoot(uint256 aspRoot);
    error NullifierAlreadyUsed(uint256 nullifier);
    error DuplicateNullifier(uint256 nullifier);
    error EmptyMerge();
    error NotATransfer(uint64 index);
    error UnauthorizedAttestation(address signer);
    error NonCanonicalRecipient(uint256 recipient);
    error UnsupportedWithdrawIntent(uint256 intent);
    error ZeroRecipient();
    error ZeroAddress();
    error InvalidProof();
    error TokenPaused(uint32 tokenId);
    error BlockedAddress(address account);
    error AcceptsEmptyProof(address verifier);

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    function initialize(
        address owner_,
        ITokenRegistry factory_,
        CommitmentLedger ledger_,
        IJoinSplitVerifier joinSplitVerifier_,
        IRageExitVerifier rageExitVerifier_,
        IMergeDeciderVerifier mergeVerifier_,
        address aspPublisher_
    ) external initializer {
        __Ownable_init(owner_);
        __Pausable_init();
        __EIP712_init("zERC20 Verifier", "1");

        VerifierStorage storage $ = _verifierStorage;
        $.factory = factory_;
        $.ledger = ledger_;
        $.joinSplitVerifier = joinSplitVerifier_;
        $.rageExitVerifier = rageExitVerifier_;
        $.mergeVerifier = mergeVerifier_;
        _setAspPublisher(aspPublisher_);
    }

    // ---- views ---------------------------------------------------------------------------------

    function factory() external view returns (ITokenRegistry) {
        return _verifierStorage.factory;
    }

    function ledger() external view returns (CommitmentLedger) {
        return _verifierStorage.ledger;
    }

    function joinSplitVerifier() external view returns (IJoinSplitVerifier) {
        return _verifierStorage.joinSplitVerifier;
    }

    function mergeVerifier() external view returns (IMergeDeciderVerifier) {
        return _verifierStorage.mergeVerifier;
    }

    function rageExitVerifier() external view returns (IRageExitVerifier) {
        return _verifierStorage.rageExitVerifier;
    }

    function isAttester(address account) external view returns (bool) {
        return _verifierStorage.attesters[account];
    }

    function aspPublisher() external view returns (address) {
        return _verifierStorage.aspPublisher;
    }

    function nullifierUsed(uint256 nullifier) external view returns (bool) {
        return _verifierStorage.nullifierUsed[nullifier];
    }

    function aspRootAccepted(uint256 aspRoot) public view returns (bool) {
        return _verifierStorage.aspRootEpoch[aspRoot] == _verifierStorage.aspEpoch;
    }

    function latestAspRoot() external view returns (uint256) {
        return _verifierStorage.latestAspRoot;
    }

    function tokenPaused(uint32 tokenId) external view returns (bool) {
        return _verifierStorage.tokenPaused[tokenId];
    }

    /// @notice Whether every balance change of `tokenId` is stopped: the Verifier or that token is paused.
    function tokenStopped(uint32 tokenId) external view returns (bool) {
        return paused() || _verifierStorage.tokenPaused[tokenId];
    }

    function accruedFees(uint32 tokenId, address recipient) external view returns (uint256) {
        return _verifierStorage.accruedFees[tokenId][recipient];
    }

    /// @notice Fee charged on a gross withdrawal of `amount`.
    function withdrawFee(uint32 tokenId, uint256 amount) public view returns (uint256) {
        return _verifierStorage.fees[tokenId].quote(amount);
    }

    function feeRecipient(uint32 tokenId) external view returns (address) {
        return _verifierStorage.fees[tokenId].recipient;
    }

    // ---- private operations --------------------------------------------------------------------

    /// @notice Spend up to two notes, optionally withdraw publicly, and create two output notes.
    function transact(TransactRequest calldata request) external nonReentrant whenNotPaused {
        TransactSignals calldata s = request.publicSignals;
        ZERC20 token = _token(s.tokenId);
        _validate(request.rootIndex, s);
        _checkAttestation(keccak256(abi.encode(TRANSACT_TYPEHASH, s)), request.attestation);
        _verifyJoinSplit(request.proof, s);

        _spend(s.nullifier0);
        _spend(s.nullifier1);

        uint64 noteIndex1 = token.commitNote(s.noteHash1);
        uint64 noteIndex2 = token.commitNote(s.noteHash2);

        // Last: paying out the native asset calls the recipient.
        address recipient = address(uint160(s.withdrawRecipient));
        bool unwrap = s.withdrawIntent == Protocol.UNWRAP_INTENT;
        // forge-lint: disable-next-line(unsafe-typecast)
        uint256 fee = _settleWithdraw(token, uint32(s.tokenId), recipient, s.withdrawAmount, unwrap);
        // forge-lint: disable-next-line(unsafe-typecast)
        emit Transacted(
            msg.sender,
            uint32(s.tokenId),
            s.commitmentRoot,
            recipient,
            s.withdrawAmount,
            fee,
            s.noteHash1,
            s.noteHash2,
            noteIndex1,
            noteIndex2
        );
    }

    /// @notice Spend N >= 1 notes or burn deposits into one private note, proven by Nova folding.
    function merge(MergeRequest calldata request) external nonReentrant whenNotPaused {
        ZERC20 token = _token(request.tokenId);
        _validate(request);
        _checkAttestation(_mergeStatement(request), request.attestation);
        _verifyMerge(request, _nullifierChain(request.nullifiers));

        // Also rejects a nullifier repeated within the request.
        for (uint256 k; k < request.nullifiers.length; ++k) {
            _spend(request.nullifiers[k]);
        }

        uint64 noteIndex = token.commitNote(request.noteHash);
        // forge-lint: disable-next-line(unsafe-typecast)
        _settleWithdraw(token, uint32(request.tokenId), address(uint160(request.feeRecipient)), request.fee, false);
        // forge-lint: disable-next-line(unsafe-typecast)
        emit Merged(
            msg.sender,
            uint32(request.tokenId),
            request.commitmentRoot,
            request.nullifiers.length,
            request.noteHash,
            noteIndex
        );
    }

    /// @notice Permissionless refund of a burn deposit, provable without the ASP or a proved root.
    function rageExit(RageExitRequest calldata request) external nonReentrant whenNotPaused {
        uint64 index =
            _verifierStorage.ledger.verifySegment(request.checkpointIndex, request.prevHashChain, request.commitments);
        uint256[4] calldata deposit = request.commitments[0];
        (uint32 tag, uint32 tokenId) = Protocol.decode(deposit[0]);
        require(tag == Protocol.TRANSFER_TAG, NotATransfer(index));
        ZERC20 token = _token(tokenId);
        _checkField(request.nullifier);
        _verifyRageExit(request.proof, [request.nullifier, block.chainid, index, deposit[2]]);

        _spend(request.nullifier);

        // A committed transfer always has a real sender and a non-zero value.
        address recipient = address(uint160(deposit[1]));
        token.payOut(recipient, deposit[3], false);
        emit RageExited(msg.sender, tokenId, recipient, deposit[3], request.nullifier);
    }

    // ---- ASP -----------------------------------------------------------------------------------

    /// @notice The ASP tree is append-only, so an older root approves a subset of a newer one. Older
    ///         roots therefore stay accepted, which spares proofs that are in flight.
    function publishAspRoot(uint256 aspRoot) external {
        VerifierStorage storage $ = _verifierStorage;
        require(msg.sender == $.aspPublisher, Unauthorized(msg.sender));
        require(aspRoot != 0 && aspRoot < Protocol.FIELD_MODULUS, InvalidField(aspRoot));
        $.aspRootEpoch[aspRoot] = $.aspEpoch;
        $.latestAspRoot = aspRoot;
        emit AspRootPublished(aspRoot);
    }

    /// @notice Replace the ASP publisher and drop every root published so far, e.g. after a key leak
    ///         or a bad root. The tree is append-only, so the new publisher's first root brings back
    ///         every honest approval. Proofs against a dropped root must be redone.
    function setAspPublisher(address publisher) external onlyOwner {
        _setAspPublisher(publisher);
    }

    /// @notice Drop the publisher and every root published so far: transact and merge stop until the admin names
    ///         a new publisher, while rage exits, wraps, unwraps and transfers go on. Stop-only, so a leaked key
    ///         or a bad root can be answered at once.
    function revokeAspPublisher() external onlyOwner {
        _setAspPublisher(address(0));
    }

    function _setAspPublisher(address publisher) private {
        VerifierStorage storage $ = _verifierStorage;
        $.aspPublisher = publisher;
        ++$.aspEpoch;
        $.latestAspRoot = 0;
        emit AspPublisherSet(publisher);
    }

    // ---- proof verifiers ----------------------------------------------------------------------
    // The owner swaps one, so that a broken circuit or a leaked setup is answered by its verifier alone, once `pause`
    // has stopped what it checks. A replacement takes the same public signals, and must reject an empty proof, so
    // that an address that answers every call, as an account without code or a permissive fallback does, cannot take
    // every proof.

    function setJoinSplitVerifier(IJoinSplitVerifier verifier) external onlyOwner {
        Groth16Proof memory none;
        uint256[11] memory signals;
        _requireRejectsEmptyProof(
            address(verifier), abi.encodeCall(IJoinSplitVerifier.verifyProof, (none.pA, none.pB, none.pC, signals))
        );
        _verifierStorage.joinSplitVerifier = verifier;
        emit JoinSplitVerifierSet(verifier);
    }

    function setRageExitVerifier(IRageExitVerifier verifier) external onlyOwner {
        Groth16Proof memory none;
        uint256[4] memory signals;
        _requireRejectsEmptyProof(
            address(verifier), abi.encodeCall(IRageExitVerifier.verifyProof, (none.pA, none.pB, none.pC, signals))
        );
        _verifierStorage.rageExitVerifier = verifier;
        emit RageExitVerifierSet(verifier);
    }

    function setMergeVerifier(IMergeDeciderVerifier verifier) external onlyOwner {
        NovaDeciderProof memory none;
        uint256[10] memory zero;
        _requireRejectsEmptyProof(
            address(verifier),
            abi.encodeCall(
                IMergeDeciderVerifier.verifyDeciderProof,
                (
                    1,
                    zero,
                    zero,
                    none.challenge,
                    none.runningCmE,
                    none.cmT,
                    none.runningCmW,
                    none.incomingCmW,
                    none.proof
                )
            )
        );
        _verifierStorage.mergeVerifier = verifier;
        emit MergeVerifierSet(verifier);
    }

    /// @dev Accepted means the call returned anything but `false`: a Groth16 verifier answers `false`, a decider
    ///      reverts, and an account without code returns nothing.
    function _requireRejectsEmptyProof(address verifier, bytes memory emptyProofCall) private view {
        (bool ok, bytes memory answer) = verifier.staticcall(emptyProofCall);
        require(!ok || (answer.length == 32 && !abi.decode(answer, (bool))), AcceptsEmptyProof(verifier));
    }

    // ---- attesters ----------------------------------------------------------------------------

    /// @notice Allow an attester key.
    function addAttester(address attester) external onlyOwner {
        require(attester != address(0), ZeroAddress());
        _verifierStorage.attesters[attester] = true;
        emit AttesterSet(attester, true);
    }

    /// @notice Revoke an attester key, e.g. a leaked one; its outstanding signatures stop counting at once.
    ///         Stop-only, so it can be instant.
    function revokeAttester(address attester) external onlyOwner {
        _verifierStorage.attesters[attester] = false;
        emit AttesterSet(attester, false);
    }

    // ---- stop controls: stopping and resuming are separate so only stopping can be made instant ----
    // Either pause also stops the token itself (wrap, unwrap, transfer; see `tokenStopped`). Neither moves funds.

    function pause() external onlyOwner {
        _pause();
    }

    function unpause() external onlyOwner {
        _unpause();
    }

    function pauseToken(uint32 tokenId) external onlyOwner {
        _setTokenPaused(tokenId, true);
    }

    function unpauseToken(uint32 tokenId) external onlyOwner {
        _setTokenPaused(tokenId, false);
    }

    // ---- fees ----------------------------------------------------------------------------------

    /// @notice Set a token's withdrawal fee schedule (replaces any previous one; applies to later withdrawals).
    /// @dev Fees are computed on-chain from the gross amount, so changing them never invalidates a proof.
    function setFee(uint32 tokenId, address recipient, FeeSchedule.Tier[] calldata tiers) external onlyOwner {
        address t = _verifierStorage.factory.tokenById(tokenId);
        require(t != address(0), UnregisteredToken(tokenId));

        bool charges = _verifierStorage.fees[tokenId].set(recipient, tiers);
        require(!charges || !ZERC20(payable(t)).isBlocked(recipient), BlockedAddress(recipient));
        emit FeeSet(tokenId, recipient, tiers.length);
    }

    /// @notice Pay out fees accrued for `recipient`. Anyone may trigger it; funds only go to `recipient`.
    function claimFees(uint32 tokenId, address recipient) external nonReentrant returns (uint256 amount) {
        VerifierStorage storage $ = _verifierStorage;
        amount = $.accruedFees[tokenId][recipient];
        if (amount == 0) return 0;
        $.accruedFees[tokenId][recipient] = 0;
        // A blocked recipient reverts here and stays frozen until unblocked. ZERC20 reverts rather than return false.
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        ZERC20(payable($.factory.tokenById(tokenId))).transfer(recipient, amount);
        emit FeesClaimed(tokenId, recipient, amount);
    }

    // ---- validation ----------------------------------------------------------------------------

    function _validate(uint64 rootIndex, TransactSignals calldata s) private view {
        _checkRoot(rootIndex, s.chainId, s.commitmentRoot);
        _checkField(s.aspRoot);
        _checkField(s.nullifier0);
        _checkField(s.nullifier1);
        _checkField(s.noteHash1);
        _checkField(s.noteHash2);
        _checkAmount(s.withdrawAmount);
        _checkAddress(s.withdrawRecipient);

        require(aspRootAccepted(s.aspRoot), UnacceptedAspRoot(s.aspRoot));
        require(s.nullifier0 != s.nullifier1, DuplicateNullifier(s.nullifier0));
        _checkUnspent(s.nullifier0);
        _checkUnspent(s.nullifier1);
        if (s.withdrawAmount == 0) {
            require(s.withdrawRecipient == 0, NonCanonicalRecipient(s.withdrawRecipient));
            require(s.withdrawIntent == 0, UnsupportedWithdrawIntent(s.withdrawIntent));
        } else {
            require(s.withdrawRecipient != 0, ZeroRecipient());
            require(
                s.withdrawIntent == 0 || s.withdrawIntent == Protocol.UNWRAP_INTENT,
                UnsupportedWithdrawIntent(s.withdrawIntent)
            );
        }
    }

    function _validate(MergeRequest calldata r) private view {
        _checkRoot(r.rootIndex, block.chainid, r.commitmentRoot);
        _checkField(r.noteHash);
        // Load-bearing: the circuit pays the fee out of the sum, which only a fee below 2^248 cannot wrap.
        _checkAmount(r.fee);
        _checkAddress(r.feeRecipient);

        require(aspRootAccepted(r.aspRoot), UnacceptedAspRoot(r.aspRoot));
        // Load-bearing: with i == 0 the decider accepts z_0 == z_i without a proof.
        require(r.nullifiers.length != 0, EmptyMerge());
        for (uint256 k; k < r.nullifiers.length; ++k) {
            _checkField(r.nullifiers[k]);
            _checkUnspent(r.nullifiers[k]);
        }
        if (r.fee == 0) {
            require(r.feeRecipient == 0, NonCanonicalRecipient(r.feeRecipient));
        } else {
            require(r.feeRecipient != 0, ZeroRecipient());
        }
    }

    function _checkRoot(uint64 rootIndex, uint256 chainId, uint256 root) private view {
        require(chainId == block.chainid, InvalidChainId(chainId, block.chainid));
        _checkField(root);
        require(_verifierStorage.ledger.provedRoots(rootIndex, root), UnprovedRoot(rootIndex, root));
    }

    /// @dev Only saves gas on a nullifier conflict: a request whose nullifier another transaction spent first, as one
    ///      racing a relayer's can, reverts here rather than after the proof is verified. `_spend` is what enforces
    ///      single use, and also catches a nullifier repeated within a merge.
    function _checkUnspent(uint256 nullifier) private view {
        require(!_verifierStorage.nullifierUsed[nullifier], NullifierAlreadyUsed(nullifier));
    }

    function _checkField(uint256 v) private pure {
        require(v < Protocol.FIELD_MODULUS, InvalidField(v));
    }

    function _checkAmount(uint256 v) private pure {
        require(v < Protocol.AMOUNT_BOUND, InvalidAmount(v));
    }

    function _checkAddress(uint256 v) private pure {
        require(v >> 160 == 0, InvalidAddress(v));
    }

    // ---- proofs: Groth16 public signals are outputs first, exactly as emitted by Circom --------

    /// @dev Replay needs no nonce: every statement spends nullifiers, which spend only once.
    function _checkAttestation(bytes32 structHash, bytes calldata signature) private view {
        address signer = ECDSA.recover(_hashTypedDataV4(structHash), signature);
        require(_verifierStorage.attesters[signer], UnauthorizedAttestation(signer));
    }

    function _mergeStatement(MergeRequest calldata r) private view returns (bytes32) {
        return keccak256(
            abi.encode(
                MERGE_TYPEHASH,
                r.tokenId,
                block.chainid,
                r.commitmentRoot,
                r.aspRoot,
                keccak256(abi.encodePacked(r.nullifiers)),
                r.noteHash,
                r.fee,
                r.feeRecipient
            )
        );
    }

    function _verifyJoinSplit(Groth16Proof calldata p, TransactSignals calldata s) private view {
        uint256[11] memory signals = [
            s.nullifier0,
            s.nullifier1,
            s.withdrawRecipient,
            s.withdrawAmount,
            s.withdrawIntent,
            s.noteHash1,
            s.noteHash2,
            s.tokenId,
            s.chainId,
            s.commitmentRoot,
            s.aspRoot
        ];
        try _verifierStorage.joinSplitVerifier.verifyProof(p.pA, p.pB, p.pC, signals) returns (bool ok) {
            require(ok, InvalidProof());
        } catch {
            revert InvalidProof();
        }
    }

    /// @dev The Nova state is [tokenId, chainId, commitmentRoot, aspRoot, nullifierChain, signedChain, noteHash,
    ///      remaining, fee, feeRecipient]; the circuit starts from a zero chain, an empty (zero) output note and one step
    ///      per nullifier left, and pays the fee at the step that finds one left. `signedChain` is the chain of the
    ///      nullifiers spent here, which every input's owner signed together with the output and the fee.
    function _verifyMerge(MergeRequest calldata r, uint256 nullifierChain) private view {
        uint256 n = r.nullifiers.length;
        uint256[10] memory z0 =
            [r.tokenId, block.chainid, r.commitmentRoot, r.aspRoot, 0, nullifierChain, 0, n, r.fee, r.feeRecipient];
        uint256[10] memory zi = [
            r.tokenId,
            block.chainid,
            r.commitmentRoot,
            r.aspRoot,
            nullifierChain,
            nullifierChain,
            r.noteHash,
            0,
            r.fee,
            r.feeRecipient
        ];
        NovaDeciderProof calldata p = r.proof;
        try _verifierStorage.mergeVerifier
            .verifyDeciderProof(n, z0, zi, p.challenge, p.runningCmE, p.cmT, p.runningCmW, p.incomingCmW, p.proof) {}
        catch {
            revert InvalidProof();
        }
    }

    /// @dev chain' = SHA256(chain || nullifier) mod 2^248 over 32-byte big-endian words, from zero.
    function _nullifierChain(uint256[] calldata nullifiers) private pure returns (uint256 chain) {
        for (uint256 k; k < nullifiers.length; ++k) {
            chain = uint256(sha256(abi.encodePacked(chain, nullifiers[k]))) & Protocol.HASH_CHAIN_MASK;
        }
    }

    /// @dev Signals: [nullifier, chainId, commitmentIndex, burnAddress].
    function _verifyRageExit(Groth16Proof calldata p, uint256[4] memory signals) private view {
        try _verifierStorage.rageExitVerifier.verifyProof(p.pA, p.pB, p.pC, signals) returns (bool ok) {
            require(ok, InvalidProof());
        } catch {
            revert InvalidProof();
        }
    }

    // ---- helpers -------------------------------------------------------------------------------

    function _token(uint256 tokenId) private view returns (ZERC20 token) {
        // forge-lint: disable-next-line(unsafe-typecast)
        address t = tokenId <= type(uint32).max ? _verifierStorage.factory.tokenById(uint32(tokenId)) : address(0);
        require(t != address(0), UnregisteredToken(tokenId));
        // forge-lint: disable-next-line(unsafe-typecast)
        require(!_verifierStorage.tokenPaused[uint32(tokenId)], TokenPaused(uint32(tokenId)));
        token = ZERC20(payable(t));
    }

    function _spend(uint256 nullifier) private {
        mapping(uint256 => bool) storage used = _verifierStorage.nullifierUsed;
        require(!used[nullifier], NullifierAlreadyUsed(nullifier));
        used[nullifier] = true;
        emit NullifierSpent(nullifier);
    }

    /// @dev Mints the fee to this contract, accrued to the fee recipient, then pays the net amount to `recipient`, as
    ///      zERC20 or with `unwrap` as the underlying. The payout comes last, since paying out the native asset calls
    ///      the recipient.
    function _settleWithdraw(ZERC20 token, uint32 tokenId, address recipient, uint256 gross, bool unwrap)
        private
        returns (uint256 fee)
    {
        if (gross == 0) return 0;
        fee = withdrawFee(tokenId, gross);
        if (fee != 0) {
            VerifierStorage storage $ = _verifierStorage;
            address feeTo = $.fees[tokenId].recipient;
            token.payOut(address(this), fee, false);
            $.accruedFees[tokenId][feeTo] += fee;
            emit FeeAccrued(tokenId, feeTo, fee);
        }
        if (gross != fee) token.payOut(recipient, gross - fee, unwrap);
    }

    function _setTokenPaused(uint32 tokenId, bool paused_) private {
        require(_verifierStorage.factory.tokenById(tokenId) != address(0), UnregisteredToken(tokenId));
        _verifierStorage.tokenPaused[tokenId] = paused_;
        emit TokenPausedUpdated(tokenId, paused_);
    }

    function _authorizeUpgrade(address) internal override onlyOwner {}
}
