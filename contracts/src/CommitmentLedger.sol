// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Initializable} from "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import {Ownable2StepUpgradeable} from "@openzeppelin/contracts-upgradeable/access/Ownable2StepUpgradeable.sol";
import {UUPSUpgradeable} from "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import {IRootDeciderVerifier, NovaDeciderProof} from "./interfaces/INovaDeciderVerifier.sol";
import {ITokenRegistry} from "./interfaces/ITokenRegistry.sol";
import {Protocol} from "./libs/Protocol.sol";

/// @title CommitmentLedger
/// @dev UUPS proxy; future implementations must retain this namespace. Upgrades are owner-only.
/// @notice Append-only stream of 4-field commitments with a SHA-256 hash chain, plus the registry of
///         commitment-tree roots proven to follow from it.
/// @dev Only the Factory-created token bound to the commitment's token id may append.
///      hashChain' = SHA256(hashChain || f0 || f1 || f2 || f3) mod 2^248.
///      A root proof moves (index, hashChain, root) from the current state to a ledger checkpoint.
///      The Nova root decider checks it directly, with `i`, `z_0` and `z_i` rebuilt here.
///      A root stays accepted unless an emergency bounds it or a recovery withdraws it. A soundness bug
///      in the root circuit lets anyone prove a forged root: a guardian or the owner then stops proving
///      and bounds the accepted roots to the last one the indexer derived itself (`enterEmergency`),
///      and once the circuit is fixed the owner restarts from that root with a new verifier
///      (`recover`, through the admin's delay), withdrawing every root proved above it.
contract CommitmentLedger layout at erc7201("zerc20.storage.CommitmentLedger")
    is
    Initializable,
    Ownable2StepUpgradeable,
    UUPSUpgradeable
{
    struct RootState {
        uint64 index;
        uint256 hashChain;
        uint256 root;
    }

    /// @dev Complete project-owned storage. Append new fields at the end only.
    /// @custom:storage-location erc7201:zerc20.storage.CommitmentLedger
    struct LedgerStorage {
        ITokenRegistry factory;
        IRootDeciderVerifier rootVerifier;
        uint64 nextIndex;
        uint256 hashChain;
        // Non-zero value at `index` marks a checkpoint; zero is the empty sentinel.
        mapping(uint64 index => uint256 hashChain) checkpoints;
        RootState rootState;
        // The era a root was proved in, zero for never. `recover` starts a new era.
        mapping(uint64 index => mapping(uint256 root => uint32 era)) provedIn;
        uint32 era;
        // In an emergency no root above it is accepted, and none is proved; `type(uint64).max` otherwise.
        uint64 bound;
        // A past era's roots stay accepted up to the index its `recover` restarted from.
        mapping(uint32 era => uint64 index) eraEnd;
        mapping(address account => bool) guardians;
        // The token id each token has committed under, once the Factory confirmed it.
        mapping(address token => uint32 tokenId) committers;
    }

    LedgerStorage private _ledgerStorage;

    event Committed(uint64 indexed index, uint256[4] fields);
    event CheckpointRecorded(uint64 indexed index, uint256 hashChain);
    event RootProved(uint64 indexed oldIndex, uint64 indexed newIndex, uint256 newRoot);
    event EmergencyEntered(uint64 bound, address indexed by);
    event GuardianSet(address indexed guardian, bool allowed);
    /// @dev Shaped like `RootProved`, so a reader of the root stream sees the restart as one more step.
    event Recovered(
        uint64 indexed oldIndex, uint64 indexed newIndex, uint256 newRoot, IRootDeciderVerifier rootVerifier
    );

    error ZeroAddress();
    error Unauthorized(address caller);
    error InvalidField(uint8 fieldIndex, uint256 value);
    error InvalidField0Layout(uint256 field0);
    error InvalidCommitmentTag(uint32 tag);
    error InvalidTransferAddress(uint8 fieldIndex, uint256 value);
    error InvalidTransferAmount(uint256 value);
    error InvalidNotePadding(uint8 fieldIndex, uint256 value);
    error TreeFull(uint64 nextIndex);
    error UnreservableZeroHashChain(uint64 index);
    error InvalidRootState();
    error InvalidProof();
    error CheckpointMismatch(uint64 index);
    error EmptySegment();
    error InEmergency();
    error NotInEmergency();
    error UnprovedRoot(uint64 index, uint256 root);
    error BelowSettledEra(uint64 index, uint64 settled);
    error AcceptsEmptyProof(IRootDeciderVerifier verifier);

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    function initialize(address owner_, ITokenRegistry factory_, IRootDeciderVerifier rootVerifier_)
        external
        initializer
    {
        require(address(factory_) != address(0) && address(rootVerifier_) != address(0), ZeroAddress());
        __Ownable_init(owner_);

        LedgerStorage storage $ = _ledgerStorage;
        $.factory = factory_;
        $.rootVerifier = rootVerifier_;
        $.rootState = RootState({index: 0, hashChain: 0, root: Protocol.EMPTY_ROOT});
        $.era = 1;
        $.bound = type(uint64).max;
        $.provedIn[0][Protocol.EMPTY_ROOT] = 1;
    }

    function factory() external view returns (ITokenRegistry) {
        return _ledgerStorage.factory;
    }

    function rootVerifier() external view returns (IRootDeciderVerifier) {
        return _ledgerStorage.rootVerifier;
    }

    function nextIndex() external view returns (uint64) {
        return _ledgerStorage.nextIndex;
    }

    function hashChain() external view returns (uint256) {
        return _ledgerStorage.hashChain;
    }

    function rootState() external view returns (RootState memory) {
        return _ledgerStorage.rootState;
    }

    /// @notice Whether a proof may use `root` at `index` now: proved, not withdrawn by a recovery, and in an
    ///         emergency no higher than the bound.
    function provedRoots(uint64 index, uint256 root) external view returns (bool) {
        return index <= _ledgerStorage.bound && _inEra(index, root);
    }

    /// @notice The era `root` was proved in at `index`, zero if never: whether this chain proved it at all,
    ///         accepted now or not.
    function provedIn(uint64 index, uint256 root) external view returns (uint32) {
        return _ledgerStorage.provedIn[index][root];
    }

    function era() external view returns (uint32) {
        return _ledgerStorage.era;
    }

    /// @notice `type(uint64).max` unless in an emergency.
    function bound() external view returns (uint64) {
        return _ledgerStorage.bound;
    }

    function isGuardian(address account) external view returns (bool) {
        return _ledgerStorage.guardians[account];
    }

    /// @notice Append a commitment; returns its index.
    function commit(uint256[4] calldata fields) external returns (uint64 index) {
        _validate(fields);
        (, uint32 tokenId) = Protocol.decode(fields[0]);
        _authorizeCommitter(tokenId);

        LedgerStorage storage $ = _ledgerStorage;
        index = $.nextIndex;
        require(index < Protocol.TREE_SIZE, TreeFull(index));

        $.hashChain = _next($.hashChain, fields);
        $.nextIndex = index + 1;

        emit Committed(index, fields);
    }

    /// @notice Pin the live head as a checkpoint so a root proof or a rage exit can target it.
    /// @dev Permissionless: it only stores a value that is already canonical. Calling it right after a burn
    ///      deposit keeps that deposit's rage-exit walk (`verifySegment`) as short as possible.
    function reserveHashChain() external returns (uint64 index, uint256 checkpoint) {
        LedgerStorage storage $ = _ledgerStorage;
        index = $.nextIndex;
        checkpoint = $.hashChain;
        if (index == 0) return (index, checkpoint); // genesis is always available
        // zero is the empty-slot sentinel; refusing it makes that a contract invariant.
        require(checkpoint != 0, UnreservableZeroHashChain(index));
        $.checkpoints[index] = checkpoint;
        emit CheckpointRecorded(index, checkpoint);
    }

    /// @notice Hash chain at `index` (live head, genesis, or a recorded checkpoint).
    function hashChainAt(uint64 index) external view returns (uint256, bool) {
        return _hashChainAt(index);
    }

    /// @notice Authenticate `commits` as the commitments right before index `end` and return the index of
    ///         `commits[0]`: hashing them onto `prev` must reach the hash chain at `end` (a checkpoint, genesis
    ///         or the live head).
    /// @dev `prev` needs no anchor. Every step is a fixed-length SHA-256, so reaching the chain at `end` from
    ///      anything but the real commitments and the real chain before them takes a 248-bit hash collision.
    ///      A live-head `end` stops matching once anything else is committed; reserve a checkpoint first.
    function verifySegment(uint64 end, uint256 prev, uint256[4][] calldata commits) public view returns (uint64 start) {
        require(commits.length != 0, EmptySegment());
        // forge-lint: disable-next-line(unsafe-typecast)
        start = uint64(end - commits.length); // a segment longer than `end` underflows and reverts
        uint256 chain = prev;
        for (uint256 i; i < commits.length; ++i) {
            chain = _next(chain, commits[i]);
        }
        (uint256 checkpoint, bool exists) = _hashChainAt(end);
        require(exists && chain == checkpoint, CheckpointMismatch(end));
    }

    /// @notice Record the hash chain before an authenticated segment as a checkpoint, so a long gap after a
    ///         commitment can be walked back toward it over several transactions.
    /// @dev Permissionless: `verifySegment` only admits the canonical value, so this cannot disturb root proofs.
    function checkpointBefore(uint64 end, uint256 prev, uint256[4][] calldata commits) external returns (uint64 start) {
        start = verifySegment(end, prev, commits);
        // Only genesis has a zero chain, and it needs no checkpoint; zero is the empty-slot sentinel.
        require(prev != 0, UnreservableZeroHashChain(start));
        _ledgerStorage.checkpoints[start] = prev;
        emit CheckpointRecorded(start, prev);
    }

    /// @dev The caller must be the Factory's token for `tokenId`. The Factory never reassigns an id, so each token is
    ///      looked up there on its first commit only.
    function _authorizeCommitter(uint32 tokenId) private {
        LedgerStorage storage $ = _ledgerStorage;
        if (tokenId != 0 && $.committers[msg.sender] == tokenId) return;
        require(tokenId != 0 && $.factory.tokenById(tokenId) == msg.sender, Unauthorized(msg.sender));
        $.committers[msg.sender] = tokenId;
    }

    function _next(uint256 chain, uint256[4] calldata f) private pure returns (uint256) {
        return uint256(sha256(abi.encodePacked(chain, f[0], f[1], f[2], f[3]))) & Protocol.HASH_CHAIN_MASK;
    }

    function _hashChainAt(uint64 index) private view returns (uint256 checkpoint, bool exists) {
        LedgerStorage storage $ = _ledgerStorage;
        if (index > $.nextIndex) return (0, false);
        if (index == $.nextIndex) return ($.hashChain, true);
        if (index == 0) return (0, true);
        checkpoint = $.checkpoints[index];
        exists = checkpoint != 0;
    }

    /// @notice Advance the proven root from the current root state to `newState` at a ledger checkpoint;
    ///         reverts unless the proof folds one step per commitment in between.
    function proveRootTransition(RootState calldata newState, NovaDeciderProof calldata proof) external {
        _validate(newState);
        LedgerStorage storage $ = _ledgerStorage;
        require($.bound == type(uint64).max, InEmergency());
        RootState memory old = $.rootState;
        // Load-bearing: with i == 0 the decider accepts z_0 == z_i without a proof.
        require(newState.index > old.index, InvalidRootState());

        (uint256 checkpoint, bool exists) = _hashChainAt(newState.index);
        require(exists && checkpoint == newState.hashChain, CheckpointMismatch(newState.index));

        try $.rootVerifier
            .verifyDeciderProof(
                newState.index - old.index,
                [uint256(old.index), old.hashChain, old.root],
                [uint256(newState.index), newState.hashChain, newState.root],
                proof.challenge,
                proof.runningCmE,
                proof.cmT,
                proof.runningCmW,
                proof.incomingCmW,
                proof.proof
            ) {}
        catch {
            revert InvalidProof();
        }

        $.rootState = newState;
        $.provedIn[newState.index][newState.root] = $.era;
        emit RootProved(old.index, newState.index, newState.root);
    }

    // ---- emergency -----------------------------------------------------------------------------

    /// @notice Stop proving roots and accepting any above `bound_`. Only ever lowers the bound, so a guardian
    ///         can stop the system but never resume it.
    /// @dev Called with the last root the indexer derived itself once a proved root differs from its own.
    function enterEmergency(uint64 bound_) external {
        LedgerStorage storage $ = _ledgerStorage;
        require(msg.sender == owner() || $.guardians[msg.sender], Unauthorized(msg.sender));
        if (bound_ >= $.bound) return;
        $.bound = bound_;
        emit EmergencyEntered(bound_, msg.sender);
    }

    function setGuardian(address guardian, bool allowed) external onlyOwner {
        require(guardian != address(0), ZeroAddress());
        _ledgerStorage.guardians[guardian] = allowed;
        emit GuardianSet(guardian, allowed);
    }

    /// @notice End an emergency: restart from `root` at `index`, which must be a proved root not yet withdrawn,
    ///         with `rootVerifier_` checking every proof from now on. Every root proved in this era above
    ///         `index` is withdrawn for good, whatever the bound was.
    /// @dev The same root and verifier as now resume after a false alarm. `index` needs its hash chain: a
    ///      checkpoint (`checkpointBefore` records one), genesis or the live head. `index` is no lower than where the
    ///      previous recovery restarted: the eras before stay accepted up to there, so a restart below it would leave
    ///      their roots above the restart standing beside the ones proved again.
    function recover(uint64 index, uint256 root, IRootDeciderVerifier rootVerifier_) external onlyOwner {
        LedgerStorage storage $ = _ledgerStorage;
        require($.bound != type(uint64).max, NotInEmergency());
        uint64 settled = $.eraEnd[$.era - 1];
        require(index >= settled, BelowSettledEra(index, settled));
        require(address(rootVerifier_) != address(0), ZeroAddress());
        // The verifier only reverts, so a wrong address that returns for any call, as a permissive fallback does,
        // would take every root. A new one must reject an empty proof; the current one passed here or came with
        // the deployment.
        if (address(rootVerifier_) != address($.rootVerifier)) _checkRejectsEmptyProof(rootVerifier_);
        require(_inEra(index, root), UnprovedRoot(index, root));
        (uint256 chain, bool exists) = _hashChainAt(index);
        require(exists, CheckpointMismatch(index));

        $.eraEnd[$.era] = index;
        ++$.era;
        $.bound = type(uint64).max;
        emit Recovered($.rootState.index, index, root, rootVerifier_);
        $.rootState = RootState({index: index, hashChain: chain, root: root});
        $.rootVerifier = rootVerifier_;
    }

    /// @dev One step from the all-zero state with an all-zero proof. An address without code reverts before the
    ///      call, outside the try.
    function _checkRejectsEmptyProof(IRootDeciderVerifier v) private view {
        NovaDeciderProof memory none;
        uint256[3] memory zero;
        try v.verifyDeciderProof(
            1, zero, zero, none.challenge, none.runningCmE, none.cmT, none.runningCmW, none.incomingCmW, none.proof
        ) {
            revert AcceptsEmptyProof(v);
        } catch {}
    }

    /// @dev Proved, and not withdrawn by a recovery; the bound is not looked at.
    function _inEra(uint64 index, uint256 root) private view returns (bool) {
        LedgerStorage storage $ = _ledgerStorage;
        uint32 e = $.provedIn[index][root];
        return e != 0 && (e == $.era || index <= $.eraEnd[e]);
    }

    function _authorizeUpgrade(address) internal override onlyOwner {}

    function _validate(RootState calldata s) private pure {
        require(
            s.index <= Protocol.TREE_SIZE && s.hashChain < Protocol.HASH_CHAIN_BOUND && s.root < Protocol.FIELD_MODULUS,
            InvalidRootState()
        );
    }

    function _validate(uint256[4] calldata f) private pure {
        for (uint8 i; i < 4; ++i) {
            if (f[i] >= Protocol.FIELD_MODULUS) revert InvalidField(i, f[i]);
        }
        require(f[0] >> 64 == 0, InvalidField0Layout(f[0]));

        (uint32 tag,) = Protocol.decode(f[0]);
        if (tag == Protocol.TRANSFER_TAG) {
            require(f[1] <= type(uint160).max, InvalidTransferAddress(1, f[1]));
            require(f[2] <= type(uint160).max, InvalidTransferAddress(2, f[2]));
            require(f[3] < Protocol.AMOUNT_BOUND, InvalidTransferAmount(f[3]));
        } else if (tag == Protocol.NOTE_HASH_TAG) {
            for (uint8 i = 2; i < 4; ++i) {
                require(f[i] == 0, InvalidNotePadding(i, f[i]));
            }
        } else {
            revert InvalidCommitmentTag(tag);
        }
    }
}
