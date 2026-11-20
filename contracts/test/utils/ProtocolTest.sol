// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Test} from "forge-std/Test.sol";
import {ERC1967Utils} from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Utils.sol";
import {Blocklist} from "../../src/Blocklist.sol";
import {CommitmentLedger} from "../../src/CommitmentLedger.sol";
import {DepositAddressFactory} from "../../src/DepositAddress.sol";
import {Verifier} from "../../src/Verifier.sol";
import {ZERC20} from "../../src/ZERC20.sol";
import {ZERC20Factory} from "../../src/ZERC20Factory.sol";
import {NovaDeciderProof} from "../../src/interfaces/INovaDeciderVerifier.sol";
import {FeeSchedule} from "../../src/libs/FeeSchedule.sol";
import {Protocol} from "../../src/libs/Protocol.sol";
import {RageExitGroth16Verifier} from "../../src/verifiers/generated/RageExitGroth16Verifier.sol";
import {BURN_NULLIFIER, rageExitProof} from "../RageExitFixture.sol";
import {AcceptAll} from "../mocks/AcceptAll.sol";
import {CREATE3_FACTORY, CREATE3_FACTORY_CODE} from "../../script/Create3Factory.sol";
import {ProtocolDeployer} from "../../script/ProtocolDeployer.sol";

/// @dev The protocol as the contract tests use it. This contract owns every proxy and publishes ASP roots, zETH is
///      token 1, and AcceptAll stands in for every proof verifier but the rage exit one, which stays real so that the
///      fixture proof is checked.
abstract contract ProtocolTest is Test, ProtocolDeployer {
    CommitmentLedger ledger;
    Verifier verifier;
    ZERC20Factory factory;
    ZERC20 token;
    Blocklist blocklist;
    DepositAddressFactory deposits;
    address tokenImpl;
    address alice = address(0xA11CE);
    address bob = address(0xB0B);
    address carol = address(0xCA201);
    address attester;
    uint256 attesterKey;

    // Mirrors of the Verifier's EIP-712 statement types, written out independently.
    bytes32 constant TRANSACT_TYPEHASH = keccak256(
        "Transact(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256 nullifier0,"
        "uint256 nullifier1,uint256 withdrawRecipient,uint256 withdrawAmount,uint256 withdrawIntent,uint256 noteHash1,"
        "uint256 noteHash2)"
    );
    bytes32 constant MERGE_TYPEHASH = keccak256(
        "Merge(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256[] nullifiers,"
        "uint256 noteHash,uint256 fee,uint256 feeRecipient)"
    );

    // The rage exit fixture: a real RageExit proof for the zkp/test-vectors burn address (sk 42, salt 2279, chain 1)
    // at ledger index 0, regenerated with the verifier by zkp/scripts/artifacts.mjs.
    address constant BURN_ADDRESS = 0x96aC69527F3b2c96fad588F3E1818c2CAC995D51;

    function setUp() public virtual {
        vm.etch(CREATE3_FACTORY, CREATE3_FACTORY_CODE);
        (deployer, deploySalt) = (address(this), "core");
        AcceptAll mock = new AcceptAll();
        Core memory c = _deployCore(
            address(this),
            ProofVerifiers({joinSplit: mock, rageExit: new RageExitGroth16Verifier(), root: mock, merge: mock}),
            address(this)
        );
        blocklist = c.blocklist;
        ledger = c.ledger;
        verifier = c.verifier;
        factory = c.factory;
        deposits = c.depositAddressFactory;
        tokenImpl = c.tokenImpl;
        token = ZERC20(payable(factory.createToken(Protocol.NATIVE, "zEther", "zETH", 18)));
        verifier.publishAspRoot(1);
        (attester, attesterKey) = makeAddrAndKey("attester");
        verifier.addAttester(attester);
    }

    // ---- accounts ------------------------------------------------------------------------------

    function _setBlocked(address account, bool blocked) internal {
        address[] memory list = new address[](1);
        list[0] = account;
        blocklist.setBlocked(list, blocked);
    }

    function _wrap(address from, uint256 amount, address to) internal {
        vm.deal(from, amount);
        vm.prank(from);
        token.wrap{value: amount}(amount, to);
    }

    function _flatFee(uint16 bps) internal pure returns (FeeSchedule.Tier[] memory tiers) {
        tiers = new FeeSchedule.Tier[](1);
        tiers[0] = FeeSchedule.Tier({minAmount: 0, feeBps: bps});
    }

    // ---- attested statements -------------------------------------------------------------------

    function _attest(uint256 key, bytes32 structHash) internal view returns (bytes memory) {
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("zERC20 Verifier"),
                keccak256("1"),
                block.chainid,
                address(verifier)
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, keccak256(abi.encodePacked("\x19\x01", domain, structHash)));
        return abi.encodePacked(r, s, v);
    }

    function _attested(Verifier.TransactSignals memory s) internal view returns (Verifier.TransactRequest memory r) {
        r.publicSignals = s;
        r.attestation = _attest(attesterKey, keccak256(abi.encode(TRANSACT_TYPEHASH, s)));
    }

    function _transactSignals(uint256 withdraw, address to, uint256 n0)
        internal
        view
        returns (Verifier.TransactSignals memory s)
    {
        s = Verifier.TransactSignals({
            tokenId: 1,
            chainId: block.chainid,
            commitmentRoot: Protocol.EMPTY_ROOT,
            aspRoot: 1,
            nullifier0: n0,
            nullifier1: n0 + 1,
            withdrawRecipient: uint256(uint160(to)),
            withdrawAmount: withdraw,
            withdrawIntent: 0,
            noteHash1: 5,
            noteHash2: 6
        });
    }

    function _signals(uint256 withdraw, address to, uint256 n0)
        internal
        view
        returns (Verifier.TransactRequest memory)
    {
        return _attested(_transactSignals(withdraw, to, n0));
    }

    function _unwrapSignals(uint256 withdraw, address to, uint256 n0)
        internal
        view
        returns (Verifier.TransactRequest memory)
    {
        Verifier.TransactSignals memory s = _transactSignals(withdraw, to, n0);
        s.withdrawIntent = Protocol.UNWRAP_INTENT;
        return _attested(s);
    }

    function _mergeStatement(Verifier.MergeRequest memory r) internal view returns (bytes32) {
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

    function _mergeRequest(uint256[] memory nullifiers) internal view returns (Verifier.MergeRequest memory r) {
        return _paidMerge(nullifiers, 0, address(0));
    }

    function _paidMerge(uint256[] memory nullifiers, uint256 fee, address to)
        internal
        view
        returns (Verifier.MergeRequest memory r)
    {
        r.fee = fee;
        r.feeRecipient = uint256(uint160(to));
        r.tokenId = 1;
        r.commitmentRoot = Protocol.EMPTY_ROOT;
        r.aspRoot = 1;
        r.noteHash = 9;
        r.nullifiers = nullifiers;
        r.proof.challenge = 77;
        r.proof.proof[11] = 88;
        r.attestation = _attest(attesterKey, _mergeStatement(r));
    }

    // ---- roots: AcceptAll proves any root, as a soundness bug in the root circuit would ----------

    /// @dev Commits a note, so the head moves, and proves `root` at the head.
    function _proveRoot(uint256 root) internal returns (uint64 idx) {
        vm.prank(address(verifier));
        token.commitNote(root);
        uint256 hc;
        (idx, hc) = ledger.reserveHashChain();
        NovaDeciderProof memory p;
        ledger.proveRootTransition(CommitmentLedger.RootState({index: idx, hashChain: hc, root: root}), p);
    }

    function _spendAt(uint64 rootIndex, uint256 root, uint256 n0)
        internal
        view
        returns (Verifier.TransactRequest memory r)
    {
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, n0);
        s.commitmentRoot = root;
        r = _attested(s);
        r.rootIndex = rootIndex;
    }

    // ---- rage exit -----------------------------------------------------------------------------

    /// @dev Alice deposits 1 zETH to the burn address; it is the ledger's first commitment.
    function _burnDeposit() internal returns (uint256[4][] memory commits) {
        vm.chainId(1); // the burn address and the proof are bound to chain 1
        _wrap(alice, 1 ether, BURN_ADDRESS);
        commits = new uint256[4][](1);
        commits[0] = [
            Protocol.encode(Protocol.TRANSFER_TAG, 1), uint256(uint160(alice)), uint256(uint160(BURN_ADDRESS)), 1 ether
        ];
    }

    function _rageExit(uint64 end, uint256 prev, uint256[4][] memory commits)
        internal
        pure
        returns (Verifier.RageExitRequest memory r)
    {
        r.checkpointIndex = end;
        r.prevHashChain = prev;
        r.commitments = commits;
        r.nullifier = BURN_NULLIFIER;
        r.proof = rageExitProof();
    }

    // ---- proxies -------------------------------------------------------------------------------

    function _implementation(address proxy) internal view returns (address) {
        return address(uint160(uint256(vm.load(proxy, ERC1967Utils.IMPLEMENTATION_SLOT))));
    }

    function _erc7201(string memory id) internal pure returns (bytes32) {
        return keccak256(abi.encode(uint256(keccak256(bytes(id))) - 1)) & ~bytes32(uint256(0xff));
    }
}
