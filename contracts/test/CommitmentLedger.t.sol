// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {stdError} from "forge-std/StdError.sol";
import {ERC1967Proxy} from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {Verifier} from "../src/Verifier.sol";
import {IRootDeciderVerifier, NovaDeciderProof} from "../src/interfaces/INovaDeciderVerifier.sol";
import {ITokenRegistry} from "../src/interfaces/ITokenRegistry.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {RootDeciderVerifier} from "../src/verifiers/generated/RootNovaVerifier.sol";
import {AcceptAll} from "./mocks/AcceptAll.sol";
import {ProtocolTest} from "./utils/ProtocolTest.sol";

contract CommitmentLedgerTest is ProtocolTest {
    uint256 constant MASK = (uint256(1) << 248) - 1;

    function _note(uint256 noteHash) internal pure returns (uint256[4] memory) {
        return [Protocol.encode(Protocol.NOTE_HASH_TAG, 1), noteHash, 0, 0];
    }

    function _transfer(address from, address to, uint256 amount) internal pure returns (uint256[4] memory) {
        return [Protocol.encode(Protocol.TRANSFER_TAG, 1), uint256(uint160(from)), uint256(uint160(to)), amount];
    }

    /// @dev Written out apart from the ledger: SHA-256 over five 32-byte big-endian words, kept to 248 bits.
    function _chain(uint256 prev, uint256[4] memory f) internal pure returns (uint256) {
        return uint256(sha256(abi.encodePacked(prev, f[0], f[1], f[2], f[3]))) & MASK;
    }

    function _commitAsToken(uint256[4] memory f) internal returns (uint64) {
        vm.prank(address(token));
        return ledger.commit(f);
    }

    // ---- initialization ------------------------------------------------------------------------

    function test_initializeStartsAtTheEmptyRoot() public view {
        assertEq(address(ledger.factory()), address(factory));
        assertEq(ledger.nextIndex(), 0);
        assertEq(ledger.hashChain(), 0);
        assertEq(ledger.era(), 1);
        assertEq(ledger.bound(), type(uint64).max);
        CommitmentLedger.RootState memory s = ledger.rootState();
        assertEq(s.index, 0);
        assertEq(s.hashChain, 0);
        assertEq(s.root, Protocol.EMPTY_ROOT);
        assertTrue(ledger.provedRoots(0, Protocol.EMPTY_ROOT));
        assertEq(ledger.provedIn(0, Protocol.EMPTY_ROOT), 1);
    }

    function test_initializeRejectsZeroDependencies() public {
        address impl = _implementation(address(ledger));
        IRootDeciderVerifier root = ledger.rootVerifier();
        vm.expectRevert(CommitmentLedger.ZeroAddress.selector);
        new ERC1967Proxy(
            impl, abi.encodeCall(CommitmentLedger.initialize, (address(this), ITokenRegistry(address(0)), root))
        );
        vm.expectRevert(CommitmentLedger.ZeroAddress.selector);
        new ERC1967Proxy(
            impl,
            abi.encodeCall(CommitmentLedger.initialize, (address(this), factory, IRootDeciderVerifier(address(0))))
        );
    }

    // ---- commitments ---------------------------------------------------------------------------

    function test_commitExtendsTheSha256HashChain() public {
        uint256[4] memory first = _transfer(alice, bob, 3);
        uint256[4] memory second = _note(7);

        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(0, first);
        assertEq(_commitAsToken(first), 0);
        uint256 chain = _chain(0, first);
        assertEq(ledger.hashChain(), chain);

        assertEq(_commitAsToken(second), 1);
        assertEq(ledger.hashChain(), _chain(chain, second));
        assertEq(ledger.nextIndex(), 2);
    }

    function test_ledgerRejectsOutsiders() public {
        uint256[4] memory f;
        f[0] = Protocol.encode(Protocol.NOTE_HASH_TAG, 1);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.Unauthorized.selector, address(this)));
        ledger.commit(f);
        f[0] = Protocol.encode(Protocol.NOTE_HASH_TAG, 0); // the cache's empty value
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.Unauthorized.selector, address(this)));
        ledger.commit(f);

        // a token that has committed still commits under its own id only
        f[0] = Protocol.encode(Protocol.NOTE_HASH_TAG, 1);
        vm.prank(address(token));
        ledger.commit(f);
        f[0] = Protocol.encode(Protocol.NOTE_HASH_TAG, 2);
        vm.prank(address(token));
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.Unauthorized.selector, address(token)));
        ledger.commit(f);
        f[0] = Protocol.encode(Protocol.NOTE_HASH_TAG, 0);
        vm.prank(address(token));
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.Unauthorized.selector, address(token)));
        ledger.commit(f);
    }

    function test_commitRejectsFieldsOutsideTheirLayout() public {
        uint256 p = Protocol.FIELD_MODULUS;
        for (uint8 i; i < 4; ++i) {
            uint256[4] memory f = _note(7);
            f[i] = p;
            _expectCommitRevert(f, abi.encodeWithSelector(CommitmentLedger.InvalidField.selector, i, p));
        }

        uint256[4] memory wide = _note(7);
        wide[0] |= uint256(1) << 64;
        _expectCommitRevert(wide, abi.encodeWithSelector(CommitmentLedger.InvalidField0Layout.selector, wide[0]));

        uint256[4] memory untagged = _note(7);
        untagged[0] = Protocol.encode(0xdeadbeef, 1);
        _expectCommitRevert(
            untagged, abi.encodeWithSelector(CommitmentLedger.InvalidCommitmentTag.selector, uint32(0xdeadbeef))
        );

        uint256 tooWide = uint256(1) << 160;
        uint256[4] memory transfer = _transfer(alice, bob, 1);
        transfer[1] = tooWide;
        _expectCommitRevert(
            transfer, abi.encodeWithSelector(CommitmentLedger.InvalidTransferAddress.selector, 1, tooWide)
        );
        transfer = _transfer(alice, bob, 1);
        transfer[2] = tooWide;
        _expectCommitRevert(
            transfer, abi.encodeWithSelector(CommitmentLedger.InvalidTransferAddress.selector, 2, tooWide)
        );
        transfer = _transfer(alice, bob, Protocol.AMOUNT_BOUND);
        _expectCommitRevert(
            transfer, abi.encodeWithSelector(CommitmentLedger.InvalidTransferAmount.selector, Protocol.AMOUNT_BOUND)
        );

        for (uint8 i = 2; i < 4; ++i) {
            uint256[4] memory padded = _note(7);
            padded[i] = 1;
            _expectCommitRevert(padded, abi.encodeWithSelector(CommitmentLedger.InvalidNotePadding.selector, i, 1));
        }
        assertEq(ledger.nextIndex(), 0);
    }

    function _expectCommitRevert(uint256[4] memory f, bytes memory err) internal {
        vm.prank(address(token));
        vm.expectRevert(err);
        ledger.commit(f);
    }

    /// @dev `nextIndex` shares the struct's second slot with `rootVerifier`, above its 160 bits.
    function _setNextIndex(uint64 n) internal {
        bytes32 slot = bytes32(uint256(_erc7201("zerc20.storage.CommitmentLedger")) + 1);
        uint256 word = uint256(vm.load(address(ledger), slot));
        word = (word & ~(uint256(type(uint64).max) << 160)) | (uint256(n) << 160);
        vm.store(address(ledger), slot, bytes32(word));
        assertEq(ledger.nextIndex(), n);
    }

    function test_commitStopsWhenTheTreeIsFull() public {
        uint64 size = uint64(Protocol.TREE_SIZE);
        _setNextIndex(size - 1);
        assertEq(_commitAsToken(_note(7)), size - 1); // the last leaf of the depth-32 tree
        vm.prank(address(token));
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.TreeFull.selector, size));
        ledger.commit(_note(8));
    }

    function testFuzz_field0PacksTheTagAboveTheTokenId(uint32 tag, uint32 tokenId) public pure {
        uint256 field0 = Protocol.encode(tag, tokenId);
        assertEq(field0 >> 64, 0);
        (uint32 t, uint32 id) = Protocol.decode(field0);
        assertEq(t, tag);
        assertEq(id, tokenId);
    }

    // ---- checkpoints ---------------------------------------------------------------------------

    function test_reserveHashChainPinsTheHeadExceptAtGenesis() public {
        vm.recordLogs();
        (uint64 idx, uint256 chain) = ledger.reserveHashChain();
        assertEq(idx, 0);
        assertEq(chain, 0);
        assertEq(vm.getRecordedLogs().length, 0); // genesis is always available
        (uint256 genesis, bool exists) = ledger.hashChainAt(0);
        assertTrue(exists);
        assertEq(genesis, 0);

        _commitAsToken(_note(1));
        _commitAsToken(_note(2));
        (, exists) = ledger.hashChainAt(1); // passed by without a checkpoint
        assertFalse(exists);

        uint256 head = ledger.hashChain();
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.CheckpointRecorded(2, head);
        (idx, chain) = ledger.reserveHashChain();
        assertEq(idx, 2);
        assertEq(chain, head);

        _commitAsToken(_note(3));
        (uint256 pinned, bool pinnedExists) = ledger.hashChainAt(2);
        assertTrue(pinnedExists);
        assertEq(pinned, head);
        (uint256 live, bool liveExists) = ledger.hashChainAt(3);
        assertTrue(liveExists);
        assertEq(live, ledger.hashChain());
        (, exists) = ledger.hashChainAt(4); // not reached yet
        assertFalse(exists);
        (genesis, exists) = ledger.hashChainAt(0); // genesis stays available once passed
        assertTrue(exists);
        assertEq(genesis, 0);
    }

    function test_verifySegmentAuthenticatesTheCommitsBeforeItsEnd() public {
        uint256[4][] memory both = new uint256[4][](2);
        both[0] = _note(1);
        both[1] = _note(2);
        _commitAsToken(both[0]);
        uint256 afterFirst = ledger.hashChain();
        _commitAsToken(both[1]);

        assertEq(ledger.verifySegment(2, 0, both), 0); // the live head as the end
        uint256[4][] memory last = new uint256[4][](1);
        last[0] = both[1];
        assertEq(ledger.verifySegment(2, afterFirst, last), 1);

        vm.expectRevert(CommitmentLedger.EmptySegment.selector);
        ledger.verifySegment(2, 0, new uint256[4][](0));
        vm.expectRevert(stdError.arithmeticError); // longer than everything before the end
        ledger.verifySegment(1, 0, both);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, 2));
        ledger.verifySegment(2, afterFirst + 1, last);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, 3));
        ledger.verifySegment(3, afterFirst, last); // past the head
    }

    function test_checkpointBeforeBringsACheckpointBackToTheDeposit() public {
        uint256[4][] memory commits = _burnDeposit();
        uint256 afterDeposit = ledger.hashChain();
        vm.prank(address(verifier));
        token.commitNote(7);
        (uint64 end,) = ledger.reserveHashChain();

        uint256[4][] memory both = new uint256[4][](2);
        both[0] = commits[0];
        both[1] = _note(7);
        assertEq(ledger.verifySegment(end, 0, both), 0); // a two-commit walk reaches the deposit directly

        uint256[4][] memory later = new uint256[4][](1);
        later[0] = both[1];
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.CheckpointRecorded(1, afterDeposit);
        assertEq(ledger.checkpointBefore(end, afterDeposit, later), 1);
        (uint256 checkpoint, bool exists) = ledger.hashChainAt(1);
        assertTrue(exists);
        assertEq(checkpoint, afterDeposit);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.UnreservableZeroHashChain.selector, 0));
        ledger.checkpointBefore(1, 0, commits); // genesis needs no checkpoint

        verifier.rageExit(_rageExit(1, 0, commits));
        assertEq(token.balanceOf(alice), 1 ether);
    }

    // ---- root proofs ---------------------------------------------------------------------------

    function test_rootTransition() public {
        _wrap(alice, 1 ether, bob); // a real leaf so there is a checkpoint to prove
        (uint64 idx, uint256 hc) = ledger.reserveHashChain();
        CommitmentLedger.RootState memory next = CommitmentLedger.RootState({index: idx, hashChain: hc, root: 1234});
        NovaDeciderProof memory p;
        p.challenge = 77;
        p.proof[11] = 88;
        // The ledger passes i = the index delta, its own root state as z_0 and the new state as z_i.
        uint256[3] memory z0 = [uint256(0), 0, Protocol.EMPTY_ROOT];
        uint256[3] memory zi = [uint256(idx), hc, 1234];
        vm.expectCall(
            address(ledger.rootVerifier()),
            abi.encodeCall(
                IRootDeciderVerifier.verifyDeciderProof,
                (idx, z0, zi, p.challenge, p.runningCmE, p.cmT, p.runningCmW, p.incomingCmW, p.proof)
            )
        );
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.RootProved(0, idx, 1234);
        vm.prank(alice); // anyone may prove
        ledger.proveRootTransition(next, p);
        assertTrue(ledger.provedRoots(idx, 1234));
        assertEq(ledger.provedIn(idx, 1234), 1);
        assertEq(ledger.rootState().root, 1234);

        vm.expectRevert(CommitmentLedger.InvalidRootState.selector); // i == 0 would skip the proof
        ledger.proveRootTransition(next, p);

        vm.prank(bob);
        assertTrue(token.transfer(alice, 1)); // another leaf for the next transition
        (idx, hc) = ledger.reserveHashChain();
        vm.mockCallRevert(
            address(ledger.rootVerifier()), abi.encodeWithSelector(IRootDeciderVerifier.verifyDeciderProof.selector), ""
        );
        vm.expectRevert(CommitmentLedger.InvalidProof.selector);
        ledger.proveRootTransition(CommitmentLedger.RootState({index: idx, hashChain: hc, root: 5678}), p);
    }

    function test_proveRootTransitionRejectsStatesOutsideTheirRanges() public {
        _commitAsToken(_note(1));
        (uint64 idx, uint256 hc) = ledger.reserveHashChain();
        NovaDeciderProof memory p;
        CommitmentLedger.RootState[3] memory bad = [
            CommitmentLedger.RootState({index: uint64(Protocol.TREE_SIZE) + 1, hashChain: hc, root: 1}),
            CommitmentLedger.RootState({index: idx, hashChain: Protocol.HASH_CHAIN_BOUND, root: 1}),
            CommitmentLedger.RootState({index: idx, hashChain: hc, root: Protocol.FIELD_MODULUS})
        ];
        for (uint256 i; i < bad.length; ++i) {
            vm.expectRevert(CommitmentLedger.InvalidRootState.selector);
            ledger.proveRootTransition(bad[i], p);
        }
    }

    function test_proveRootTransitionEndsAtTheChainOfItsIndex() public {
        _commitAsToken(_note(1));
        _commitAsToken(_note(2));
        uint256 head = ledger.hashChain();
        NovaDeciderProof memory p;

        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, 1));
        ledger.proveRootTransition(CommitmentLedger.RootState({index: 1, hashChain: head, root: 1}), p); // no checkpoint
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, 2));
        ledger.proveRootTransition(CommitmentLedger.RootState({index: 2, hashChain: head ^ 1, root: 1}), p);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, 3));
        ledger.proveRootTransition(CommitmentLedger.RootState({index: 3, hashChain: head, root: 1}), p);

        ledger.proveRootTransition(CommitmentLedger.RootState({index: 2, hashChain: head, root: 1}), p); // live head
        assertEq(ledger.rootState().index, 2);
    }

    // ---- emergency -----------------------------------------------------------------------------

    function test_guardianOrOwnerEntersEmergency() public {
        address guardian = address(0x6A2D);
        vm.prank(guardian);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.Unauthorized.selector, guardian));
        ledger.enterEmergency(0);
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        ledger.setGuardian(guardian, true);
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.GuardianSet(guardian, true);
        ledger.setGuardian(guardian, true);
        assertTrue(ledger.isGuardian(guardian));
        assertEq(ledger.bound(), type(uint64).max);

        vm.expectEmit(address(ledger));
        emit CommitmentLedger.EmergencyEntered(5, guardian);
        vm.prank(guardian);
        ledger.enterEmergency(5);
        assertEq(ledger.bound(), 5);

        vm.recordLogs();
        vm.prank(guardian);
        ledger.enterEmergency(9); // never raised
        vm.prank(guardian);
        ledger.enterEmergency(5);
        assertEq(vm.getRecordedLogs().length, 0); // and only a lower bound is news
        assertEq(ledger.bound(), 5);

        ledger.enterEmergency(2); // the owner too
        assertEq(ledger.bound(), 2);

        ledger.setGuardian(guardian, false);
        assertFalse(ledger.isGuardian(guardian));
        vm.prank(guardian);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.Unauthorized.selector, guardian));
        ledger.enterEmergency(1);

        vm.expectRevert(CommitmentLedger.ZeroAddress.selector);
        ledger.setGuardian(address(0), true);
    }

    function test_emergencyKeepsRootsUpToTheBoundAndRageExits() public {
        uint256[4][] memory deposit = _burnDeposit();
        (uint64 end,) = ledger.reserveHashChain();
        uint64 good = _proveRoot(111);
        uint64 forged = _proveRoot(222);
        ledger.enterEmergency(good);

        verifier.transact(_spendAt(good, 111, 10)); // notes under the last good root stay spendable
        Verifier.TransactRequest memory r = _spendAt(forged, 222, 20);
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnprovedRoot.selector, forged, 222));
        verifier.transact(r);
        assertFalse(ledger.provedRoots(forged, 222));
        assertEq(ledger.provedIn(forged, 222), 1);

        (uint64 idx, uint256 hc) = ledger.reserveHashChain(); // still open, for rage exits
        NovaDeciderProof memory p;
        vm.expectRevert(CommitmentLedger.InEmergency.selector);
        ledger.proveRootTransition(CommitmentLedger.RootState({index: idx, hashChain: hc, root: 333}), p);

        verifier.rageExit(_rageExit(end, 0, deposit)); // needs no root
        assertEq(token.balanceOf(alice), 1 ether);
    }

    // ---- recovery ------------------------------------------------------------------------------

    function test_recoverWithdrawsRootsAboveItAndResumes() public {
        uint64 good = _proveRoot(111);
        uint64 forged = _proveRoot(222);
        IRootDeciderVerifier broken = ledger.rootVerifier();
        vm.expectRevert(CommitmentLedger.NotInEmergency.selector);
        ledger.recover(good, 111, broken);

        ledger.enterEmergency(0); // a bound below the good root does not keep recovery from it
        IRootDeciderVerifier repaired = new AcceptAll();
        _rejectEmptyProof(repaired);
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Recovered(forged, good, 111, repaired);
        ledger.recover(good, 111, repaired);

        (uint256 goodChain,) = ledger.hashChainAt(good);
        assertEq(ledger.bound(), type(uint64).max);
        assertEq(ledger.era(), 2);
        assertEq(ledger.rootState().index, good);
        assertEq(ledger.rootState().hashChain, goodChain);
        assertEq(ledger.rootState().root, 111);
        assertEq(address(ledger.rootVerifier()), address(repaired));
        assertTrue(ledger.provedRoots(good, 111));
        assertFalse(ledger.provedRoots(forged, 222)); // withdrawn for good

        // Nothing was committed since, so the forged root's index is proved again, honestly this time.
        (uint64 idx, uint256 hc) = ledger.reserveHashChain();
        assertEq(idx, forged);
        NovaDeciderProof memory p;
        ledger.proveRootTransition(CommitmentLedger.RootState({index: idx, hashChain: hc, root: 333}), p);
        assertTrue(ledger.provedRoots(forged, 333));
        assertFalse(ledger.provedRoots(forged, 222));
        verifier.transact(_spendAt(forged, 333, 10));

        // A second incident starts era 3; the first era's good root stays accepted.
        uint64 again = _proveRoot(555);
        ledger.enterEmergency(forged);
        ledger.recover(forged, 333, repaired);
        assertEq(ledger.era(), 3);
        assertTrue(ledger.provedRoots(good, 111));
        assertTrue(ledger.provedRoots(forged, 333));
        assertFalse(ledger.provedRoots(again, 555));
        assertFalse(ledger.provedRoots(forged, 222));
    }

    /// @dev As a real verifier does, reject the probe `recover` sends a new verifier: one step from the all-zero
    ///      state, which no root proof starts from.
    function _rejectEmptyProof(IRootDeciderVerifier v) internal {
        vm.mockCallRevert(
            address(v),
            abi.encodeWithSelector(IRootDeciderVerifier.verifyDeciderProof.selector, uint256(1), [uint256(0), 0, 0]),
            ""
        );
    }

    function test_recoverRefusesAVerifierThatTakesAnything() public {
        uint64 good = _proveRoot(111);
        ledger.enterEmergency(good);
        IRootDeciderVerifier lax = new AcceptAll();
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.AcceptsEmptyProof.selector, lax));
        ledger.recover(good, 111, lax);
        vm.expectRevert(bytes("")); // no code: the call reverts before the try
        ledger.recover(good, 111, IRootDeciderVerifier(address(0xC0DE)));

        IRootDeciderVerifier real = new RootDeciderVerifier();
        ledger.recover(good, 111, real);
        assertEq(address(ledger.rootVerifier()), address(real));
    }

    function test_recoverChecks() public {
        uint64 good = _proveRoot(111);
        IRootDeciderVerifier v = ledger.rootVerifier();
        ledger.enterEmergency(good);
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        ledger.recover(good, 111, v); // owner only, so through Admin's delay
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.UnprovedRoot.selector, good, 999));
        ledger.recover(good, 999, v);
        vm.expectRevert(CommitmentLedger.ZeroAddress.selector);
        ledger.recover(good, 111, IRootDeciderVerifier(address(0)));
        ledger.recover(good, 111, v); // a false alarm: the same root and verifier resume
        assertEq(ledger.bound(), type(uint64).max);

        // A withdrawn root cannot be recovered to.
        uint64 forged = _proveRoot(222);
        ledger.enterEmergency(good);
        ledger.recover(good, 111, v);
        ledger.enterEmergency(good);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.UnprovedRoot.selector, forged, 222));
        ledger.recover(forged, 222, v);
        ledger.recover(good, 111, v);

        // A root proved at the live head has no checkpoint once the head moves on: one is recorded first.
        vm.prank(address(verifier));
        uint64 noteIndex = token.commitNote(7);
        uint256 headChain = ledger.hashChain();
        NovaDeciderProof memory p;
        ledger.proveRootTransition(
            CommitmentLedger.RootState({index: noteIndex + 1, hashChain: headChain, root: 777}), p
        );
        vm.prank(address(verifier));
        token.commitNote(8);
        ledger.enterEmergency(noteIndex + 1);
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, noteIndex + 1));
        ledger.recover(noteIndex + 1, 777, v);
        uint256[4][] memory next = new uint256[4][](1);
        next[0] = _note(8);
        ledger.checkpointBefore(noteIndex + 2, headChain, next);
        ledger.recover(noteIndex + 1, 777, v);
        assertEq(ledger.rootState().root, 777);
    }

    function test_recoverCannotRestartBelowThePreviousRecovery() public {
        IRootDeciderVerifier v = ledger.rootVerifier();
        uint64 z = _proveRoot(111);
        uint64 a = _proveRoot(222);
        _proveRoot(333);
        ledger.enterEmergency(a);
        ledger.recover(a, 222, v); // era 1 stays accepted up to a
        _proveRoot(444);
        ledger.enterEmergency(z);

        // Restarting from z would leave era 1's root at a accepted next to the one proved there again.
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.BelowSettledEra.selector, z, a));
        ledger.recover(z, 111, v);
        ledger.recover(a, 222, v); // the restart itself is still open
        assertEq(ledger.era(), 3);
        assertTrue(ledger.provedRoots(z, 111));
        assertTrue(ledger.provedRoots(a, 222));
    }

    function test_provedInKeepsRootsThatProvedRootsRefuses() public {
        uint64 good = _proveRoot(111);
        uint64 forged = _proveRoot(222);
        ledger.enterEmergency(good);
        assertEq(ledger.provedIn(forged, 222), 1);
        assertFalse(ledger.provedRoots(forged, 222)); // above the bound

        ledger.recover(good, 111, ledger.rootVerifier());
        assertEq(ledger.provedIn(forged, 222), 1); // proved by this chain, in era 1
        assertFalse(ledger.provedRoots(forged, 222)); // and withdrawn
        assertEq(ledger.provedIn(forged, 999), 0);
    }
}
