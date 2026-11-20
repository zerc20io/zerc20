// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {PausableUpgradeable} from "@openzeppelin/contracts-upgradeable/utils/PausableUpgradeable.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {Verifier} from "../src/Verifier.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {IMergeDeciderVerifier, NovaDeciderProof} from "../src/interfaces/INovaDeciderVerifier.sol";
import {IJoinSplitVerifier, IRageExitVerifier} from "../src/interfaces/IPrivateProofVerifier.sol";
import {FeeSchedule} from "../src/libs/FeeSchedule.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {JoinSplitGroth16Verifier} from "../src/verifiers/generated/JoinSplitGroth16Verifier.sol";
import {MergeDeciderVerifier} from "../src/verifiers/generated/MergeNovaVerifier.sol";
import {RageExitGroth16Verifier} from "../src/verifiers/generated/RageExitGroth16Verifier.sol";
import {BURN_NULLIFIER} from "./RageExitFixture.sol";
import {AcceptAll} from "./mocks/AcceptAll.sol";
import {MockToken} from "./mocks/MockToken.sol";
import {ProtocolTest} from "./utils/ProtocolTest.sol";

/// @dev Calls back into the Verifier when paid the native asset, and keeps what that call reverted with and the fee
///      accrued so far.
contract VerifierReenterer {
    Verifier private immutable VERIFIER;
    bytes public reentryError;
    uint256 public accruedWhenPaid;

    constructor(Verifier verifier_) {
        VERIFIER = verifier_;
    }

    receive() external payable {
        accruedWhenPaid = VERIFIER.accruedFees(1, VERIFIER.feeRecipient(1));
        try VERIFIER.claimFees(1, address(this)) {}
        catch (bytes memory err) {
            reentryError = err;
        }
    }
}

contract VerifierTest is ProtocolTest {
    function _transactAt(Verifier.TransactSignals memory s, uint64 rootIndex)
        internal
        view
        returns (Verifier.TransactRequest memory r)
    {
        r = _attested(s);
        r.rootIndex = rootIndex;
    }

    function _expectTransactRevert(Verifier.TransactSignals memory s, bytes memory err) internal {
        Verifier.TransactRequest memory r = _attested(s);
        vm.expectRevert(err);
        verifier.transact(r);
    }

    function _two(uint256 a, uint256 b) internal pure returns (uint256[] memory list) {
        list = new uint256[](2);
        (list[0], list[1]) = (a, b);
    }

    // ---- transact ------------------------------------------------------------------------------

    function test_transactMintsAndSpendsOnce() public {
        Verifier.TransactRequest memory r = _signals(2 ether, bob, 10);
        verifier.transact(r);
        assertEq(token.balanceOf(bob), 2 ether);
        assertTrue(verifier.nullifierUsed(10));
        assertTrue(verifier.nullifierUsed(11));
        assertEq(ledger.nextIndex(), 2); // mint is not a leaf; 2 notes
        // a spent nullifier reverts before the proof is checked
        vm.mockCallRevert(address(verifier.joinSplitVerifier()), new bytes(0), "");
        vm.expectRevert(abi.encodeWithSelector(Verifier.NullifierAlreadyUsed.selector, 10));
        verifier.transact(r);
    }

    function test_transactEmitsItsSpendsNotesAndFee() public {
        verifier.setFee(1, carol, _flatFee(100));
        vm.expectEmit(address(verifier));
        emit Verifier.NullifierSpent(10);
        vm.expectEmit(address(verifier));
        emit Verifier.NullifierSpent(11);
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(0, [Protocol.encode(Protocol.NOTE_HASH_TAG, 1), 5, 0, 0]);
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(1, [Protocol.encode(Protocol.NOTE_HASH_TAG, 1), 6, 0, 0]);
        vm.expectEmit(address(verifier));
        emit Verifier.FeeAccrued(1, carol, 0.01 ether);
        vm.expectEmit(address(verifier));
        emit Verifier.Transacted(address(this), 1, Protocol.EMPTY_ROOT, bob, 1 ether, 0.01 ether, 5, 6, 0, 1);
        verifier.transact(_signals(1 ether, bob, 10));
    }

    function test_aTransactWithoutAWithdrawalPaysNoFee() public {
        verifier.setFee(1, carol, _flatFee(100));
        vm.expectEmit(address(verifier));
        emit Verifier.Transacted(address(this), 1, Protocol.EMPTY_ROOT, address(0), 0, 0, 5, 6, 0, 1);
        verifier.transact(_signals(0, address(0), 10));
        assertEq(token.totalSupply(), 0);
        assertEq(verifier.accruedFees(1, carol), 0);
        assertEq(ledger.nextIndex(), 2);
    }

    function test_transactHandsTheVerifierItsSignalsInCircuitOrder() public {
        Verifier.TransactSignals memory s = Verifier.TransactSignals({
            tokenId: 1,
            chainId: block.chainid,
            commitmentRoot: Protocol.EMPTY_ROOT,
            aspRoot: 1,
            nullifier0: 101,
            nullifier1: 102,
            withdrawRecipient: uint256(uint160(bob)),
            withdrawAmount: 3,
            withdrawIntent: 0,
            noteHash1: 104,
            noteHash2: 105
        });
        Verifier.TransactRequest memory r = _attested(s);
        r.proof.pA = [uint256(1), 2];
        r.proof.pC = [uint256(3), 4];
        uint256[11] memory signals =
            [uint256(101), 102, uint256(uint160(bob)), 3, 0, 104, 105, 1, block.chainid, Protocol.EMPTY_ROOT, 1];
        vm.expectCall(
            address(verifier.joinSplitVerifier()),
            abi.encodeCall(IJoinSplitVerifier.verifyProof, (r.proof.pA, r.proof.pB, r.proof.pC, signals))
        );
        verifier.transact(r);
    }

    function test_transactRejectsAProofItsVerifierRefuses() public {
        address joinSplit = address(verifier.joinSplitVerifier());
        Verifier.TransactRequest memory r = _signals(1 ether, bob, 10);
        vm.mockCall(joinSplit, abi.encodeWithSelector(IJoinSplitVerifier.verifyProof.selector), abi.encode(false));
        vm.expectRevert(Verifier.InvalidProof.selector);
        verifier.transact(r);
        vm.mockCallRevert(joinSplit, abi.encodeWithSelector(IJoinSplitVerifier.verifyProof.selector), "");
        vm.expectRevert(Verifier.InvalidProof.selector);
        verifier.transact(r);
        assertFalse(verifier.nullifierUsed(10));
    }

    function test_transactRejectsSignalsOutsideTheirRanges() public {
        uint256 p = Protocol.FIELD_MODULUS;
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 10);
        s.chainId = block.chainid + 1;
        _expectTransactRevert(
            s, abi.encodeWithSelector(Verifier.InvalidChainId.selector, block.chainid + 1, block.chainid)
        );

        s = _transactSignals(1 ether, bob, 10);
        s.commitmentRoot = p;
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.InvalidField.selector, p));
        for (uint256 i; i < 5; ++i) {
            s = _transactSignals(1 ether, bob, 10);
            if (i == 0) s.aspRoot = p;
            else if (i == 1) s.nullifier0 = p;
            else if (i == 2) s.nullifier1 = p;
            else if (i == 3) s.noteHash1 = p;
            else s.noteHash2 = p;
            _expectTransactRevert(s, abi.encodeWithSelector(Verifier.InvalidField.selector, p));
        }

        s = _transactSignals(Protocol.AMOUNT_BOUND, bob, 10);
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.InvalidAmount.selector, Protocol.AMOUNT_BOUND));
        s = _transactSignals(1 ether, bob, 10);
        s.withdrawRecipient = uint256(1) << 160;
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.InvalidAddress.selector, uint256(1) << 160));
    }

    function test_transactUsesOnlyAProvedRootAtItsIndex() public {
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 10);
        s.commitmentRoot = 123;
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.UnprovedRoot.selector, 0, 123));

        Verifier.TransactRequest memory r = _transactAt(_transactSignals(1 ether, bob, 10), 1);
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnprovedRoot.selector, 1, Protocol.EMPTY_ROOT));
        verifier.transact(r);

        uint64 idx = _proveRoot(777);
        s.commitmentRoot = 777;
        verifier.transact(_transactAt(s, idx));
        assertEq(token.balanceOf(bob), 1 ether);
    }

    function test_transactRejectsInconsistentStatements() public {
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 10);
        s.nullifier1 = s.nullifier0;
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.DuplicateNullifier.selector, 10));

        s = _transactSignals(0, bob, 10); // no withdrawal names no recipient
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.NonCanonicalRecipient.selector, uint256(uint160(bob))));
        s = _transactSignals(1 ether, address(0), 10);
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.ZeroRecipient.selector));
    }

    function test_transactNeedsARegisteredRunningToken() public {
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 10);
        s.tokenId = 99;
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.UnregisteredToken.selector, 99));
        s.tokenId = (uint256(1) << 32) + 1; // token 1 once truncated to 32 bits
        _expectTransactRevert(s, abi.encodeWithSelector(Verifier.UnregisteredToken.selector, s.tokenId));

        verifier.pauseToken(1);
        _expectTransactRevert(
            _transactSignals(1 ether, bob, 10), abi.encodeWithSelector(Verifier.TokenPaused.selector, uint32(1))
        );
        verifier.unpauseToken(1);
        verifier.pause();
        _expectTransactRevert(
            _transactSignals(1 ether, bob, 10), abi.encodeWithSelector(PausableUpgradeable.EnforcedPause.selector)
        );
    }

    function test_transactUnwrapsToTheUnderlying() public {
        address burn = address(0xB0E);
        _wrap(alice, 2 ether, burn); // the deposit that backs the withdrawal
        verifier.setFee(1, carol, _flatFee(100)); // 1%

        vm.expectEmit(address(token));
        emit ZERC20.Unwrapped(address(verifier), bob, 1.98 ether);
        verifier.transact(_unwrapSignals(2 ether, bob, 110));
        assertEq(bob.balance, 1.98 ether); // no zETH, so no gas needed to unwrap
        assertEq(token.balanceOf(bob), 0);
        assertEq(verifier.accruedFees(1, carol), 0.02 ether); // the fee is still minted as zETH
        assertEq(address(token).balance, 0.02 ether); // which is what is left backing it
        assertEq(ledger.nextIndex(), 3); // the deposit and 2 notes

        MockToken usdc = new MockToken(6);
        ZERC20 zusdc = ZERC20(payable(factory.createToken(address(usdc), "zUSDC", "zUSDC", 6)));
        deal(address(usdc), alice, 5e6);
        vm.startPrank(alice);
        usdc.approve(address(zusdc), 5e6);
        zusdc.wrap(5e6, burn);
        vm.stopPrank();
        Verifier.TransactSignals memory s = _transactSignals(5e6, bob, 112);
        s.tokenId = 2;
        s.withdrawIntent = Protocol.UNWRAP_INTENT;
        verifier.transact(_attested(s));
        assertEq(usdc.balanceOf(bob), 5e6);
        assertEq(zusdc.balanceOf(bob), 0);

        vm.expectRevert(abi.encodeWithSelector(ZERC20.Unauthorized.selector, address(this)));
        token.payOut(bob, 1, true); // Verifier only
    }

    function test_anUnwrapRecipientIsCalledLastAndCannotReenterTheVerifier() public {
        _wrap(alice, 1 ether, address(0xB0E));
        verifier.setFee(1, carol, _flatFee(100));
        VerifierReenterer recipient = new VerifierReenterer(verifier);
        verifier.transact(_unwrapSignals(1 ether, address(recipient), 10));
        assertEq(address(recipient).balance, 0.99 ether);
        assertEq(recipient.accruedWhenPaid(), 0.01 ether); // the fee is settled before the recipient runs
        assertEq(
            recipient.reentryError(),
            abi.encodeWithSelector(ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector)
        );
    }

    function test_transactRejectsUnsupportedWithdrawIntents() public {
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 120);
        s.withdrawIntent = 1; // no such intent
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnsupportedWithdrawIntent.selector, 1));
        verifier.transact(_attested(s));

        s = _transactSignals(0, address(0), 120);
        s.withdrawIntent = Protocol.UNWRAP_INTENT; // nothing to pay out
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnsupportedWithdrawIntent.selector, Protocol.UNWRAP_INTENT));
        verifier.transact(_attested(s));

        Verifier.TransactRequest memory tampered = _signals(1 ether, bob, 120);
        tampered.publicSignals.withdrawIntent = Protocol.UNWRAP_INTENT; // the attester signed a mint
        vm.expectPartialRevert(Verifier.UnauthorizedAttestation.selector);
        verifier.transact(tampered);
    }

    // ---- attestations --------------------------------------------------------------------------

    function test_transactAndMergeNeedAnAttestation() public {
        Verifier.TransactRequest memory tampered = _signals(1 ether, bob, 90);
        tampered.publicSignals.withdrawAmount = 2 ether; // the attester signed 1 ether
        vm.expectPartialRevert(Verifier.UnauthorizedAttestation.selector);
        verifier.transact(tampered);

        (address stranger, uint256 strangerKey) = makeAddrAndKey("stranger");
        Verifier.TransactRequest memory forged = _signals(1 ether, bob, 90);
        forged.attestation = _attest(strangerKey, keccak256(abi.encode(TRANSACT_TYPEHASH, forged.publicSignals)));
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnauthorizedAttestation.selector, stranger));
        verifier.transact(forged);

        Verifier.TransactRequest memory r = _signals(1 ether, bob, 90);
        vm.expectEmit(address(verifier));
        emit Verifier.AttesterSet(attester, false);
        verifier.revokeAttester(attester); // revoking kills outstanding signatures
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnauthorizedAttestation.selector, attester));
        verifier.transact(r);
        vm.expectEmit(address(verifier));
        emit Verifier.AttesterSet(attester, true);
        verifier.addAttester(attester);
        verifier.transact(r);

        Verifier.MergeRequest memory m = _mergeRequest(_two(93, 94));
        m.nullifiers[0] = 95; // the attester signed nullifier 93
        vm.expectPartialRevert(Verifier.UnauthorizedAttestation.selector);
        verifier.merge(m);

        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.addAttester(alice);
        vm.expectRevert(Verifier.ZeroAddress.selector);
        verifier.addAttester(address(0));
    }

    function test_anAttestationIsBoundToThisChainAndVerifier() public {
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 10);
        bytes32 structHash = keccak256(abi.encode(TRANSACT_TYPEHASH, s));
        Verifier.TransactRequest memory r = _attested(s);

        r.attestation = _attestUnder(block.chainid + 1, address(verifier), structHash);
        vm.expectPartialRevert(Verifier.UnauthorizedAttestation.selector);
        verifier.transact(r);
        r.attestation = _attestUnder(block.chainid, address(0xBEEF), structHash);
        vm.expectPartialRevert(Verifier.UnauthorizedAttestation.selector);
        verifier.transact(r);

        r.attestation = new bytes(10);
        vm.expectRevert(abi.encodeWithSelector(ECDSA.ECDSAInvalidSignatureLength.selector, 10));
        verifier.transact(r);
    }

    function _attestUnder(uint256 chainId, address verifyingContract, bytes32 structHash)
        internal
        view
        returns (bytes memory)
    {
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("zERC20 Verifier"),
                keccak256("1"),
                chainId,
                verifyingContract
            )
        );
        (uint8 v, bytes32 r, bytes32 s) =
            vm.sign(attesterKey, keccak256(abi.encodePacked("\x19\x01", domain, structHash)));
        return abi.encodePacked(r, s, v);
    }

    // ---- merge ---------------------------------------------------------------------------------

    function test_mergeSpendsEveryNullifierAndCommitsOneNote() public {
        Verifier.MergeRequest memory r = _mergeRequest(_two(21, 22));
        // SHA256(SHA256(0 || 21) mod 2^248 || 22) mod 2^248, as zkp/src/primitives.rs hash_chain computes it.
        uint256 chain = 372117935037112951106234068472273087244645795842942548021319280872655617899;
        uint256[10] memory z0 = [uint256(1), block.chainid, Protocol.EMPTY_ROOT, 1, 0, chain, 0, 2, 0, 0];
        uint256[10] memory zi = [uint256(1), block.chainid, Protocol.EMPTY_ROOT, 1, chain, chain, 9, 0, 0, 0];
        NovaDeciderProof memory p = r.proof;
        vm.expectCall(
            address(verifier.mergeVerifier()),
            abi.encodeCall(
                IMergeDeciderVerifier.verifyDeciderProof,
                (2, z0, zi, p.challenge, p.runningCmE, p.cmT, p.runningCmW, p.incomingCmW, p.proof)
            )
        );
        vm.expectEmit(address(verifier));
        emit Verifier.NullifierSpent(21);
        vm.expectEmit(address(verifier));
        emit Verifier.NullifierSpent(22);
        vm.expectEmit(address(verifier));
        emit Verifier.Merged(address(this), 1, Protocol.EMPTY_ROOT, 2, 9, 0);
        verifier.merge(r);
        assertTrue(verifier.nullifierUsed(21));
        assertTrue(verifier.nullifierUsed(22));
        assertEq(ledger.nextIndex(), 1); // one output note
        // a spent nullifier reverts before the proof is checked
        vm.mockCallRevert(address(verifier.mergeVerifier()), new bytes(0), "");
        vm.expectRevert(abi.encodeWithSelector(Verifier.NullifierAlreadyUsed.selector, 21));
        verifier.merge(r);
    }

    function test_mergePaysItsFeeToItsRecipient() public {
        verifier.setFee(1, carol, _flatFee(100)); // 1%

        uint256[] memory nullifiers = new uint256[](1);
        nullifiers[0] = 31;
        Verifier.MergeRequest memory r = _paidMerge(nullifiers, 1 ether, bob);
        // the fee and its recipient are part of the folded state, so the proof binds them
        uint256 chain = uint256(sha256(abi.encodePacked(uint256(0), uint256(31)))) & Protocol.HASH_CHAIN_MASK;
        uint256 to = uint256(uint160(bob));
        uint256[10] memory z0 = [uint256(1), block.chainid, Protocol.EMPTY_ROOT, 1, 0, chain, 0, 1, 1 ether, to];
        uint256[10] memory zi = [uint256(1), block.chainid, Protocol.EMPTY_ROOT, 1, chain, chain, 9, 0, 1 ether, to];
        NovaDeciderProof memory p = r.proof;
        vm.expectCall(
            address(verifier.mergeVerifier()),
            abi.encodeCall(
                IMergeDeciderVerifier.verifyDeciderProof,
                (1, z0, zi, p.challenge, p.runningCmE, p.cmT, p.runningCmW, p.incomingCmW, p.proof)
            )
        );
        verifier.merge(r);
        // a public withdrawal to the relayer, so the protocol's withdrawal fee applies
        assertEq(token.balanceOf(bob), 0.99 ether);
        assertEq(verifier.accruedFees(1, carol), 0.01 ether);
        assertEq(ledger.nextIndex(), 1);

        nullifiers[0] = 32;
        vm.expectRevert(Verifier.ZeroRecipient.selector);
        verifier.merge(_paidMerge(nullifiers, 1 ether, address(0)));
        vm.expectRevert(abi.encodeWithSelector(Verifier.NonCanonicalRecipient.selector, to));
        verifier.merge(_paidMerge(nullifiers, 0, bob));
        Verifier.MergeRequest memory huge = _paidMerge(nullifiers, Protocol.AMOUNT_BOUND, bob);
        vm.expectRevert(abi.encodeWithSelector(Verifier.InvalidAmount.selector, Protocol.AMOUNT_BOUND));
        verifier.merge(huge);
        Verifier.MergeRequest memory wide = _paidMerge(nullifiers, 1 ether, bob);
        wide.feeRecipient = 1 << 160;
        wide.attestation = _attest(attesterKey, _mergeStatement(wide));
        vm.expectRevert(abi.encodeWithSelector(Verifier.InvalidAddress.selector, uint256(1 << 160)));
        verifier.merge(wide);

        Verifier.MergeRequest memory raised = _paidMerge(nullifiers, 1 ether, bob);
        raised.fee = 2 ether; // the attester signed 1 ether
        vm.expectPartialRevert(Verifier.UnauthorizedAttestation.selector);
        verifier.merge(raised);
        Verifier.MergeRequest memory redirected = _paidMerge(nullifiers, 1 ether, bob);
        redirected.feeRecipient = uint256(uint160(alice));
        vm.expectPartialRevert(Verifier.UnauthorizedAttestation.selector);
        verifier.merge(redirected);
    }

    function test_mergeRejectsEmptyDuplicateAndInvalidRequests() public {
        vm.expectRevert(Verifier.EmptyMerge.selector);
        verifier.merge(_mergeRequest(new uint256[](0)));

        vm.expectRevert(abi.encodeWithSelector(Verifier.NullifierAlreadyUsed.selector, 5));
        verifier.merge(_mergeRequest(_two(5, 5)));
        vm.expectRevert(abi.encodeWithSelector(Verifier.InvalidField.selector, Protocol.FIELD_MODULUS));
        verifier.merge(_mergeRequest(_two(5, Protocol.FIELD_MODULUS)));

        vm.mockCallRevert(
            address(verifier.mergeVerifier()),
            abi.encodeWithSelector(IMergeDeciderVerifier.verifyDeciderProof.selector),
            ""
        );
        vm.expectRevert(Verifier.InvalidProof.selector);
        verifier.merge(_mergeRequest(new uint256[](1)));
    }

    function test_mergeChecksItsTokenRootsAndOutputNote() public {
        Verifier.MergeRequest memory r = _mergeRequest(_two(41, 42));
        r.tokenId = 99;
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnregisteredToken.selector, 99));
        verifier.merge(r);

        r = _mergeRequest(_two(41, 42));
        r.commitmentRoot = 123;
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnprovedRoot.selector, 0, 123));
        verifier.merge(r);

        r = _mergeRequest(_two(41, 42));
        r.aspRoot = 3;
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnacceptedAspRoot.selector, 3));
        verifier.merge(r);

        r = _mergeRequest(_two(41, 42));
        r.noteHash = Protocol.FIELD_MODULUS;
        vm.expectRevert(abi.encodeWithSelector(Verifier.InvalidField.selector, Protocol.FIELD_MODULUS));
        verifier.merge(r);

        r = _mergeRequest(_two(41, 42));
        verifier.pauseToken(1);
        vm.expectRevert(abi.encodeWithSelector(Verifier.TokenPaused.selector, uint32(1)));
        verifier.merge(r);
        verifier.unpauseToken(1);
        verifier.pause();
        vm.expectRevert(PausableUpgradeable.EnforcedPause.selector);
        verifier.merge(r);
        verifier.unpause();
        verifier.merge(r);
    }

    // ---- rage exit -----------------------------------------------------------------------------

    function test_rageExitWalksTheHashChainWithoutAProvedRoot() public {
        uint256[4][] memory commits = _burnDeposit();
        (uint64 end,) = ledger.reserveHashChain();
        assertEq(ledger.rootState().index, 0); // no root covers the deposit

        vm.expectEmit(address(verifier));
        emit Verifier.NullifierSpent(BURN_NULLIFIER);
        vm.expectEmit(address(verifier));
        emit Verifier.RageExited(bob, 1, alice, 1 ether, BURN_NULLIFIER);
        vm.prank(bob); // anyone may send it; the refund goes to the sender of the deposit
        verifier.rageExit(_rageExit(end, 0, commits));
        assertEq(token.balanceOf(alice), 1 ether);
        assertTrue(verifier.nullifierUsed(BURN_NULLIFIER));

        vm.expectRevert(abi.encodeWithSelector(Verifier.NullifierAlreadyUsed.selector, BURN_NULLIFIER));
        verifier.rageExit(_rageExit(end, 0, commits));
    }

    function test_rageExitWalksBackOverLaterCommits() public {
        uint256[4][] memory deposit = _burnDeposit();
        vm.prank(address(verifier));
        token.commitNote(7);
        (uint64 end,) = ledger.reserveHashChain();
        uint256[4][] memory both = new uint256[4][](2);
        both[0] = deposit[0];
        both[1] = [Protocol.encode(Protocol.NOTE_HASH_TAG, 1), 7, 0, 0];
        verifier.rageExit(_rageExit(end, 0, both)); // the proof is for index 0, where the walk starts
        assertEq(token.balanceOf(alice), 1 ether);
    }

    function test_rageExitRejectsForgedDeposits() public {
        uint256[4][] memory commits = _burnDeposit();
        (uint64 end,) = ledger.reserveHashChain();

        uint256[4][] memory inflated = new uint256[4][](1);
        inflated[0] = [commits[0][0], commits[0][1], commits[0][2], 2 ether];
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, end));
        verifier.rageExit(_rageExit(end, 0, inflated));
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, end));
        verifier.rageExit(_rageExit(end, 1, commits)); // wrong chain before the deposit
        vm.expectRevert(abi.encodeWithSelector(CommitmentLedger.CheckpointMismatch.selector, end + 1));
        verifier.rageExit(_rageExit(end + 1, 0, commits)); // nothing recorded there

        Verifier.RageExitRequest memory wrongNullifier = _rageExit(end, 0, commits);
        wrongNullifier.nullifier += 1;
        vm.expectRevert(Verifier.InvalidProof.selector);
        verifier.rageExit(wrongNullifier);
        wrongNullifier.nullifier = Protocol.FIELD_MODULUS;
        vm.expectRevert(abi.encodeWithSelector(Verifier.InvalidField.selector, Protocol.FIELD_MODULUS));
        verifier.rageExit(wrongNullifier);
        vm.mockCallRevert(
            address(verifier.rageExitVerifier()), abi.encodeWithSelector(IRageExitVerifier.verifyProof.selector), ""
        );
        vm.expectRevert(Verifier.InvalidProof.selector); // a verifier that reverts is a refusal too
        verifier.rageExit(_rageExit(end, 0, commits));
        vm.clearMockedCalls();

        // A note commitment authenticates fine but is not a burn deposit.
        uint256 beforeNote = ledger.hashChain();
        vm.prank(address(verifier));
        uint64 noteIndex = token.commitNote(5);
        uint256[4][] memory note = new uint256[4][](1);
        note[0] = [Protocol.encode(Protocol.NOTE_HASH_TAG, 1), 5, 0, 0];
        vm.expectRevert(abi.encodeWithSelector(Verifier.NotATransfer.selector, noteIndex));
        verifier.rageExit(_rageExit(noteIndex + 1, beforeNote, note)); // live head as the end
    }

    function test_rageExitStopsWithEitherPause() public {
        uint256[4][] memory commits = _burnDeposit();
        (uint64 end,) = ledger.reserveHashChain();
        Verifier.RageExitRequest memory r = _rageExit(end, 0, commits);

        verifier.pause();
        vm.expectRevert(PausableUpgradeable.EnforcedPause.selector);
        verifier.rageExit(r);
        verifier.unpause();
        verifier.pauseToken(1);
        vm.expectRevert(abi.encodeWithSelector(Verifier.TokenPaused.selector, uint32(1)));
        verifier.rageExit(r);
        verifier.unpauseToken(1);
        verifier.rageExit(r);
    }

    function test_aBlockedSenderGetsNoRefundUntilUnblocked() public {
        uint256[4][] memory commits = _burnDeposit();
        (uint64 end,) = ledger.reserveHashChain();
        _setBlocked(alice, true);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.BlockedAddress.selector, alice));
        verifier.rageExit(_rageExit(end, 0, commits));
        _setBlocked(alice, false);
        verifier.rageExit(_rageExit(end, 0, commits));
        assertEq(token.balanceOf(alice), 1 ether);
    }

    // ---- ASP -----------------------------------------------------------------------------------

    function test_aspRootsStayAcceptedUntilThePublisherIsReplaced() public {
        vm.expectEmit(address(verifier));
        emit Verifier.AspRootPublished(2);
        verifier.publishAspRoot(2);
        assertEq(verifier.latestAspRoot(), 2);
        assertTrue(verifier.aspRootAccepted(1)); // older roots approve a subset and stay accepted
        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 100);
        s.aspRoot = 3;
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnacceptedAspRoot.selector, 3));
        verifier.transact(_attested(s));

        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(Verifier.Unauthorized.selector, alice));
        verifier.publishAspRoot(4);
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.setAspPublisher(alice);

        // Replacing the publisher drops every root; only the new publisher brings them back.
        vm.expectEmit(address(verifier));
        emit Verifier.AspPublisherSet(alice);
        verifier.setAspPublisher(alice);
        assertEq(verifier.aspPublisher(), alice);
        assertFalse(verifier.aspRootAccepted(1));
        assertFalse(verifier.aspRootAccepted(2));
        assertEq(verifier.latestAspRoot(), 0);
        Verifier.TransactRequest memory r = _signals(1 ether, bob, 100);
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnacceptedAspRoot.selector, 1));
        verifier.transact(r);
        vm.expectRevert(abi.encodeWithSelector(Verifier.Unauthorized.selector, address(this)));
        verifier.publishAspRoot(1);
        vm.prank(alice);
        verifier.publishAspRoot(1);
        verifier.transact(r);
        assertEq(token.balanceOf(bob), 1 ether);
    }

    function test_publishAspRootTakesOnlyNonZeroFieldElements() public {
        vm.expectRevert(abi.encodeWithSelector(Verifier.InvalidField.selector, 0));
        verifier.publishAspRoot(0); // zero stands for no root published
        vm.expectRevert(abi.encodeWithSelector(Verifier.InvalidField.selector, Protocol.FIELD_MODULUS));
        verifier.publishAspRoot(Protocol.FIELD_MODULUS);
        assertFalse(verifier.aspRootAccepted(0));
        verifier.publishAspRoot(Protocol.FIELD_MODULUS - 1);
        assertTrue(verifier.aspRootAccepted(Protocol.FIELD_MODULUS - 1));
    }

    function test_revokingThePublisherOrAnAttesterStopsSpends() public {
        Verifier.TransactRequest memory r = _signals(1 ether, bob, 110);
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.revokeAspPublisher();
        vm.expectEmit(address(verifier));
        emit Verifier.AspPublisherSet(address(0));
        verifier.revokeAspPublisher(); // drops every root, like setAspPublisher
        assertEq(verifier.aspPublisher(), address(0));
        assertFalse(verifier.aspRootAccepted(1));
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnacceptedAspRoot.selector, 1));
        verifier.transact(r);
        vm.expectRevert(abi.encodeWithSelector(Verifier.Unauthorized.selector, address(this)));
        verifier.publishAspRoot(1);

        verifier.setAspPublisher(address(this));
        verifier.publishAspRoot(1);
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.revokeAttester(attester);
        verifier.revokeAttester(attester);
        assertFalse(verifier.isAttester(attester));
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnauthorizedAttestation.selector, attester));
        verifier.transact(r);
    }

    // ---- fees ----------------------------------------------------------------------------------

    function test_withdrawFeeAccruesAndIsClaimed() public {
        FeeSchedule.Tier[] memory tiers = new FeeSchedule.Tier[](2);
        tiers[0] = FeeSchedule.Tier({minAmount: 0, feeBps: 100}); // 1%
        tiers[1] = FeeSchedule.Tier({minAmount: 10 ether, feeBps: 50}); // 0.5% from 10 ether
        vm.expectEmit(address(verifier));
        emit Verifier.FeeSet(1, carol, 2);
        verifier.setFee(1, carol, tiers);
        assertEq(verifier.feeRecipient(1), carol);
        assertEq(verifier.withdrawFee(1, 2 ether), 0.02 ether);
        assertEq(verifier.withdrawFee(1, 10 ether), 0.05 ether);

        verifier.transact(_signals(2 ether, bob, 20));
        assertEq(token.balanceOf(bob), 1.98 ether);
        assertEq(token.balanceOf(address(verifier)), 0.02 ether);
        assertEq(verifier.accruedFees(1, carol), 0.02 ether);

        vm.expectEmit(address(verifier));
        emit Verifier.FeesClaimed(1, carol, 0.02 ether);
        vm.prank(bob); // anyone may trigger; pays only carol
        assertEq(verifier.claimFees(1, carol), 0.02 ether);
        assertEq(token.balanceOf(carol), 0.02 ether);
        assertEq(verifier.accruedFees(1, carol), 0);

        // blocked recipient stays frozen until unblocked
        verifier.transact(_signals(2 ether, bob, 40));
        _setBlocked(carol, true);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.BlockedAddress.selector, carol));
        verifier.claimFees(1, carol);
        assertEq(verifier.accruedFees(1, carol), 0.02 ether);
        _setBlocked(carol, false);
        verifier.claimFees(1, carol);
        assertEq(token.balanceOf(carol), 0.04 ether);
    }

    function test_feesStayWithTheRecipientOfTheirSettlement() public {
        verifier.setFee(1, carol, _flatFee(100));
        verifier.transact(_signals(2 ether, bob, 10));
        verifier.setFee(1, alice, _flatFee(100));
        verifier.transact(_signals(1 ether, bob, 20));
        assertEq(verifier.accruedFees(1, carol), 0.02 ether);
        assertEq(verifier.accruedFees(1, alice), 0.01 ether);
        verifier.claimFees(1, carol);
        assertEq(token.balanceOf(carol), 0.02 ether);
    }

    function test_claimingNothingPaysNothing() public {
        vm.recordLogs();
        assertEq(verifier.claimFees(1, carol), 0);
        assertEq(verifier.claimFees(99, carol), 0); // no token, nothing accrued
        assertEq(vm.getRecordedLogs().length, 0);
    }

    function test_feeConfigIsOwnerOnlyAndValidated() public {
        FeeSchedule.Tier[] memory bad = new FeeSchedule.Tier[](1);
        bad[0] = FeeSchedule.Tier({minAmount: 1, feeBps: 10}); // first tier must start at 0
        vm.expectRevert(FeeSchedule.InvalidFeeConfig.selector);
        verifier.setFee(1, bob, bad);
        bad[0] = FeeSchedule.Tier({minAmount: 0, feeBps: 301}); // above the 3% cap
        vm.expectRevert(FeeSchedule.InvalidFeeConfig.selector);
        verifier.setFee(1, bob, bad);
        bad[0] = FeeSchedule.Tier({minAmount: 0, feeBps: 300});
        verifier.setFee(1, bob, bad);
        bad[0] = FeeSchedule.Tier({minAmount: 0, feeBps: 10});
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.setFee(1, bob, bad);
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnregisteredToken.selector, 99));
        verifier.setFee(99, bob, bad);
    }

    function test_aChargedFeeCannotGoToABlockedAccount() public {
        _setBlocked(carol, true);
        vm.expectRevert(abi.encodeWithSelector(Verifier.BlockedAddress.selector, carol));
        verifier.setFee(1, carol, _flatFee(100));
        verifier.setFee(1, carol, _flatFee(0)); // nothing will be owed to it
        assertEq(verifier.withdrawFee(1, 1 ether), 0);
    }

    // ---- pause ---------------------------------------------------------------------------------

    function test_pauseTokenStopsOnlyThatToken() public {
        ZERC20 token2 = ZERC20(payable(factory.createToken(address(new MockToken(18)), "Foo", "FOO", 18)));
        _wrap(alice, 1 ether, alice);
        vm.expectEmit(address(verifier));
        emit Verifier.TokenPausedUpdated(1, true);
        verifier.pauseToken(1);
        assertTrue(verifier.tokenPaused(1));
        assertTrue(verifier.tokenStopped(1));
        assertFalse(verifier.tokenStopped(2));
        vm.expectRevert(abi.encodeWithSelector(Verifier.TokenPaused.selector, uint32(1)));
        verifier.transact(_signals(1 ether, bob, 70)); // token 1 is paused
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.TokenStopped.selector, uint32(1)));
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        token.transfer(bob, 1); // and so is the token itself

        Verifier.TransactSignals memory s = _transactSignals(1 ether, bob, 70);
        s.tokenId = 2;
        verifier.transact(_attested(s)); // token 2 is unaffected
        assertEq(token2.balanceOf(bob), 1 ether);
        vm.prank(bob);
        assertTrue(token2.transfer(alice, 1));

        vm.expectEmit(address(verifier));
        emit Verifier.TokenPausedUpdated(1, false);
        verifier.unpauseToken(1);
        assertFalse(verifier.tokenStopped(1));
        verifier.transact(_signals(1 ether, bob, 72));
        vm.prank(alice);
        assertTrue(token.transfer(bob, 1));

        verifier.pause(); // the global pause stops every token
        assertTrue(verifier.tokenStopped(1));
        assertTrue(verifier.tokenStopped(2));
        assertFalse(verifier.tokenPaused(2));
        verifier.unpause();

        vm.expectRevert(abi.encodeWithSelector(Verifier.UnregisteredToken.selector, 99));
        verifier.pauseToken(99);
        vm.expectRevert(abi.encodeWithSelector(Verifier.UnregisteredToken.selector, 99));
        verifier.unpauseToken(99);
        vm.startPrank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.pauseToken(1);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.pause();
        vm.stopPrank();
    }

    // ---- proof verifiers -----------------------------------------------------------------------

    function test_proofVerifiersAreReplacedByTheOwner() public {
        // the mock took any proof; the real verifier, once in, refuses the same request
        Verifier.TransactRequest memory r = _signals(1 ether, bob, 80);
        JoinSplitGroth16Verifier joinSplit = new JoinSplitGroth16Verifier();
        vm.expectEmit(address(verifier));
        emit Verifier.JoinSplitVerifierSet(joinSplit);
        verifier.setJoinSplitVerifier(joinSplit);
        assertEq(address(verifier.joinSplitVerifier()), address(joinSplit));
        vm.expectRevert(Verifier.InvalidProof.selector);
        verifier.transact(r);

        RageExitGroth16Verifier rageExit = new RageExitGroth16Verifier();
        vm.expectEmit(address(verifier));
        emit Verifier.RageExitVerifierSet(rageExit);
        verifier.setRageExitVerifier(rageExit);
        assertEq(address(verifier.rageExitVerifier()), address(rageExit));
        MergeDeciderVerifier merge = new MergeDeciderVerifier();
        vm.expectEmit(address(verifier));
        emit Verifier.MergeVerifierSet(merge);
        verifier.setMergeVerifier(merge);
        assertEq(address(verifier.mergeVerifier()), address(merge));

        // one that takes an empty proof, an account without code and the zero address are refused
        address acceptAll = address(new AcceptAll());
        address[3] memory wrong = [acceptAll, address(0xBEEF), address(0)];
        for (uint256 i; i < wrong.length; ++i) {
            bytes memory refused = abi.encodeWithSelector(Verifier.AcceptsEmptyProof.selector, wrong[i]);
            vm.expectRevert(refused);
            verifier.setJoinSplitVerifier(IJoinSplitVerifier(wrong[i]));
            vm.expectRevert(refused);
            verifier.setRageExitVerifier(IRageExitVerifier(wrong[i]));
            vm.expectRevert(refused);
            verifier.setMergeVerifier(IMergeDeciderVerifier(wrong[i]));
        }

        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        verifier.setJoinSplitVerifier(joinSplit);
    }
}
