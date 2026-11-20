// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {stdError} from "forge-std/StdError.sol";
import {Vm} from "forge-std/Vm.sol";
import {ERC1967Proxy} from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol";
import {Errors} from "@openzeppelin/contracts/utils/Errors.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {DepositAddress, DepositAddressFactory} from "../src/DepositAddress.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {ITokenRegistry} from "../src/interfaces/ITokenRegistry.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {MockToken} from "./mocks/MockToken.sol";
import {ProtocolTest} from "./utils/ProtocolTest.sol";

/// @dev A fee recipient or referrer that flushes its deposit address again when paid, keeping what that call reverted
///      with, or that refuses the payment outright.
contract FeeRecipient {
    bool public refuse;
    bytes public reentryError;

    function setRefuse(bool refuse_) external {
        refuse = refuse_;
    }

    receive() external payable {
        require(!refuse);
        try DepositAddress(payable(msg.sender)).flush() {}
        catch (bytes memory err) {
            reentryError = err;
        }
    }
}

/// @dev Reverts on a zero transfer, as some ERC-20s do.
contract NoZeroTransfers is MockToken {
    constructor() MockToken(6) {}

    function _update(address from, address to, uint256 value) internal override {
        require(value != 0, "zero transfer");
        super._update(from, to, value);
    }
}

contract DepositAddressTest is ProtocolTest {
    /// @dev Where a deposit address's fee goes: the relayer that registered it, whoever flushes.
    address constant FEE_TO = address(0xFEE);
    address constant BURN = address(0xB0E);
    /// @dev The app that handed a deposit address out.
    address constant REFERRER = address(0xAFF);

    function test_depositAddressWrapsErc20IntoTheBurnAddress() public {
        MockToken usdc = new MockToken(6);
        ZERC20 zusdc = ZERC20(payable(factory.createToken(address(usdc), "zUSDC", "zUSDC", 6)));
        address deposit = deposits.predict(zusdc, BURN, alice, address(0), FEE_TO, 1e6, address(0), 0);

        deal(address(usdc), deposit, 100e6); // a plain transfer, e.g. a CEX withdrawal
        // The burn leaf's `from` is the deposit address, which the circuit and the ASP take as is.
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(
            0, [Protocol.encode(Protocol.TRANSFER_TAG, 2), uint256(uint160(deposit)), uint256(uint160(BURN)), 99e6]
        );
        vm.prank(bob); // anyone may flush; the fee still goes to its recipient
        assertEq(deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 1e6, address(0), 0), deposit);
        assertEq(zusdc.balanceOf(BURN), 99e6);
        assertEq(usdc.balanceOf(FEE_TO), 1e6);
        assertEq(usdc.balanceOf(deposit), 0);
        assertEq(usdc.allowance(deposit, address(zusdc)), 0); // the approval is used up

        deal(address(usdc), deposit, 5e6); // reusable once deployed
        deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 1e6, address(0), 0);
        assertEq(zusdc.balanceOf(BURN), 103e6);
        assertEq(usdc.balanceOf(FEE_TO), 2e6);
        assertEq(ledger.nextIndex(), 2);

        deal(address(usdc), deposit, 1e6); // no more than the fee: nothing to wrap
        vm.expectRevert(ZERC20.ZeroAmount.selector);
        deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 1e6, address(0), 0);
    }

    function test_depositAddressWrapsNative() public {
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);

        vm.deal(deposit, 2 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        assertEq(token.balanceOf(BURN), 1.99 ether);
        assertEq(FEE_TO.balance, 0.01 ether);
        assertEq(deposit.balance, 0);

        vm.deal(alice, 1 ether);
        vm.prank(alice);
        (bool ok,) = deposit.call{value: 1 ether}(""); // the deployed clone still accepts native
        assertTrue(ok);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        assertEq(token.balanceOf(BURN), 2.98 ether);
        assertEq(FEE_TO.balance, 0.02 ether);

        vm.deal(deposit, 0.005 ether); // less than the fee
        vm.expectRevert(stdError.arithmeticError);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
    }

    function test_theCloneIsCreatedOnceAtThePredictedAddress() public {
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        assertEq(deposit.code.length, 0);
        vm.deal(deposit, 1 ether);
        vm.expectEmit(address(deposits));
        emit DepositAddressFactory.DepositAddressCreated(
            deposit, address(token), BURN, alice, address(0), FEE_TO, 0, address(0), 0
        );
        assertEq(deposits.flush(token, BURN, alice, address(0), FEE_TO, 0, address(0), 0), deposit);
        assertGt(deposit.code.length, 0);
        assertEq(token.balanceOf(BURN), 1 ether); // without a fee everything is wrapped

        vm.deal(deposit, 1 ether);
        vm.recordLogs();
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        for (uint256 i; i < logs.length; ++i) {
            assertNotEq(logs[i].topics[0], DepositAddressFactory.DepositAddressCreated.selector);
        }

        // every argument is part of the address
        assertNotEq(deposits.predict(token, BURN, alice, address(0), FEE_TO, 1, address(0), 0), deposit);
        assertNotEq(deposits.predict(token, BURN, bob, address(0), FEE_TO, 0, address(0), 0), deposit);
        assertNotEq(deposits.predict(token, bob, alice, address(0), FEE_TO, 0, address(0), 0), deposit);
        assertNotEq(deposits.predict(token, BURN, address(0), alice, FEE_TO, 0, address(0), 0), deposit);
        assertNotEq(deposits.predict(token, BURN, alice, address(0), bob, 0, address(0), 0), deposit);
        assertNotEq(deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, REFERRER, 0), deposit);
        assertNotEq(
            deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, REFERRER, 1),
            deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, REFERRER, 0)
        );
        assertEq(address(deposits.registry()), address(factory));
        assertGt(deposits.depositImplementation().code.length, 0);
    }

    function test_aReferrerTakesItsShareOfWhatIsLeftAfterTheFee() public {
        NoZeroTransfers usdc = new NoZeroTransfers();
        ZERC20 zusdc = ZERC20(payable(factory.createToken(address(usdc), "zUSDC", "zUSDC", 6)));
        address deposit = deposits.predict(zusdc, BURN, alice, address(0), FEE_TO, 1e6, REFERRER, 30);

        deal(address(usdc), deposit, 101e6);
        vm.expectEmit(address(deposits));
        emit DepositAddressFactory.DepositAddressCreated(
            deposit, address(zusdc), BURN, alice, address(0), FEE_TO, 1e6, REFERRER, 30
        );
        deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 1e6, REFERRER, 30);
        assertEq(usdc.balanceOf(FEE_TO), 1e6);
        assertEq(usdc.balanceOf(REFERRER), 0.3e6); // 0.3% of the 100 left after the fee
        assertEq(zusdc.balanceOf(BURN), 99.7e6);
        assertEq(usdc.balanceOf(deposit), 0);

        deal(address(usdc), deposit, 1e6 + 33); // a referral that rounds down to nothing is not paid
        deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 1e6, REFERRER, 30);
        assertEq(usdc.balanceOf(REFERRER), 0.3e6);
        assertEq(zusdc.balanceOf(BURN), 99.7e6 + 33);
    }

    function test_aReferrerTakesItsShareOfNative() public {
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0.01 ether, REFERRER, 300);
        vm.deal(deposit, 1.01 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, REFERRER, 300);
        assertEq(FEE_TO.balance, 0.01 ether);
        assertEq(REFERRER.balance, 0.03 ether);
        assertEq(token.balanceOf(BURN), 0.97 ether);
        assertEq(deposit.balance, 0);
    }

    function test_aReferralIsCappedAndNeedsAReferrer() public {
        uint16 tooHigh = deposits.MAX_REFERRAL_BPS() + 1;
        vm.expectRevert(abi.encodeWithSelector(DepositAddressFactory.ReferralTooHigh.selector, tooHigh));
        deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, REFERRER, tooHigh);
        vm.expectRevert(abi.encodeWithSelector(DepositAddressFactory.ReferralTooHigh.selector, tooHigh));
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0, REFERRER, tooHigh);
        vm.expectRevert(DepositAddressFactory.ZeroAddress.selector);
        deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, address(0), 1);
    }

    function test_aReferrerThatReentersFindsNothingAndOneThatRefusesBlocksTheFlush() public {
        FeeRecipient referrer = new FeeRecipient();
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(referrer), 300);
        vm.deal(deposit, 1.01 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(referrer), 300);
        assertEq(address(referrer).balance, 0.03 ether);
        assertEq(referrer.reentryError(), stdError.arithmeticError);

        referrer.setRefuse(true);
        vm.deal(deposit, 1 ether);
        vm.expectRevert(Errors.FailedCall.selector);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(referrer), 300);
        DepositAddress(payable(deposit)).refund(Protocol.NATIVE);
        assertEq(alice.balance, 1 ether);
    }

    /// @dev Paid before the referral, the fee recipient finds the referral still there, and a flush of it pays it out:
    ///      the outer flush then cannot pay the referral, and reverts.
    function test_aFlushReenteredFromTheFeeRecipientCannotTakeTheReferral() public {
        FeeRecipient recipient = new FeeRecipient();
        address deposit =
            deposits.predict(token, BURN, alice, address(0), address(recipient), 0.01 ether, REFERRER, 300);
        vm.deal(deposit, 1.01 ether);
        vm.expectRevert(abi.encodeWithSelector(Errors.InsufficientBalance.selector, 0, 0.03 ether));
        deposits.flush(token, BURN, alice, address(0), address(recipient), 0.01 ether, REFERRER, 300);
        assertEq(deposit.balance, 1.01 ether);
    }

    function test_initializeRejectsAZeroRegistry() public {
        address impl = _implementation(address(deposits));
        vm.expectRevert(DepositAddressFactory.ZeroAddress.selector);
        new ERC1967Proxy(
            impl, abi.encodeCall(DepositAddressFactory.initialize, (address(this), ITokenRegistry(address(0))))
        );
    }

    function test_aZeroFeeIsNotPaid() public {
        NoZeroTransfers usdc = new NoZeroTransfers();
        ZERC20 zusdc = ZERC20(payable(factory.createToken(address(usdc), "zUSDC", "zUSDC", 6)));
        address deposit = deposits.predict(zusdc, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        deal(address(usdc), deposit, 5e6);
        assertEq(deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 0, address(0), 0), deposit);
        assertEq(zusdc.balanceOf(BURN), 5e6);
        assertEq(usdc.balanceOf(deposit), 0);
        assertEq(usdc.balanceOf(FEE_TO), 0);
    }

    function test_aDeployedCloneFlushesWithoutTheFactory() public {
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        vm.deal(deposit, 1 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);

        vm.deal(deposit, 1 ether);
        vm.prank(bob);
        DepositAddress(payable(deposit)).flush();
        assertEq(token.balanceOf(BURN), 1.98 ether);
        assertEq(FEE_TO.balance, 0.02 ether);
    }

    function test_aFlushReenteredFromTheFeeRecipientFindsNothingLeft() public {
        FeeRecipient recipient = new FeeRecipient();
        vm.deal(
            deposits.predict(token, BURN, alice, address(0), address(recipient), 0.01 ether, address(0), 0), 1 ether
        );
        deposits.flush(token, BURN, alice, address(0), address(recipient), 0.01 ether, address(0), 0);
        assertEq(token.balanceOf(BURN), 0.99 ether);
        assertEq(address(recipient).balance, 0.01 ether);
        assertEq(recipient.reentryError(), stdError.arithmeticError);
    }

    function test_aFeeRecipientRefusingPaymentBlocksTheFlush() public {
        FeeRecipient recipient = new FeeRecipient();
        address deposit =
            deposits.predict(token, BURN, alice, address(0), address(recipient), 0.01 ether, address(0), 0);
        vm.deal(deposit, 1 ether);
        deposits.flush(token, BURN, alice, address(0), address(recipient), 0.01 ether, address(0), 0);

        recipient.setRefuse(true);
        vm.deal(deposit, 1 ether);
        vm.expectRevert(Errors.FailedCall.selector);
        deposits.flush(token, BURN, alice, address(0), address(recipient), 0.01 ether, address(0), 0);
        assertEq(deposit.balance, 1 ether);

        vm.prank(bob);
        DepositAddress(payable(deposit)).refund(Protocol.NATIVE); // what cannot be wrapped goes back
        assertEq(alice.balance, 1 ether);
        assertEq(token.balanceOf(BURN), 0.99 ether);
    }

    function test_aStoppedTokenCannotBeFlushed() public {
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        vm.deal(deposit, 1 ether);
        verifier.pauseToken(1);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.TokenStopped.selector, uint32(1)));
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        assertEq(deposit.balance, 1 ether);
    }

    function test_aRefundOfUnderlyingThatCanBeWrappedFlushesIt() public {
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        vm.deal(deposit, 1 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);

        vm.deal(deposit, 1 ether); // the next deposit, before the relayer flushes it
        vm.prank(bob);
        DepositAddress(payable(deposit)).refund(Protocol.NATIVE);
        assertEq(token.balanceOf(BURN), 1.98 ether);
        assertEq(FEE_TO.balance, 0.02 ether);
        assertEq(alice.balance, 0);

        vm.deal(deposit, 1 ether);
        verifier.pauseToken(1); // a stopped token cannot take it, so it goes back
        vm.prank(bob);
        DepositAddress(payable(deposit)).refund(Protocol.NATIVE);
        assertEq(alice.balance, 1 ether);
        assertEq(token.balanceOf(BURN), 1.98 ether);
    }

    /// @dev Every gas limit up to well past a flush's cost, a step at a time: whatever frame runs out, a refund either
    ///      fails or the flush went through.
    function test_aFlushStarvedOfGasNeverTurnsIntoARefund() public {
        MockToken usdc = new MockToken(6);
        ZERC20 zusdc = ZERC20(payable(factory.createToken(address(usdc), "zUSDC", "zUSDC", 6)));
        address native = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        address erc20 = deposits.predict(zusdc, BURN, alice, address(0), FEE_TO, 1, address(0), 0);
        vm.deal(native, 1 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        deal(address(usdc), erc20, 10);
        deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 1, address(0), 0);
        vm.deal(native, 1 ether);
        deal(address(usdc), erc20, 10);

        for (uint256 gas = 20_000; gas < 300_000; gas += 100) {
            uint256 snapshot = vm.snapshotState();
            (bool ok,) = native.call{gas: gas}(abi.encodeCall(DepositAddress.refund, (Protocol.NATIVE)));
            assertFalse(ok && alice.balance != 0);
            (ok,) = erc20.call{gas: gas}(abi.encodeCall(DepositAddress.refund, (address(usdc))));
            assertFalse(ok && usdc.balanceOf(alice) != 0);
            vm.revertToState(snapshot);
        }
    }

    function test_depositAddressRefundsToTheRefundAddress() public {
        address deposit = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        vm.deal(deposit, 1 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0, address(0), 0);

        // A rage exit mints the refund to the leaf's `from`, i.e. the deposit address.
        vm.prank(address(verifier));
        token.payOut(deposit, 1 ether, false);
        vm.prank(bob); // anyone may trigger; pays only the refund address
        DepositAddress(payable(deposit)).refund(address(token));
        assertEq(token.balanceOf(alice), 1 ether);
        assertEq(token.balanceOf(deposit), 0);

        // underlying too little to wrap
        address small = deposits.predict(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        vm.deal(small, 1 ether);
        deposits.flush(token, BURN, alice, address(0), FEE_TO, 0.01 ether, address(0), 0);
        vm.deal(small, 0.005 ether);
        vm.prank(bob);
        DepositAddress(payable(small)).refund(Protocol.NATIVE);
        assertEq(alice.balance, 0.005 ether);
    }

    function _refundSignature(uint256 key, address deposit, address asset, address to, uint256 deadline)
        private
        view
        returns (bytes memory)
    {
        bytes32 digest = keccak256(
            abi.encodePacked(
                "\x19Ethereum Signed Message:\n32", keccak256(abi.encode(block.chainid, deposit, asset, to, deadline))
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, digest);
        return abi.encodePacked(r, s, v);
    }

    function test_aSignedRefundGoesWhereTheSignerSays() public {
        (address signer, uint256 key) = makeAddrAndKey("refund signer");
        address deposit = deposits.predict(token, BURN, address(0), signer, FEE_TO, 0, address(0), 0);
        vm.deal(deposit, 1 ether);
        deposits.flush(token, BURN, address(0), signer, FEE_TO, 0, address(0), 0);
        vm.prank(address(verifier)); // a rage exit
        token.payOut(deposit, 1 ether, false);

        // no fixed destination, so nobody can push the refund out unasked
        vm.expectRevert(DepositAddress.NotRefundable.selector);
        DepositAddress(payable(deposit)).refund(address(token));

        uint256 deadline = block.timestamp + 1 hours;
        bytes memory sig = _refundSignature(key, deposit, address(token), bob, deadline);
        // signed for bob: sent to anyone else, it recovers another signer
        vm.expectPartialRevert(DepositAddress.WrongSigner.selector);
        DepositAddress(payable(deposit)).refundTo(address(token), carol, deadline, sig);

        vm.prank(carol); // anyone may send it, and pays the gas
        DepositAddress(payable(deposit)).refundTo(address(token), bob, deadline, sig);
        assertEq(token.balanceOf(bob), 1 ether);
        assertEq(token.balanceOf(deposit), 0);

        // underlying a flush can take is flushed, signed or not
        vm.deal(deposit, 1 ether);
        DepositAddress(payable(deposit))
            .refundTo(Protocol.NATIVE, bob, deadline, _refundSignature(key, deposit, Protocol.NATIVE, bob, deadline));
        assertEq(token.balanceOf(BURN), 2 ether);

        vm.warp(deadline + 1);
        vm.expectRevert(abi.encodeWithSelector(DepositAddress.Expired.selector, deadline));
        DepositAddress(payable(deposit)).refundTo(address(token), bob, deadline, sig);
    }

    function test_refundForwardsAnyErc20() public {
        MockToken usdc = new MockToken(6);
        ZERC20 zusdc = ZERC20(payable(factory.createToken(address(usdc), "zUSDC", "zUSDC", 6)));
        address deposit = deposits.predict(zusdc, BURN, alice, address(0), FEE_TO, 1e6, address(0), 0);
        deal(address(usdc), deposit, 3e6);
        deposits.flush(zusdc, BURN, alice, address(0), FEE_TO, 1e6, address(0), 0);

        MockToken stray = new MockToken(18); // a wrong token sent to the address
        deal(address(stray), deposit, 7);
        vm.prank(alice);
        DepositAddress(payable(deposit)).refund(address(stray));
        assertEq(stray.balanceOf(alice), 7);
        assertEq(stray.balanceOf(deposit), 0);
    }

    function test_depositAddressRejectsUnknownTokensAndZeroAddresses() public {
        ZERC20 fake = ZERC20(payable(address(new ZERC20())));
        vm.expectRevert(abi.encodeWithSelector(DepositAddressFactory.UnknownToken.selector, address(fake)));
        deposits.predict(fake, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        vm.expectRevert(abi.encodeWithSelector(DepositAddressFactory.UnknownToken.selector, address(fake)));
        deposits.flush(fake, BURN, alice, address(0), FEE_TO, 0, address(0), 0);
        vm.expectRevert(DepositAddressFactory.ZeroAddress.selector);
        deposits.predict(token, address(0), alice, address(0), FEE_TO, 0, address(0), 0);
        vm.expectRevert(DepositAddressFactory.ZeroAddress.selector);
        deposits.flush(token, BURN, address(0), address(0), FEE_TO, 0, address(0), 0);
        vm.expectRevert(DepositAddressFactory.ZeroAddress.selector); // a refund address and a signer both
        deposits.predict(token, BURN, alice, bob, FEE_TO, 0, address(0), 0);
        vm.expectRevert(DepositAddressFactory.ZeroAddress.selector); // whatever the fee
        deposits.predict(token, BURN, alice, address(0), address(0), 0, address(0), 0);
    }
}
