// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {CommonBase} from "forge-std/Base.sol";
import {StdUtils} from "forge-std/StdUtils.sol";
import {IERC20Errors} from "@openzeppelin/contracts/interfaces/draft-IERC6093.sol";
import {BeaconProxy} from "@openzeppelin/contracts/proxy/beacon/BeaconProxy.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {PausableUpgradeable} from "@openzeppelin/contracts-upgradeable/utils/PausableUpgradeable.sol";
import {
    ERC20PermitUpgradeable
} from "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/ERC20PermitUpgradeable.sol";
import {
    ERC3009Upgradeable
} from "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/draft-ERC3009Upgradeable.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {IBlocklist} from "../src/interfaces/IBlocklist.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {MockToken} from "./mocks/MockToken.sol";
import {ProtocolTest} from "./utils/ProtocolTest.sol";

/// @dev Moves `shortBy` less than asked on every transfer, as a fee-on-transfer or rebasing token can.
contract ShortToken is MockToken {
    uint256 public shortBy;

    constructor() MockToken(6) {}

    function setShortBy(uint256 amount) external {
        shortBy = amount;
    }

    function transfer(address to, uint256 value) public override returns (bool) {
        _transfer(msg.sender, to, value - shortBy);
        return true;
    }

    function transferFrom(address from, address to, uint256 value) public override returns (bool) {
        _spendAllowance(from, msg.sender, value);
        _transfer(from, to, value - shortBy);
        return true;
    }
}

/// @dev Has no way to take the native asset.
contract NoReceive {}

/// @dev Calls back into the token when paid the native asset, and keeps what that call reverted with.
contract ReenteringReceiver {
    ZERC20 private immutable TOKEN;
    bytes public reentryError;

    constructor(ZERC20 token_) {
        TOKEN = token_;
    }

    receive() external payable {
        try TOKEN.transfer(address(1), 0) {}
        catch (bytes memory err) {
            reentryError = err;
        }
    }
}

contract ZERC20Test is ProtocolTest {
    bytes32 constant TRANSFER_WITH_AUTHORIZATION_TYPEHASH = keccak256(
        "TransferWithAuthorization(address from,address to,uint256 value,uint256 validAfter,uint256 validBefore,"
        "bytes32 nonce)"
    );
    bytes32 constant RECEIVE_WITH_AUTHORIZATION_TYPEHASH = keccak256(
        "ReceiveWithAuthorization(address from,address to,uint256 value,uint256 validAfter,uint256 validBefore,"
        "bytes32 nonce)"
    );
    bytes32 constant CANCEL_AUTHORIZATION_TYPEHASH = keccak256("CancelAuthorization(address authorizer,bytes32 nonce)");

    function _list(MockToken underlying) internal returns (ZERC20) {
        return ZERC20(payable(factory.createToken(address(underlying), "zMock", "zMCK", underlying.decimals())));
    }

    function _leaf(address from, address to, uint256 amount) internal pure returns (uint256[4] memory) {
        return [Protocol.encode(Protocol.TRANSFER_TAG, 1), uint256(uint160(from)), uint256(uint160(to)), amount];
    }

    // ---- initialization ------------------------------------------------------------------------

    function test_viewsReturnWhatTheFactoryInitialized() public view {
        assertEq(token.name(), "zEther");
        assertEq(token.symbol(), "zETH");
        assertEq(token.decimals(), 18);
        assertEq(token.tokenId(), 1);
        assertEq(token.underlyingAsset(), Protocol.NATIVE);
        assertEq(address(token.ledger()), address(ledger));
        assertEq(token.verifier(), address(verifier));
        assertEq(address(token.blocklist()), address(blocklist));
        assertEq(token.factory(), address(factory));
    }

    function test_initializeRejectsZeroDependencies() public {
        address beacon = address(factory.tokenBeacon());
        CommitmentLedger[3] memory ledgers = [ledger, CommitmentLedger(address(0)), ledger];
        address[3] memory verifiers = [address(verifier), address(verifier), address(0)];
        IBlocklist[3] memory lists = [IBlocklist(address(0)), blocklist, blocklist];
        for (uint256 i; i < 3; ++i) {
            vm.expectRevert(ZERC20.ZeroAddress.selector);
            new BeaconProxy(
                beacon,
                abi.encodeCall(
                    ZERC20.initialize, ("z", "z", 18, 9, Protocol.NATIVE, ledgers[i], verifiers[i], lists[i])
                )
            );
        }
    }

    function test_directNativeTransfersAreRefused() public {
        vm.deal(alice, 1 ether);
        vm.prank(alice);
        (bool ok, bytes memory err) = address(token).call{value: 1 ether}("");
        assertFalse(ok);
        assertEq(err, abi.encodeWithSelector(ZERC20.DirectNativeTransfer.selector));
    }

    // ---- wrap / unwrap -------------------------------------------------------------------------

    function test_wrapUnwrapAndLedger() public {
        _wrap(alice, 3 ether, bob); // only the alice -> bob forward is a leaf
        assertEq(ledger.nextIndex(), 1);
        assertEq(token.balanceOf(bob), 3 ether);
        vm.prank(bob);
        token.unwrap(1 ether, bob);
        assertEq(bob.balance, 1 ether);
        assertEq(token.totalSupply(), 2 ether);
        assertEq(ledger.nextIndex(), 1); // burns are not leaves
    }

    function test_wrapForwardsFromTheCallerSoTheLeafHasARealSender() public {
        vm.deal(alice, 3 ether);
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(0, _leaf(alice, bob, 2 ether));
        vm.expectEmit(address(token));
        emit ZERC20.Wrapped(alice, bob, 2 ether);
        vm.prank(alice);
        token.wrap{value: 2 ether}(2 ether, bob);

        vm.prank(alice);
        token.wrap{value: 1 ether}(1 ether, alice); // a mint alone
        assertEq(ledger.nextIndex(), 1);
        assertEq(token.balanceOf(alice), 1 ether);
        assertEq(address(token).balance, 3 ether);
    }

    function test_wrapRejectsZeroReceiverAndAmount() public {
        vm.expectRevert(ZERC20.ZeroAddress.selector);
        token.wrap(0, address(0));
        vm.expectRevert(ZERC20.ZeroAmount.selector);
        token.wrap(0, alice);
    }

    function test_wrapTakesExactlyTheNativeAmount() public {
        vm.deal(alice, 3 ether);
        vm.startPrank(alice);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.InvalidNativeValue.selector, 2 ether, 1 ether));
        token.wrap{value: 1 ether}(2 ether, alice);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.InvalidNativeValue.selector, 1 ether, 2 ether));
        token.wrap{value: 2 ether}(1 ether, alice);
        vm.stopPrank();
    }

    function test_wrapOfAnErc20TakesNoNativeValue() public {
        MockToken usdc = new MockToken(6);
        ZERC20 zusdc = _list(usdc);
        deal(address(usdc), alice, 5e6);
        vm.deal(alice, 1);
        vm.startPrank(alice);
        usdc.approve(address(zusdc), 5e6);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.InvalidNativeValue.selector, 0, 1));
        zusdc.wrap{value: 1}(5e6, alice);
        zusdc.wrap(5e6, alice);
        vm.stopPrank();
        assertEq(zusdc.balanceOf(alice), 5e6);
        assertEq(usdc.balanceOf(address(zusdc)), 5e6);
    }

    function test_wrapAndUnwrapRefuseAnUnderlyingThatMovesShort() public {
        ShortToken short = new ShortToken();
        ZERC20 zshort = _list(short);
        deal(address(short), alice, 100);
        vm.startPrank(alice);
        short.approve(address(zshort), 100);

        short.setShortBy(1); // arrives short
        vm.expectRevert(abi.encodeWithSelector(ZERC20.InvalidUnderlyingDelta.selector, 10, 9));
        zshort.wrap(10, alice);

        short.setShortBy(0);
        zshort.wrap(10, alice);
        short.setShortBy(1); // leaves short
        vm.expectRevert(abi.encodeWithSelector(ZERC20.InvalidUnderlyingDelta.selector, 10, 9));
        zshort.unwrap(10, alice);
        vm.stopPrank();
    }

    function test_unwrapReleasesTheErc20Underlying() public {
        MockToken usdc = new MockToken(6);
        ZERC20 zusdc = _list(usdc);
        deal(address(usdc), alice, 5e6);
        vm.startPrank(alice);
        usdc.approve(address(zusdc), 5e6);
        zusdc.wrap(5e6, alice);
        vm.expectEmit(address(zusdc));
        emit ZERC20.Unwrapped(alice, bob, 2e6);
        zusdc.unwrap(2e6, bob);
        vm.stopPrank();
        assertEq(usdc.balanceOf(bob), 2e6);
        assertEq(zusdc.balanceOf(alice), 3e6);
        assertEq(zusdc.totalSupply(), 3e6);
        assertEq(ledger.nextIndex(), 0);
    }

    function test_unwrapRejectsZeroArgumentsAndOverdrafts() public {
        _wrap(alice, 1 ether, alice);
        vm.startPrank(alice);
        vm.expectRevert(ZERC20.ZeroAddress.selector);
        token.unwrap(1, address(0));
        vm.expectRevert(ZERC20.ZeroAmount.selector);
        token.unwrap(0, alice);
        vm.expectRevert(
            abi.encodeWithSelector(IERC20Errors.ERC20InsufficientBalance.selector, alice, 1 ether, 1 ether + 1)
        );
        token.unwrap(1 ether + 1, alice);
        vm.stopPrank();
    }

    function test_unwrapToAnAccountRefusingTheNativeAssetReverts() public {
        _wrap(alice, 1 ether, alice);
        address sink = address(new NoReceive());
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.NativeTransferFailed.selector, sink, 1 ether));
        token.unwrap(1 ether, sink);
    }

    function test_aNativeRecipientCannotReenterTheToken() public {
        _wrap(alice, 1 ether, alice);
        ReenteringReceiver receiver = new ReenteringReceiver(token);
        vm.prank(alice);
        token.unwrap(1 ether, address(receiver));
        assertEq(address(receiver).balance, 1 ether);
        assertEq(
            receiver.reentryError(),
            abi.encodeWithSelector(ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector)
        );
    }

    // ---- transfers -----------------------------------------------------------------------------

    function test_aZeroTransferCommitsNothing() public {
        vm.prank(alice);
        assertTrue(token.transfer(bob, 0));
        assertEq(ledger.nextIndex(), 0);
    }

    function test_transferFromChecksTheSpenderTooAsItPicksTheRecipient() public {
        _wrap(alice, 1 ether, alice);
        vm.prank(alice);
        token.approve(bob, 1 ether);

        _setBlocked(bob, true);
        vm.prank(bob);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.BlockedAddress.selector, bob));
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        token.transferFrom(alice, carol, 1);
        _setBlocked(bob, false);

        _setBlocked(carol, true);
        vm.prank(bob);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.BlockedAddress.selector, carol));
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        token.transferFrom(alice, carol, 1);
        _setBlocked(carol, false);

        _setBlocked(alice, true);
        vm.prank(bob);
        vm.expectRevert(abi.encodeWithSelector(ZERC20.BlockedAddress.selector, alice));
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        token.transferFrom(alice, carol, 1);
        _setBlocked(alice, false);

        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(0, _leaf(alice, carol, 1)); // the leaf is the owner's, not the spender's
        vm.prank(bob);
        assertTrue(token.transferFrom(alice, carol, 1));
    }

    function test_blocklistStopsTransfersWrapsAndWithdrawals() public {
        _wrap(alice, 2 ether, alice);
        _setBlocked(bob, true);
        bytes memory blocked = abi.encodeWithSelector(ZERC20.BlockedAddress.selector, bob);

        vm.deal(alice, 1 ether);
        vm.startPrank(alice);
        vm.expectRevert(blocked);
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        token.transfer(bob, 1 ether);
        vm.expectRevert(blocked);
        token.wrap{value: 1 ether}(1 ether, bob);
        vm.expectRevert(blocked);
        token.unwrap(1 ether, bob);
        vm.stopPrank();
        vm.expectRevert(blocked); // withdrawal to a blocked recipient
        verifier.transact(_signals(1 ether, bob, 30));
        vm.expectRevert(blocked); // also as the underlying
        verifier.transact(_unwrapSignals(1 ether, bob, 30));

        // a blocked holder can neither send, unwrap nor wrap, since a wrap mints to the caller first
        _setBlocked(alice, true);
        blocked = abi.encodeWithSelector(ZERC20.BlockedAddress.selector, alice);
        vm.startPrank(alice);
        vm.expectRevert(blocked);
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        token.transfer(carol, 1);
        vm.expectRevert(blocked);
        token.unwrap(1, carol);
        vm.expectRevert(blocked);
        token.wrap{value: 1}(1, carol);
        vm.stopPrank();

        address[] memory both = new address[](2);
        (both[0], both[1]) = (alice, bob);
        blocklist.setBlocked(both, false);
        vm.prank(alice);
        assertTrue(token.transfer(bob, 1 ether));
        assertEq(token.balanceOf(bob), 1 ether);
    }

    function test_amountsReachingTheBoundAreRefused() public {
        vm.startPrank(address(verifier));
        vm.expectRevert(abi.encodeWithSelector(ZERC20.InvalidAmount.selector, Protocol.AMOUNT_BOUND));
        token.payOut(alice, Protocol.AMOUNT_BOUND, false);
        token.payOut(alice, Protocol.AMOUNT_BOUND - 1, false);
        vm.stopPrank();
        assertEq(token.balanceOf(alice), Protocol.AMOUNT_BOUND - 1);
    }

    // ---- Verifier entry points -----------------------------------------------------------------

    function test_commitNoteIsTheVerifiersAndStaysInTheField() public {
        vm.expectRevert(abi.encodeWithSelector(ZERC20.Unauthorized.selector, address(this)));
        token.commitNote(7);

        vm.startPrank(address(verifier));
        vm.expectRevert(abi.encodeWithSelector(ZERC20.InvalidNoteHash.selector, Protocol.FIELD_MODULUS));
        token.commitNote(Protocol.FIELD_MODULUS);
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(0, [Protocol.encode(Protocol.NOTE_HASH_TAG, 1), 7, 0, 0]);
        assertEq(token.commitNote(7), 0);
        assertEq(token.commitNote(8), 1);
        vm.stopPrank();
    }

    function test_payOutIsTheVerifiersAndMintsWithoutALeaf() public {
        vm.expectRevert(abi.encodeWithSelector(ZERC20.Unauthorized.selector, address(this)));
        token.payOut(bob, 1, false);

        vm.startPrank(address(verifier));
        vm.expectRevert(ZERC20.ZeroAddress.selector);
        token.payOut(address(0), 1, false);
        vm.expectRevert(ZERC20.ZeroAmount.selector);
        token.payOut(bob, 0, true);
        token.payOut(bob, 2 ether, false);
        vm.stopPrank();
        assertEq(token.balanceOf(bob), 2 ether);
        assertEq(token.totalSupply(), 2 ether);
        assertEq(ledger.nextIndex(), 0);
    }

    // ---- pause ---------------------------------------------------------------------------------

    function test_pauseStopsEveryBalanceChange() public {
        verifier.setFee(1, carol, _flatFee(100));
        verifier.transact(_signals(2 ether, bob, 50));
        vm.deal(alice, 1 ether);
        bytes memory stopped = abi.encodeWithSelector(ZERC20.TokenStopped.selector, uint32(1));

        verifier.pause();
        vm.expectRevert(PausableUpgradeable.EnforcedPause.selector);
        verifier.transact(_signals(1 ether, bob, 60));
        vm.expectRevert(stopped);
        verifier.claimFees(1, carol);
        vm.startPrank(bob);
        vm.expectRevert(stopped);
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        token.transfer(alice, 1);
        vm.expectRevert(stopped);
        token.unwrap(1, bob);
        vm.stopPrank();
        vm.prank(alice);
        vm.expectRevert(stopped);
        token.wrap{value: 1 ether}(1 ether, alice);
        vm.prank(address(verifier)); // the token stops a release by itself too
        vm.expectRevert(stopped);
        token.payOut(bob, 1, true);

        verifier.unpause();
        verifier.claimFees(1, carol);
        assertEq(token.balanceOf(carol), 0.02 ether);
        vm.prank(bob);
        assertTrue(token.transfer(alice, 1));
        verifier.transact(_signals(1 ether, bob, 60));

        // a token's own pause stops its fee claims too
        verifier.pauseToken(1);
        vm.expectRevert(stopped);
        verifier.claimFees(1, carol);
        verifier.unpauseToken(1);
        verifier.claimFees(1, carol);
        assertEq(token.balanceOf(carol), 0.03 ether);
    }

    // ---- signatures ----------------------------------------------------------------------------

    function _permitDigest(string memory name, address owner) internal view returns (bytes32) {
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256(bytes(name)),
                keccak256("1"),
                block.chainid,
                address(token)
            )
        );
        bytes32 structHash = keccak256(
            abi.encode(
                keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"),
                owner,
                bob,
                1 ether,
                0,
                block.timestamp
            )
        );
        return keccak256(abi.encodePacked("\x19\x01", domain, structHash));
    }

    function test_permitSignsOverTheCurrentName() public {
        (address owner, uint256 key) = makeAddrAndKey("owner");
        factory.setTokenMetadata(1, "zWrapped Ether", "zWETH");

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, _permitDigest("zEther", owner));
        vm.expectPartialRevert(ERC20PermitUpgradeable.ERC2612InvalidSigner.selector); // signed before the rename
        token.permit(owner, bob, 1 ether, block.timestamp, v, r, s);

        (v, r, s) = vm.sign(key, _permitDigest("zWrapped Ether", owner));
        token.permit(owner, bob, 1 ether, block.timestamp, v, r, s);
        assertEq(token.allowance(owner, bob), 1 ether);
        assertEq(token.nonces(owner), 1);
    }

    function test_eip712DomainFollowsTheName() public {
        (, string memory name, string memory version, uint256 chainId, address verifyingContract,,) =
            token.eip712Domain();
        assertEq(name, "zEther");
        assertEq(version, "1");
        assertEq(chainId, block.chainid);
        assertEq(verifyingContract, address(token));

        factory.setTokenMetadata(1, "zWrapped Ether", "zWETH");
        (, name,,,,,) = token.eip712Domain();
        assertEq(name, "zWrapped Ether");
    }

    function _authorize(
        bytes32 typehash,
        uint256 key,
        address from,
        address to,
        uint256 value,
        uint256 validBefore,
        bytes32 nonce
    ) internal view returns (uint8 v, bytes32 r, bytes32 s) {
        bytes32 structHash = keccak256(abi.encode(typehash, from, to, value, 0, validBefore, nonce));
        return vm.sign(key, keccak256(abi.encodePacked("\x19\x01", token.DOMAIN_SEPARATOR(), structHash)));
    }

    function test_transferWithAuthorizationPaysABurnAddress() public {
        (address payer, uint256 key) = makeAddrAndKey("payer");
        address burn = address(0xB0E);
        _wrap(payer, 1 ether, payer); // a mint, not a leaf

        bytes32 nonce = keccak256("x402"); // x402 clients sign a random 32-byte nonce
        uint256 before = block.timestamp + 60;
        (uint8 v, bytes32 r, bytes32 s) =
            _authorize(TRANSFER_WITH_AUTHORIZATION_TYPEHASH, key, payer, burn, 0.1 ether, before, nonce);

        // The leaf's `from` is the payer, not the relaying facilitator.
        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(0, _leaf(payer, burn, 0.1 ether));
        vm.prank(bob); // the facilitator
        token.transferWithAuthorization(payer, burn, 0.1 ether, 0, before, nonce, v, r, s);
        assertEq(token.balanceOf(burn), 0.1 ether);
        assertTrue(token.authorizationState(payer, nonce));

        vm.expectRevert(abi.encodeWithSelector(ERC3009Upgradeable.ERC3009UsedAuthorization.selector, payer, nonce));
        token.transferWithAuthorization(payer, burn, 0.1 ether, 0, before, nonce, v, r, s);
    }

    function test_receiveWithAuthorizationIsCalledByItsRecipient() public {
        (address payer, uint256 key) = makeAddrAndKey("payer");
        _wrap(payer, 1 ether, payer);
        bytes32 nonce = keccak256("receive");
        uint256 before = block.timestamp + 60;
        (uint8 v, bytes32 r, bytes32 s) =
            _authorize(RECEIVE_WITH_AUTHORIZATION_TYPEHASH, key, payer, bob, 0.1 ether, before, nonce);

        vm.prank(alice); // a front-runner cannot take it over
        vm.expectRevert(abi.encodeWithSelector(IERC20Errors.ERC20InvalidReceiver.selector, bob));
        token.receiveWithAuthorization(payer, bob, 0.1 ether, 0, before, nonce, v, r, s);

        vm.expectEmit(address(ledger));
        emit CommitmentLedger.Committed(0, _leaf(payer, bob, 0.1 ether));
        vm.prank(bob);
        token.receiveWithAuthorization(payer, bob, 0.1 ether, 0, before, nonce, v, r, s);
        assertEq(token.balanceOf(bob), 0.1 ether);
    }

    function test_authorizationsHonourTheirWindowAndCancellation() public {
        (address payer, uint256 key) = makeAddrAndKey("payer");
        _wrap(payer, 1 ether, payer);
        vm.warp(1000);
        bytes32 nonce = keccak256("window");
        (uint8 v, bytes32 r, bytes32 s) =
            _authorize(TRANSFER_WITH_AUTHORIZATION_TYPEHASH, key, payer, bob, 1, 1000, nonce);
        vm.expectRevert(abi.encodeWithSelector(ERC3009Upgradeable.ERC3009InvalidAuthorizationTime.selector, 0, 1000));
        token.transferWithAuthorization(payer, bob, 1, 0, 1000, nonce, v, r, s); // validBefore is exclusive

        (v, r, s) = _authorize(TRANSFER_WITH_AUTHORIZATION_TYPEHASH, key, payer, bob, 1, 1001, nonce);
        bytes32 cancel = keccak256(abi.encode(CANCEL_AUTHORIZATION_TYPEHASH, payer, nonce));
        (uint8 cv, bytes32 cr, bytes32 cs) =
            vm.sign(key, keccak256(abi.encodePacked("\x19\x01", token.DOMAIN_SEPARATOR(), cancel)));
        token.cancelAuthorization(payer, nonce, cv, cr, cs);
        assertTrue(token.authorizationState(payer, nonce));
        vm.expectRevert(abi.encodeWithSelector(ERC3009Upgradeable.ERC3009UsedAuthorization.selector, payer, nonce));
        token.transferWithAuthorization(payer, bob, 1, 0, 1001, nonce, v, r, s);
    }

    function test_authorizationsCheckThePayerAndRecipientButNotTheRelayer() public {
        (address payer, uint256 key) = makeAddrAndKey("payer");
        _wrap(payer, 1 ether, payer);
        uint256 before = block.timestamp + 60;

        _setBlocked(bob, true); // the relayer only carries what the payer signed
        (uint8 v, bytes32 r, bytes32 s) =
            _authorize(TRANSFER_WITH_AUTHORIZATION_TYPEHASH, key, payer, carol, 1, before, "a");
        vm.prank(bob);
        token.transferWithAuthorization(payer, carol, 1, 0, before, "a", v, r, s);
        assertEq(token.balanceOf(carol), 1);

        (v, r, s) = _authorize(TRANSFER_WITH_AUTHORIZATION_TYPEHASH, key, payer, bob, 1, before, "b");
        vm.expectRevert(abi.encodeWithSelector(ZERC20.BlockedAddress.selector, bob));
        token.transferWithAuthorization(payer, bob, 1, 0, before, "b", v, r, s);

        _setBlocked(payer, true);
        (v, r, s) = _authorize(TRANSFER_WITH_AUTHORIZATION_TYPEHASH, key, payer, carol, 1, before, "c");
        vm.expectRevert(abi.encodeWithSelector(ZERC20.BlockedAddress.selector, payer));
        token.transferWithAuthorization(payer, carol, 1, 0, before, "c", v, r, s);
    }
}

/// @dev Wraps, unwraps and transfers zETH among three accounts, and keeps the ledger leaves those calls must add.
contract WrapHandler is CommonBase, StdUtils {
    ZERC20 private immutable TOKEN;
    address[3] private actors = [address(0x1001), address(0x1002), address(0x1003)];
    uint256 public commits;
    uint256 public chain;

    constructor(ZERC20 token_) {
        TOKEN = token_;
    }

    function wrap(uint256 fromSeed, uint256 toSeed, uint256 amount) external {
        (address from, address to) = (actors[fromSeed % 3], actors[toSeed % 3]);
        amount = bound(amount, 1, 100 ether);
        vm.deal(from, from.balance + amount);
        vm.prank(from);
        TOKEN.wrap{value: amount}(amount, to);
        if (to != from) _record(from, to, amount);
    }

    function unwrap(uint256 fromSeed, uint256 toSeed, uint256 amount) external {
        address from = actors[fromSeed % 3];
        uint256 balance = TOKEN.balanceOf(from);
        if (balance == 0) return;
        vm.prank(from);
        TOKEN.unwrap(bound(amount, 1, balance), actors[toSeed % 3]);
    }

    function transfer(uint256 fromSeed, uint256 toSeed, uint256 amount) external {
        // never to itself
        (address from, address to) = (actors[fromSeed % 3], actors[(fromSeed % 3 + 1 + toSeed % 2) % 3]);
        amount = bound(amount, 0, TOKEN.balanceOf(from));
        vm.prank(from);
        // forge-lint: disable-next-line(erc20-unchecked-transfer)
        TOKEN.transfer(to, amount);
        if (amount != 0) _record(from, to, amount);
    }

    function _record(address from, address to, uint256 amount) private {
        ++commits;
        bytes memory leaf = abi.encodePacked(
            chain, Protocol.encode(Protocol.TRANSFER_TAG, 1), uint256(uint160(from)), uint256(uint160(to)), amount
        );
        chain = uint256(sha256(leaf)) & Protocol.HASH_CHAIN_MASK;
    }
}

contract ZERC20InvariantTest is ProtocolTest {
    WrapHandler handler;

    function setUp() public override {
        super.setUp();
        handler = new WrapHandler(token);
        targetContract(address(handler));
        bytes4[] memory selectors = new bytes4[](3);
        selectors[0] = WrapHandler.wrap.selector;
        selectors[1] = WrapHandler.unwrap.selector;
        selectors[2] = WrapHandler.transfer.selector;
        targetSelector(FuzzSelector({addr: address(handler), selectors: selectors}));
    }

    /// forge-config: default.invariant.runs = 64
    /// forge-config: default.invariant.depth = 64
    /// forge-config: default.invariant.fail-on-revert = true
    function invariant_theNativeReserveBacksTheSupply() public view {
        assertEq(address(token).balance, token.totalSupply());
    }

    /// forge-config: default.invariant.runs = 64
    /// forge-config: default.invariant.depth = 64
    /// forge-config: default.invariant.fail-on-revert = true
    function invariant_theLedgerHoldsEveryTransferInOrder() public view {
        assertEq(ledger.nextIndex(), handler.commits());
        assertEq(ledger.hashChain(), handler.chain());
    }
}
