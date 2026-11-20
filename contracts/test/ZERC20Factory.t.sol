// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {ERC1967Proxy} from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol";
import {UpgradeableBeacon} from "@openzeppelin/contracts/proxy/beacon/UpgradeableBeacon.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {Verifier} from "../src/Verifier.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {ZERC20Factory} from "../src/ZERC20Factory.sol";
import {IRootDeciderVerifier} from "../src/interfaces/INovaDeciderVerifier.sol";
import {ITokenRegistry} from "../src/interfaces/ITokenRegistry.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {MockToken} from "./mocks/MockToken.sol";
import {ProtocolTest} from "./utils/ProtocolTest.sol";

contract NoDecimals {}

contract OversizedDecimals {
    function decimals() external pure returns (uint256) {
        return 300;
    }
}

contract ZERC20FactoryTest is ProtocolTest {
    function _proxy(address implementation, bytes memory initData) internal returns (address) {
        return address(new ERC1967Proxy(implementation, initData));
    }

    function test_createTokenNumbersTokensAndInitializesThem() public {
        MockToken usdc = new MockToken(6);
        address predicted = vm.computeCreateAddress(address(factory), vm.getNonce(address(factory)));
        vm.expectEmit(address(factory));
        emit ZERC20Factory.TokenCreated(2, predicted, address(usdc), "zUSDC", "zUSDC", 6);
        ZERC20 zusdc = ZERC20(payable(factory.createToken(address(usdc), "zUSDC", "zUSDC", 6)));

        assertEq(address(zusdc), predicted);
        assertEq(factory.tokenCount(), 2);
        assertEq(factory.tokenById(2), address(zusdc));
        assertEq(factory.tokenIdOf(address(usdc)), 2);
        assertEq(factory.tokenIdOf(Protocol.NATIVE), 1);
        assertEq(factory.tokenById(3), address(0));
        assertEq(zusdc.tokenId(), 2);
        assertEq(zusdc.underlyingAsset(), address(usdc));
        assertEq(address(zusdc.ledger()), address(factory.ledger()));
        assertEq(zusdc.verifier(), factory.verifier());
        assertEq(address(zusdc.blocklist()), address(factory.blocklist()));
        assertEq(zusdc.factory(), address(factory));
    }

    function test_onlyTheOwnerCreatesTokensOncePerUnderlying() public {
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        factory.createToken(address(0xBEEF), "Foo", "FOO", 6);
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.TokenExists.selector, Protocol.NATIVE));
        factory.createToken(Protocol.NATIVE, "zEther", "zETH", 18);
    }

    function test_createTokenRejectsZeroUnderlyingAndEmptyMetadata() public {
        address usdc = address(new MockToken(6));
        vm.expectRevert(ZERC20Factory.ZeroAddress.selector);
        factory.createToken(address(0), "zX", "zX", 18);
        vm.expectRevert(ZERC20Factory.EmptyMetadata.selector);
        factory.createToken(usdc, "", "zUSDC", 6);
        vm.expectRevert(ZERC20Factory.EmptyMetadata.selector);
        factory.createToken(usdc, "zUSDC", "", 6);
    }

    function test_createTokenEnforcesUnderlyingDecimals() public {
        // native asset must be 18 (decimals are checked before the duplicate check)
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.DecimalsMismatch.selector, 18, 6));
        factory.createToken(Protocol.NATIVE, "zEther", "zETH", 6);

        address usdc = address(new MockToken(6));
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.DecimalsMismatch.selector, 6, 18));
        factory.createToken(usdc, "zUSDC", "zUSDC", 18);
        ZERC20 z = ZERC20(payable(factory.createToken(usdc, "zUSDC", "zUSDC", 6)));
        assertEq(z.decimals(), 6);

        // decimals() is optional in ERC-20: without it the owner's value stands
        ZERC20 n = ZERC20(payable(factory.createToken(address(new NoDecimals()), "zN", "zN", 9)));
        assertEq(n.decimals(), 9);

        address oversized = address(new OversizedDecimals());
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.InvalidUnderlyingDecimals.selector, oversized));
        factory.createToken(oversized, "zO", "zO", 18);

        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.UnderlyingHasNoCode.selector, address(0xBEEF)));
        factory.createToken(address(0xBEEF), "zB", "zB", 18);
    }

    function test_ownerUpdatesTokenMetadata() public {
        _wrap(alice, 1 ether, alice);
        assertEq(token.name(), "zEther");

        vm.expectEmit(address(token));
        emit ZERC20.MetadataUpdated("zWrapped Ether", "zWETH");
        vm.expectEmit(address(factory));
        emit ZERC20Factory.TokenMetadataUpdated(1, "zWrapped Ether", "zWETH");
        factory.setTokenMetadata(1, "zWrapped Ether", "zWETH");
        assertEq(token.name(), "zWrapped Ether");
        assertEq(token.symbol(), "zWETH");
        assertEq(token.decimals(), 18);
        assertEq(token.balanceOf(alice), 1 ether);

        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        factory.setTokenMetadata(1, "x", "x");
        vm.expectRevert(abi.encodeWithSelector(ZERC20.Unauthorized.selector, address(this)));
        token.setMetadata("x", "x"); // the token accepts metadata only from its factory
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.UnknownToken.selector, 99));
        factory.setTokenMetadata(99, "x", "x");
        vm.expectRevert(ZERC20Factory.EmptyMetadata.selector);
        factory.setTokenMetadata(1, "", "x");
        vm.expectRevert(ZERC20Factory.EmptyMetadata.selector);
        factory.setTokenMetadata(1, "x", "");

        factory.upgradeTokenBeacon(address(new ZERC20())); // survives an implementation upgrade
        assertEq(token.symbol(), "zWETH");
    }

    function test_tokenBeaconUpgradesEveryTokenAtOnce() public {
        _wrap(alice, 1 ether, alice);
        ZERC20 other = ZERC20(payable(factory.createToken(address(new MockToken(6)), "Foo", "FOO", 6)));
        UpgradeableBeacon beacon = factory.tokenBeacon();
        assertEq(beacon.owner(), address(factory));
        assertEq(beacon.implementation(), tokenImpl);

        address newImpl = address(new ZERC20());
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, alice));
        factory.upgradeTokenBeacon(newImpl);
        vm.expectEmit(address(factory));
        emit ZERC20Factory.TokenBeaconUpgraded(newImpl);
        factory.upgradeTokenBeacon(newImpl);

        assertEq(beacon.implementation(), newImpl);
        assertEq(token.balanceOf(alice), 1 ether); // balances and config survive
        assertEq(token.tokenId(), 1);
        assertEq(other.tokenId(), 2);
        assertEq(other.decimals(), 6);

        vm.expectRevert(abi.encodeWithSelector(UpgradeableBeacon.BeaconInvalidImplementation.selector, address(0xBEEF)));
        factory.upgradeTokenBeacon(address(0xBEEF));
    }

    function test_ownershipTransfersInTwoSteps() public {
        factory.transferOwnership(alice);
        assertEq(factory.owner(), address(this)); // not effective until accepted
        assertEq(factory.pendingOwner(), alice);
        vm.prank(bob);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, bob));
        factory.acceptOwnership();
        vm.prank(alice);
        factory.acceptOwnership();
        assertEq(factory.owner(), alice);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, address(this)));
        factory.createToken(address(0xBEEF), "Foo", "FOO", 6); // the previous owner lost the right
    }

    function test_initializeRejectsZeroDependencies() public {
        address impl = _implementation(address(factory));
        vm.expectRevert(ZERC20Factory.ZeroAddress.selector);
        _proxy(
            impl,
            abi.encodeCall(
                ZERC20Factory.initialize,
                (address(this), CommitmentLedger(address(0)), address(verifier), blocklist, tokenImpl)
            )
        );
        vm.expectRevert(ZERC20Factory.ZeroAddress.selector);
        _proxy(
            impl, abi.encodeCall(ZERC20Factory.initialize, (address(this), ledger, address(0), blocklist, tokenImpl))
        );
    }

    function test_factoryRejectsMiswiredDependencies() public {
        address factoryImpl = _implementation(address(factory));
        address ledgerImpl = _implementation(address(ledger));
        address verifierImpl = _implementation(address(verifier));
        IRootDeciderVerifier rootVerifier = ledger.rootVerifier();

        // The setUp ledger points at the existing factory, not at this new proxy.
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.Miswired.selector, address(ledger)));
        _proxy(
            factoryImpl,
            abi.encodeCall(ZERC20Factory.initialize, (address(this), ledger, address(verifier), blocklist, tokenImpl))
        );

        // Ledger is wired correctly (next deployment after it is the factory proxy), Verifier is not.
        address predicted = vm.computeCreateAddress(address(this), vm.getNonce(address(this)) + 1);
        CommitmentLedger ledger2 = CommitmentLedger(
            _proxy(
                ledgerImpl,
                abi.encodeCall(CommitmentLedger.initialize, (address(this), ITokenRegistry(predicted), rootVerifier))
            )
        );
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.Miswired.selector, address(verifier)));
        _proxy(
            factoryImpl,
            abi.encodeCall(ZERC20Factory.initialize, (address(this), ledger2, address(verifier), blocklist, tokenImpl))
        );

        // Verifier points at the new factory but at a different ledger.
        predicted = vm.computeCreateAddress(address(this), vm.getNonce(address(this)) + 2);
        ledger2 = CommitmentLedger(
            _proxy(
                ledgerImpl,
                abi.encodeCall(CommitmentLedger.initialize, (address(this), ITokenRegistry(predicted), rootVerifier))
            )
        );
        address verifier2 = _proxy(
            verifierImpl,
            abi.encodeCall(
                Verifier.initialize,
                (
                    address(this),
                    ITokenRegistry(predicted),
                    ledger,
                    verifier.joinSplitVerifier(),
                    verifier.rageExitVerifier(),
                    verifier.mergeVerifier(),
                    address(this)
                )
            )
        );
        vm.expectRevert(abi.encodeWithSelector(ZERC20Factory.Miswired.selector, verifier2));
        _proxy(
            factoryImpl,
            abi.encodeCall(ZERC20Factory.initialize, (address(this), ledger2, verifier2, blocklist, tokenImpl))
        );
    }
}
