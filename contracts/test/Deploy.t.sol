// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Test} from "forge-std/Test.sol";
import {AccessManager} from "@openzeppelin/contracts/access/manager/AccessManager.sol";
import {IAccessManager} from "@openzeppelin/contracts/access/manager/IAccessManager.sol";
import {ERC1967Utils} from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Utils.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {UUPSUpgradeable} from "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import {Blocklist} from "../src/Blocklist.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {DepositAddressFactory} from "../src/DepositAddress.sol";
import {Verifier} from "../src/Verifier.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {ZERC20Factory} from "../src/ZERC20Factory.sol";
import {FeeSchedule} from "../src/libs/FeeSchedule.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {CREATE3_FACTORY, CREATE3_FACTORY_CODE} from "../script/Create3Factory.sol";
import {Deploy} from "../script/Deploy.s.sol";
import {DummyUSDC} from "../script/DummyUSDC.sol";

contract DeployTest is Test {
    // Mirrors of the roles Deploy assigns, written out independently.
    uint64 constant ADMIN = 0;
    uint64 constant OPERATOR = 1;
    uint64 constant PAUSER = 2;

    function setUp() public {
        vm.etch(CREATE3_FACTORY, CREATE3_FACTORY_CODE);
    }

    // The salt is passed directly: env vars are shared by tests running in parallel.
    function _deploy(string memory salt) internal returns (Deploy.Deployment memory) {
        return new Deploy().deploy(salt, false);
    }

    function _owned(Deploy.Deployment memory d) internal pure returns (address[5] memory) {
        return [d.blocklist, d.ledger, d.verifier, d.factory, d.depositAddressFactory];
    }

    function _assertMember(AccessManager m, uint64 role, address account, uint32 delay) internal view {
        (bool member, uint32 current) = m.hasRole(role, account);
        assertTrue(member);
        assertEq(current, delay);
    }

    function _expectDenied(AccessManager m, address caller, address target, bytes memory data) internal {
        vm.prank(caller);
        vm.expectRevert(
            // forge-lint: disable-next-line(unsafe-typecast)
            abi.encodeWithSelector(IAccessManager.AccessManagerUnauthorizedCall.selector, caller, target, bytes4(data))
        );
        m.execute(target, data);
    }

    function _flatFee(uint16 bps) internal pure returns (FeeSchedule.Tier[] memory tiers) {
        tiers = new FeeSchedule.Tier[](1);
        tiers[0] = FeeSchedule.Tier({minAmount: 0, feeBps: bps});
    }

    function test_deploysAndWiresTheProtocol() public {
        Deploy.Deployment memory d = _deploy("test.a");

        ZERC20Factory factory = ZERC20Factory(d.factory);
        assertEq(address(factory.ledger()), d.ledger);
        assertEq(factory.verifier(), d.verifier);
        assertEq(address(factory.blocklist()), d.blocklist);

        CommitmentLedger ledger = CommitmentLedger(d.ledger);
        assertEq(address(ledger.factory()), d.factory);
        assertEq(address(ledger.rootVerifier()), d.rootVerifier);

        Verifier verifier = Verifier(d.verifier);
        assertEq(address(verifier.factory()), d.factory);
        assertEq(address(verifier.ledger()), d.ledger);
        assertEq(address(verifier.joinSplitVerifier()), d.joinSplitVerifier);
        assertEq(address(verifier.rageExitVerifier()), d.rageExitVerifier);
        assertEq(address(verifier.mergeVerifier()), d.mergeVerifier);
        assertEq(verifier.aspPublisher(), d.deployer);
        assertTrue(verifier.isAttester(d.deployer));

        assertEq(address(DepositAddressFactory(d.depositAddressFactory).registry()), d.factory);

        address[5] memory owned = _owned(d);
        for (uint256 i; i < owned.length; ++i) {
            assertEq(OwnableUpgradeable(owned[i]).owner(), d.accessManager);
        }
        AccessManager m = AccessManager(d.accessManager);
        _assertMember(m, ADMIN, d.deployer, 0);
        _assertMember(m, OPERATOR, d.deployer, 0);
        _assertMember(m, PAUSER, d.deployer, 0);

        assertEq(factory.tokenById(1), d.zeth);
        assertEq(ZERC20(payable(d.zeth)).underlyingAsset(), Protocol.NATIVE);
        assertEq(d.usdc, address(0));
        assertEq(factory.tokenCount(), 1);
    }

    function test_operatorAndPauserGetOnlyTheirFunctions() public {
        Deploy.Deployment memory d = _deploy("test.a");
        AccessManager m = AccessManager(d.accessManager);

        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.setFee.selector), OPERATOR);
        assertEq(m.getTargetFunctionRole(d.factory, ZERC20Factory.createToken.selector), OPERATOR);
        assertEq(m.getTargetFunctionRole(d.factory, ZERC20Factory.setTokenMetadata.selector), OPERATOR);
        assertEq(m.getTargetFunctionRole(d.blocklist, Blocklist.setBlocked.selector), OPERATOR);
        assertEq(m.getTargetFunctionRole(d.ledger, CommitmentLedger.setGuardian.selector), OPERATOR);

        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.pause.selector), PAUSER);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.pauseToken.selector), PAUSER);
        assertEq(m.getTargetFunctionRole(d.ledger, CommitmentLedger.enterEmergency.selector), PAUSER);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.revokeAspPublisher.selector), PAUSER);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.revokeAttester.selector), PAUSER);

        // everything that changes code, resumes, or decides who attests or approves stays the admin's
        address[5] memory owned = _owned(d);
        for (uint256 i; i < owned.length; ++i) {
            assertEq(m.getTargetFunctionRole(owned[i], UUPSUpgradeable.upgradeToAndCall.selector), ADMIN);
            assertEq(m.getTargetFunctionRole(owned[i], OwnableUpgradeable.transferOwnership.selector), ADMIN);
        }
        assertEq(m.getTargetFunctionRole(d.factory, ZERC20Factory.upgradeTokenBeacon.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.ledger, CommitmentLedger.recover.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.unpause.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.unpauseToken.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.addAttester.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.setAspPublisher.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.setJoinSplitVerifier.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.setRageExitVerifier.selector), ADMIN);
        assertEq(m.getTargetFunctionRole(d.verifier, Verifier.setMergeVerifier.selector), ADMIN);
    }

    function test_operatorCannotReachAdminFunctions() public {
        Deploy.Deployment memory d = _deploy("test.a");
        AccessManager m = AccessManager(d.accessManager);
        address op = makeAddr("operator");
        vm.startPrank(d.deployer);
        m.grantRole(OPERATOR, op, 0);
        m.grantRole(PAUSER, op, 0);
        vm.stopPrank();

        // its own functions run at once
        vm.startPrank(op);
        m.execute(d.verifier, abi.encodeCall(Verifier.setFee, (1, op, _flatFee(300))));
        m.execute(d.verifier, abi.encodeCall(Verifier.pause, ()));
        vm.stopPrank();
        assertEq(Verifier(d.verifier).withdrawFee(1, 100), 3);
        assertTrue(Verifier(d.verifier).paused());

        CommitmentLedger ledger = CommitmentLedger(d.ledger);
        _expectDenied(m, op, d.verifier, abi.encodeCall(Verifier.unpause, ()));
        _expectDenied(m, op, d.verifier, abi.encodeCall(UUPSUpgradeable.upgradeToAndCall, (address(1), "")));
        _expectDenied(m, op, d.factory, abi.encodeCall(ZERC20Factory.upgradeTokenBeacon, (address(1))));
        _expectDenied(
            m, op, d.ledger, abi.encodeCall(CommitmentLedger.recover, (0, Protocol.EMPTY_ROOT, ledger.rootVerifier()))
        );
        _expectDenied(m, op, d.verifier, abi.encodeCall(Verifier.addAttester, (op)));
        _expectDenied(m, op, d.verifier, abi.encodeCall(Verifier.setAspPublisher, (op)));
        _expectDenied(m, op, d.verifier, abi.encodeCall(OwnableUpgradeable.transferOwnership, (op)));

        // nor can it schedule them, or change who may call what
        vm.startPrank(op);
        vm.expectRevert(
            abi.encodeWithSelector(
                IAccessManager.AccessManagerUnauthorizedCall.selector, op, d.verifier, Verifier.unpause.selector
            )
        );
        m.schedule(d.verifier, abi.encodeCall(Verifier.unpause, ()), 0);
        vm.expectRevert(abi.encodeWithSelector(IAccessManager.AccessManagerUnauthorizedAccount.selector, op, ADMIN));
        m.grantRole(ADMIN, op, 0);
        bytes4[] memory upgrade = new bytes4[](1);
        upgrade[0] = UUPSUpgradeable.upgradeToAndCall.selector;
        vm.expectRevert(abi.encodeWithSelector(IAccessManager.AccessManagerUnauthorizedAccount.selector, op, ADMIN));
        m.setTargetFunctionRole(d.verifier, upgrade, OPERATOR);
        vm.stopPrank();
    }

    function test_anAdminWithADelayMustScheduleAndWait() public {
        Deploy.Deployment memory d = _deploy("test.a");
        AccessManager m = AccessManager(d.accessManager);
        address gov = makeAddr("governance");
        bytes memory unpause = abi.encodeCall(Verifier.unpause, ());
        vm.startPrank(d.deployer);
        m.grantRole(ADMIN, gov, 2 days);
        m.execute(d.verifier, abi.encodeCall(Verifier.pause, ()));
        vm.stopPrank();

        vm.startPrank(gov);
        vm.expectRevert(); // not scheduled
        m.execute(d.verifier, unpause);
        m.schedule(d.verifier, unpause, 0);
        vm.expectRevert(); // not ready
        m.execute(d.verifier, unpause);
        vm.warp(block.timestamp + 2 days);
        m.execute(d.verifier, unpause);
        vm.stopPrank();
        assertFalse(Verifier(d.verifier).paused());
    }

    function test_aZeroDelayAdminRunsEverythingAtOnce() public {
        Deploy.Deployment memory d = _deploy("test.a");
        AccessManager m = AccessManager(d.accessManager);
        CommitmentLedger ledger = CommitmentLedger(d.ledger);
        address newImpl = address(new Verifier());

        vm.startPrank(d.deployer);
        m.execute(d.verifier, abi.encodeCall(UUPSUpgradeable.upgradeToAndCall, (newImpl, "")));
        m.execute(d.verifier, abi.encodeCall(Verifier.pause, ()));
        m.execute(d.verifier, abi.encodeCall(Verifier.unpause, ()));
        m.execute(d.ledger, abi.encodeCall(CommitmentLedger.enterEmergency, (0)));
        m.execute(d.ledger, abi.encodeCall(CommitmentLedger.recover, (0, Protocol.EMPTY_ROOT, ledger.rootVerifier())));
        vm.stopPrank();

        assertEq(address(uint160(uint256(vm.load(d.verifier, ERC1967Utils.IMPLEMENTATION_SLOT)))), newImpl);
        assertFalse(Verifier(d.verifier).paused());
        assertEq(ledger.bound(), type(uint64).max);
    }

    function test_handOverLeavesTheDeployerNothing() public {
        Deploy.Deployment memory d = _deploy("test.a");
        AccessManager m = AccessManager(d.accessManager);
        address gov = makeAddr("governance");
        address company = makeAddr("company");
        bytes memory pause = abi.encodeCall(Verifier.pause, ());
        bytes memory unpause = abi.encodeCall(Verifier.unpause, ());

        vm.startPrank(d.deployer);
        m.grantRole(ADMIN, gov, 1 days);
        m.grantRole(PAUSER, gov, 0);
        m.grantRole(OPERATOR, company, 0);
        m.grantRole(PAUSER, company, 0);
        m.renounceRole(OPERATOR, d.deployer);
        m.renounceRole(PAUSER, d.deployer);
        m.renounceRole(ADMIN, d.deployer);
        vm.stopPrank();

        _expectDenied(m, d.deployer, d.verifier, pause);
        _expectDenied(m, d.deployer, d.verifier, unpause);

        vm.startPrank(company);
        m.execute(d.verifier, abi.encodeCall(Verifier.setFee, (1, company, _flatFee(100))));
        m.execute(d.verifier, pause);
        vm.stopPrank();

        vm.startPrank(gov);
        m.schedule(d.verifier, unpause, 0);
        vm.warp(block.timestamp + 1 days);
        m.execute(d.verifier, unpause);
        vm.stopPrank();
        assertFalse(Verifier(d.verifier).paused());
    }

    function test_dummyUsdcOnlyOnTestnets() public {
        Deploy deploy = new Deploy();
        vm.chainId(1);
        vm.expectRevert(Deploy.TestnetOnly.selector);
        deploy.deploy("test.a", true);
    }

    function test_dummyUsdcIsMintableAndWrapped() public {
        Deploy.Deployment memory d = new Deploy().deploy("test.a", true);
        assertEq(ZERC20Factory(d.factory).tokenById(2), d.zusdc);
        ZERC20 zusdc = ZERC20(payable(d.zusdc));
        assertEq(zusdc.underlyingAsset(), d.usdc);
        assertEq(zusdc.decimals(), 6);

        address alice = makeAddr("alice");
        vm.startPrank(alice);
        DummyUSDC(d.usdc).mint(alice, 100e6); // anyone
        DummyUSDC(d.usdc).approve(d.zusdc, 100e6);
        zusdc.wrap(100e6, alice);
        vm.stopPrank();
        assertEq(zusdc.balanceOf(alice), 100e6);

        // another instance reuses the same DummyUSDC
        assertEq(new Deploy().deploy("test.b", true).usdc, d.usdc);
    }

    function test_namesTokensZerc20AndTheUnderlyingsNameNotAOneLetterCopyScannersFlag() public {
        Deploy.Deployment memory d = new Deploy().deploy("test.a", true);
        ZERC20 zeth = ZERC20(payable(d.zeth));
        ZERC20 zusdc = ZERC20(payable(d.zusdc));
        assertEq(zeth.name(), "zERC20 Ether");
        assertEq(zeth.symbol(), "zETH");
        assertEq(zusdc.name(), "zERC20 Dummy USD Coin");
        assertEq(zusdc.symbol(), "zUSDC");
    }

    function test_anotherSaltReusesCodeButNotProxies() public {
        Deploy.Deployment memory a = _deploy("test.a");
        Deploy.Deployment memory b = _deploy("test.b");

        assertEq(b.rootVerifier, a.rootVerifier);
        assertEq(b.mergeVerifier, a.mergeVerifier);
        assertEq(b.joinSplitVerifier, a.joinSplitVerifier);
        assertEq(b.verifierImpl, a.verifierImpl);
        assertNotEq(b.accessManager, a.accessManager);
        assertNotEq(b.verifier, a.verifier);
        assertEq(address(CommitmentLedger(b.ledger).rootVerifier()), a.rootVerifier);
    }

    function test_rejectsAUsedSalt() public {
        _deploy("test.a");
        // expectRevert does not catch a revert raised while broadcasting, so check the call directly.
        (bool ok, bytes memory err) = address(new Deploy()).call(abi.encodeCall(Deploy.deploy, ("test.a", false)));
        assertFalse(ok);
        assertEq(err, abi.encodeWithSelector(Deploy.AlreadyDeployed.selector, "test.a"));
    }
}
