// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Test} from "forge-std/Test.sol";
import {DepositAddressFactory} from "../src/DepositAddress.sol";
import {ITokenRegistry} from "../src/interfaces/ITokenRegistry.sol";
import {CREATE3_FACTORY, CREATE3_FACTORY_CODE} from "../script/Create3Factory.sol";
import {Deploy} from "../script/Deploy.s.sol";
import {ProtocolDeployer} from "../script/ProtocolDeployer.sol";
import {SwapDepositAddressFactory} from "../script/SwapDepositAddressFactory.s.sol";

/// @dev `_depositAddressFactory` with any implementation, deploying from this contract's CREATE3 namespace.
contract FactoryDeployer is ProtocolDeployer {
    constructor() {
        deploySalt = "test.factories";
        deployer = address(this);
    }

    function factory(address owner, ITokenRegistry registry, address implementation)
        external
        returns (DepositAddressFactory)
    {
        return _depositAddressFactory(owner, registry, implementation);
    }
}

contract SwapDepositAddressFactoryTest is Test {
    function setUp() public {
        vm.etch(CREATE3_FACTORY, CREATE3_FACTORY_CODE);
    }

    function test_theCommittedFactoryIsTheDeployedOneAndStays() public {
        Deploy.Deployment memory d = new Deploy().deploy("test.swap", false);
        SwapDepositAddressFactory script = new SwapDepositAddressFactory();
        vm.recordLogs();
        (DepositAddressFactory f, address implementation) =
            script.swap("test.swap", d.deployer, d.accessManager, ITokenRegistry(d.factory));
        assertEq(vm.getRecordedLogs().length, 0); // nothing deployed
        assertEq(address(f), d.depositAddressFactory);
        assertEq(implementation, d.depositAddressFactoryImpl);
    }

    function test_aChangedImplementationGetsAFactoryOfItsOwn() public {
        FactoryDeployer h = new FactoryDeployer();
        address owner = address(0x0A11);
        ITokenRegistry registry = ITokenRegistry(address(0xFAC));
        address before = address(new DepositAddressFactory());
        address changed = address(new DepositAddressFactory());

        DepositAddressFactory f = h.factory(owner, registry, before);
        assertEq(address(h.factory(owner, registry, before)), address(f)); // reused, not deployed again
        DepositAddressFactory g = h.factory(owner, registry, changed);
        assertNotEq(address(g), address(f));
        assertEq(g.owner(), owner);
        assertEq(address(g.registry()), address(registry));
        assertGt(address(f).code.length, 0); // the one before stays
    }

    function test_onlyTheDeployerSwaps() public {
        Deploy.Deployment memory d = new Deploy().deploy("test.swap", false);
        SwapDepositAddressFactory script = new SwapDepositAddressFactory();
        vm.expectPartialRevert(SwapDepositAddressFactory.NotTheDeployer.selector);
        script.swap("test.swap", address(0xBAD), d.accessManager, ITokenRegistry(d.factory));
    }
}
