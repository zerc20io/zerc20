// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Script} from "forge-std/Script.sol";
import {VmSafe} from "forge-std/Vm.sol";
import {stdJson} from "forge-std/StdJson.sol";
import {DepositAddressFactory} from "../src/DepositAddress.sol";
import {ITokenRegistry} from "../src/interfaces/ITokenRegistry.sol";
import {ProtocolDeployer} from "./ProtocolDeployer.sol";

/// @title SwapDepositAddressFactory
/// @notice Puts the committed deposit address factory in place on a chain that deployments/<chainId>.json names:
///
///   forge script script/SwapDepositAddressFactory.s.sol --rpc-url $RPC_URL --broadcast --private-key $PRIVATE_KEY
///
/// A factory sits at an address derived from its implementation, as Deploy puts it, so one whose code is unchanged is
/// the one in use and stays. A new one is owned by the same AccessManager over the same token registry, and the one
/// before stays as well: the addresses it derived are flushed and refunded through it. No contract names a factory, so
/// this is the whole swap on chain; the deposit relayer and the apps read the new address from the json.
/// The broadcaster is the deployer the json names, whose CREATE3 namespace puts the factory at one address on every
/// chain. A broadcast writes the new addresses into deployments/<chainId>.json.
contract SwapDepositAddressFactory is Script, ProtocolDeployer {
    using stdJson for string;

    error NotTheDeployer(address broadcaster, address deployer);

    function run() external {
        string memory file = string.concat(vm.projectRoot(), "/deployments/", vm.toString(block.chainid), ".json");
        // forge-lint: disable-next-line(unsafe-cheatcode) the deployment it swaps on
        string memory json = vm.readFile(file);
        (DepositAddressFactory f, address implementation) = swap(
            json.readString(".deploySalt"),
            json.readAddress(".deployer"),
            json.readAddress(".accessManager"),
            ITokenRegistry(json.readAddress(".factory"))
        );
        if (!vm.isContext(VmSafe.ForgeContext.ScriptBroadcast)) return;
        vm.writeJson(vm.toString(address(f)), file, ".depositAddressFactory");
        vm.writeJson(vm.toString(implementation), file, ".depositAddressFactoryImpl");
    }

    function swap(string memory salt, address expectedDeployer, address owner, ITokenRegistry registry)
        public
        returns (DepositAddressFactory f, address implementation)
    {
        deploySalt = salt;
        vm.startBroadcast();
        (, deployer,) = vm.readCallers();
        require(deployer == expectedDeployer, NotTheDeployer(deployer, expectedDeployer));
        implementation = _code(type(DepositAddressFactory).creationCode);
        f = _depositAddressFactory(owner, registry, implementation);
        vm.stopBroadcast();
    }
}
