// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Script} from "forge-std/Script.sol";
import {VmSafe} from "forge-std/Vm.sol";
import {stdJson} from "forge-std/StdJson.sol";
import {AccessManager} from "@openzeppelin/contracts/access/manager/AccessManager.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {Verifier} from "../src/Verifier.sol";
import {IMergeDeciderVerifier, IRootDeciderVerifier} from "../src/interfaces/INovaDeciderVerifier.sol";
import {IJoinSplitVerifier, IRageExitVerifier} from "../src/interfaces/IPrivateProofVerifier.sol";
import {JoinSplitGroth16Verifier} from "../src/verifiers/generated/JoinSplitGroth16Verifier.sol";
import {MergeDeciderVerifier} from "../src/verifiers/generated/MergeNovaVerifier.sol";
import {RageExitGroth16Verifier} from "../src/verifiers/generated/RageExitGroth16Verifier.sol";
import {RootDeciderVerifier} from "../src/verifiers/generated/RootNovaVerifier.sol";
import {ProtocolDeployer} from "./ProtocolDeployer.sol";

/// @title SwapVerifiers
/// @notice Puts the committed proof verifiers in place on a chain that deployments/<chainId>.json names:
///
///   forge script script/SwapVerifiers.s.sol --rpc-url $RPC_URL --broadcast --private-key $PRIVATE_KEY
///
/// Each verifier sits at an address derived from its creation code, as Deploy puts it, so one whose code is unchanged
/// is the one in use and stays. The Verifier's are set directly. The root verifier changes only through an emergency
/// and a recovery at the current root state, which withdraws no root. Every swap goes in one AccessManager multicall:
/// a commitment or a root landing between separate transactions would move the state the recovery restarts from.
/// The broadcaster needs the admin and pauser roles with no delay, as Deploy leaves them; with a delay the call
/// reverts unscheduled. A broadcast writes the new addresses into deployments/<chainId>.json.
contract SwapVerifiers is Script, ProtocolDeployer {
    using stdJson for string;

    function run() external {
        string memory file = string.concat(vm.projectRoot(), "/deployments/", vm.toString(block.chainid), ".json");
        // forge-lint: disable-next-line(unsafe-cheatcode) the deployment it swaps on
        string memory json = vm.readFile(file);
        ProofVerifiers memory v = swap(
            AccessManager(json.readAddress(".accessManager")),
            Verifier(json.readAddress(".verifier")),
            CommitmentLedger(json.readAddress(".ledger"))
        );
        if (!vm.isContext(VmSafe.ForgeContext.ScriptBroadcast)) return;
        vm.writeJson(vm.toString(address(v.joinSplit)), file, ".joinSplitVerifier");
        vm.writeJson(vm.toString(address(v.rageExit)), file, ".rageExitVerifier");
        vm.writeJson(vm.toString(address(v.root)), file, ".rootVerifier");
        vm.writeJson(vm.toString(address(v.merge)), file, ".mergeVerifier");
    }

    function swap(AccessManager manager, Verifier verifier, CommitmentLedger ledger)
        public
        returns (ProofVerifiers memory v)
    {
        vm.startBroadcast();
        (, deployer,) = vm.readCallers();
        v = ProofVerifiers({
            joinSplit: IJoinSplitVerifier(_code(type(JoinSplitGroth16Verifier).creationCode)),
            rageExit: IRageExitVerifier(_code(type(RageExitGroth16Verifier).creationCode)),
            root: IRootDeciderVerifier(_code(type(RootDeciderVerifier).creationCode)),
            merge: IMergeDeciderVerifier(_code(type(MergeDeciderVerifier).creationCode))
        });

        bytes[] memory calls = new bytes[](5);
        uint256 n;
        if (address(v.joinSplit) != address(verifier.joinSplitVerifier())) {
            calls[n++] = _execute(address(verifier), abi.encodeCall(Verifier.setJoinSplitVerifier, (v.joinSplit)));
        }
        if (address(v.rageExit) != address(verifier.rageExitVerifier())) {
            calls[n++] = _execute(address(verifier), abi.encodeCall(Verifier.setRageExitVerifier, (v.rageExit)));
        }
        if (address(v.merge) != address(verifier.mergeVerifier())) {
            calls[n++] = _execute(address(verifier), abi.encodeCall(Verifier.setMergeVerifier, (v.merge)));
        }
        if (address(v.root) != address(ledger.rootVerifier())) {
            CommitmentLedger.RootState memory s = ledger.rootState();
            calls[n++] = _execute(address(ledger), abi.encodeCall(CommitmentLedger.enterEmergency, (s.index)));
            calls[n++] = _execute(address(ledger), abi.encodeCall(CommitmentLedger.recover, (s.index, s.root, v.root)));
        }
        if (n != 0) {
            assembly ("memory-safe") {
                mstore(calls, n)
            }
            manager.multicall(calls);
        }
        vm.stopBroadcast();
    }

    function _execute(address target, bytes memory data) private pure returns (bytes memory) {
        return abi.encodeCall(AccessManager.execute, (target, data));
    }
}
