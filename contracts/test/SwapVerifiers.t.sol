// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Test, Vm} from "forge-std/Test.sol";
import {AccessManager} from "@openzeppelin/contracts/access/manager/AccessManager.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {Verifier} from "../src/Verifier.sol";
import {MergeDeciderVerifier} from "../src/verifiers/generated/MergeNovaVerifier.sol";
import {RootDeciderVerifier} from "../src/verifiers/generated/RootNovaVerifier.sol";
import {CREATE3_FACTORY, CREATE3_FACTORY_CODE} from "../script/Create3Factory.sol";
import {Deploy} from "../script/Deploy.s.sol";
import {ProtocolDeployer} from "../script/ProtocolDeployer.sol";
import {SwapVerifiers} from "../script/SwapVerifiers.s.sol";

contract SwapVerifiersTest is Test {
    function setUp() public {
        vm.etch(CREATE3_FACTORY, CREATE3_FACTORY_CODE);
    }

    // Copies of the committed deciders at other addresses stand in for verifiers older than the committed code.
    function test_swapsTheChangedVerifiersAndKeepsTheRootState() public {
        Deploy.Deployment memory d = new Deploy().deploy("test.swap", false);
        AccessManager m = AccessManager(d.accessManager);
        CommitmentLedger ledger = CommitmentLedger(d.ledger);
        Verifier verifier = Verifier(d.verifier);
        CommitmentLedger.RootState memory s = ledger.rootState();
        vm.startPrank(d.deployer);
        m.execute(d.verifier, abi.encodeCall(Verifier.setMergeVerifier, (new MergeDeciderVerifier())));
        m.execute(d.ledger, abi.encodeCall(CommitmentLedger.enterEmergency, (s.index)));
        m.execute(d.ledger, abi.encodeCall(CommitmentLedger.recover, (s.index, s.root, new RootDeciderVerifier())));
        vm.stopPrank();
        uint32 era = ledger.era();

        SwapVerifiers script = new SwapVerifiers();
        ProtocolDeployer.ProofVerifiers memory v = script.swap(m, verifier, ledger);

        assertEq(address(v.root), d.rootVerifier);
        assertEq(address(v.merge), d.mergeVerifier);
        assertEq(address(ledger.rootVerifier()), d.rootVerifier);
        assertEq(address(verifier.mergeVerifier()), d.mergeVerifier);
        assertEq(address(verifier.joinSplitVerifier()), d.joinSplitVerifier);
        assertEq(address(verifier.rageExitVerifier()), d.rageExitVerifier);
        assertEq(abi.encode(ledger.rootState()), abi.encode(s));
        assertEq(ledger.bound(), type(uint64).max);
        assertEq(ledger.era(), era + 1);

        // Every verifier is the committed one now, so a second run sends nothing.
        vm.recordLogs();
        script.swap(m, verifier, ledger);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 0);
        assertEq(ledger.era(), era + 1);
    }
}
