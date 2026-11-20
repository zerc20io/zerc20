// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Script} from "forge-std/Script.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {Verifier} from "../src/Verifier.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {IRootDeciderVerifier, NovaDeciderProof} from "../src/interfaces/INovaDeciderVerifier.sol";
import {Groth16Proof} from "../src/interfaces/IPrivateProofVerifier.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {RootDeciderVerifier} from "../src/verifiers/generated/RootNovaVerifier.sol";
import {AcceptAll} from "../test/mocks/AcceptAll.sol";
import {ProtocolDeployer} from "./ProtocolDeployer.sol";

/// @dev Holds zETH and hands it out 1 wei at a time, so one transaction appends many commitments.
contract Spray {
    function spray(ZERC20 token, uint256 n) external {
        for (uint256 i = 1; i <= n; ++i) {
            // forge-lint: disable-next-line(unsafe-typecast)
            require(token.transfer(address(uint160(0x5000 + i)), 1));
        }
    }
}

/// @title IndexerFixture
/// @notice Real ledger and verifier events for backend/indexer's e2e tests, on anvil. Proofs go to a verifier that
///         accepts everything; attestations are signed by PRIVATE_KEY, which also broadcasts.
///
///   forge script script/IndexerFixture.s.sol --tc IndexerFixture --sig "deploy()" --rpc-url $RPC --broadcast
///   forge script script/IndexerFixture.s.sol --tc IndexerFixture --sig "activity(uint256,uint256)" 5 1000 --rpc-url $RPC --broadcast
///   forge script script/IndexerFixture.s.sol --tc IndexerFixture --sig "recover(uint64,uint256)" $INDEX $ROOT --rpc-url $RPC --broadcast
///
/// `deploy` needs the CREATE3 factory on the node (`Deploy.bootstrapAnvil`) and writes the addresses to
/// deployments/indexer-fixture.json. Each `activity` round makes a burn deposit
/// and rage-exits it, a transfer, a transact, a 3-input merge, `sprayCount` transfers in one transaction, and a
/// root transition to a made-up root (which the indexer reports as not matching its own).
///
/// With REAL_ROOT_VERIFIER=1 (backend/root-prover's e2e), the ledger gets the real RootDeciderVerifier and `activity`
/// leaves root transitions to the root-prover.
contract IndexerFixture is Script, ProtocolDeployer {
    string constant FILE = "/deployments/indexer-fixture.json";
    uint32 constant TOKEN_ID = 1;
    uint256 constant ASP_ROOT = 1;
    bytes32 constant TRANSACT_TYPEHASH = keccak256(
        "Transact(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256 nullifier0,"
        "uint256 nullifier1,uint256 withdrawRecipient,uint256 withdrawAmount,uint256 withdrawIntent,uint256 noteHash1,"
        "uint256 noteHash2)"
    );
    bytes32 constant MERGE_TYPEHASH = keccak256(
        "Merge(uint256 tokenId,uint256 chainId,uint256 commitmentRoot,uint256 aspRoot,uint256[] nullifiers,"
        "uint256 noteHash,uint256 fee,uint256 feeRecipient)"
    );

    function deploy() external {
        uint256 key = vm.envUint("PRIVATE_KEY");
        uint256 startBlock = block.number;
        vm.startBroadcast(key);
        (CommitmentLedger ledger, Verifier verifier, ZERC20 token) = _deploy(vm.addr(key));
        vm.stopBroadcast();

        string memory j = "fixture";
        vm.serializeAddress(j, "ledger", address(ledger));
        vm.serializeAddress(j, "verifier", address(verifier));
        vm.serializeAddress(j, "token", address(token));
        vm.writeJson(vm.serializeUint(j, "startBlock", startBlock), string.concat(vm.projectRoot(), FILE));
    }

    function _deploy(address me) internal returns (CommitmentLedger ledger, Verifier verifier, ZERC20 token) {
        deployer = me;
        deploySalt = "indexer-fixture";
        AcceptAll mock = new AcceptAll();
        IRootDeciderVerifier root = _realRoots() ? IRootDeciderVerifier(address(new RootDeciderVerifier())) : mock;
        Core memory c = _deployCore(me, ProofVerifiers({joinSplit: mock, rageExit: mock, root: root, merge: mock}), me);
        (ledger, verifier) = (c.ledger, c.verifier);
        token = ZERC20(payable(c.factory.createToken(Protocol.NATIVE, "zEther", "zETH", 18)));
        verifier.publishAspRoot(ASP_ROOT);
        verifier.addAttester(me);
    }

    function activity(uint256 rounds, uint256 sprayCount) external {
        uint256 key = vm.envUint("PRIVATE_KEY");
        address me = vm.addr(key);
        // forge-lint: disable-next-line(unsafe-cheatcode) the deployment it runs against
        string memory json = vm.readFile(string.concat(vm.projectRoot(), FILE));
        CommitmentLedger ledger = CommitmentLedger(vm.parseJsonAddress(json, ".ledger"));
        Verifier verifier = Verifier(vm.parseJsonAddress(json, ".verifier"));
        ZERC20 token = ZERC20(payable(vm.parseJsonAddress(json, ".token")));
        // nullifiers, note hashes and roots differ per round, per run (the ledger only grows), and between two runs
        // from the same state with different `sprayCount` (the two sides of a reorg in the e2e test)
        uint256 salt = (uint256(ledger.nextIndex()) << 32) + (sprayCount << 16);
        NovaDeciderProof memory noProof;

        vm.startBroadcast(key);
        Spray spray = new Spray();
        for (uint256 r; r < rounds; ++r) {
            uint256 s = salt + r * 16;
            _depositAndRageExit(ledger, verifier, token, me, s);
            // forge-lint: disable-next-line(unsafe-typecast)
            require(token.transfer(address(uint160(0xA000 + s)), 1));
            verifier.transact(_transact(key, verifier, s));
            verifier.merge(_merge(key, verifier, s));
            if (sprayCount > 0) {
                token.wrap{value: sprayCount}(sprayCount, address(spray));
                spray.spray(token, sprayCount);
            }
            if (!_realRoots()) {
                (uint64 index, uint256 hashChain) = ledger.reserveHashChain();
                ledger.proveRootTransition(
                    CommitmentLedger.RootState({index: index, hashChain: hashChain, root: s + 7}), noProof
                );
            }
        }
        vm.stopBroadcast();
    }

    /// @notice An emergency, then a recovery to the proved `root` at `index`: the root stream steps back to it.
    function recover(uint64 index, uint256 root) external {
        // forge-lint: disable-next-line(unsafe-cheatcode) the deployment it runs against
        string memory json = vm.readFile(string.concat(vm.projectRoot(), FILE));
        CommitmentLedger ledger = CommitmentLedger(vm.parseJsonAddress(json, ".ledger"));
        IRootDeciderVerifier rootVerifier = ledger.rootVerifier();
        vm.startBroadcast(vm.envUint("PRIVATE_KEY"));
        ledger.enterEmergency(index);
        ledger.recover(index, root, rootVerifier);
        vm.stopBroadcast();
    }

    /// @dev One commitment and one nullifier: the rage exit walks the hash chain from the deposit to a checkpoint.
    function _depositAndRageExit(CommitmentLedger ledger, Verifier verifier, ZERC20 token, address me, uint256 s)
        internal
    {
        // forge-lint: disable-next-line(unsafe-typecast)
        address burn = address(uint160(0xB000 + s));
        uint256 prev = ledger.hashChain();
        token.wrap{value: 1 ether}(1 ether, burn);
        (uint64 end,) = ledger.reserveHashChain();
        uint256[4][] memory commits = new uint256[4][](1);
        commits[0] =
            [Protocol.encode(Protocol.TRANSFER_TAG, TOKEN_ID), uint256(uint160(me)), uint256(uint160(burn)), 1 ether];
        Groth16Proof memory noProof;
        verifier.rageExit(
            Verifier.RageExitRequest({
                checkpointIndex: end, prevHashChain: prev, commitments: commits, nullifier: s + 1, proof: noProof
            })
        );
    }

    /// @dev Two nullifiers, two notes.
    function _transact(uint256 key, Verifier verifier, uint256 s)
        internal
        view
        returns (Verifier.TransactRequest memory r)
    {
        r.publicSignals = Verifier.TransactSignals({
            tokenId: TOKEN_ID,
            chainId: block.chainid,
            commitmentRoot: Protocol.EMPTY_ROOT,
            aspRoot: ASP_ROOT,
            nullifier0: s + 2,
            nullifier1: s + 3,
            withdrawRecipient: 0,
            withdrawAmount: 0,
            withdrawIntent: 0,
            noteHash1: s + 4,
            noteHash2: s + 5
        });
        r.attestation = _sign(key, verifier, keccak256(abi.encode(TRANSACT_TYPEHASH, r.publicSignals)));
    }

    /// @dev Three nullifiers, one note.
    function _merge(uint256 key, Verifier verifier, uint256 s) internal view returns (Verifier.MergeRequest memory r) {
        r.tokenId = TOKEN_ID;
        r.commitmentRoot = Protocol.EMPTY_ROOT;
        r.aspRoot = ASP_ROOT;
        r.noteHash = s + 6;
        r.nullifiers = new uint256[](3);
        for (uint256 i; i < 3; ++i) {
            r.nullifiers[i] = s + 8 + i;
        }
        bytes32 statement = keccak256(
            abi.encode(
                MERGE_TYPEHASH,
                r.tokenId,
                block.chainid,
                r.commitmentRoot,
                r.aspRoot,
                keccak256(abi.encodePacked(r.nullifiers)),
                r.noteHash,
                r.fee,
                r.feeRecipient
            )
        );
        r.attestation = _sign(key, verifier, statement);
    }

    function _sign(uint256 key, Verifier verifier, bytes32 structHash) internal view returns (bytes memory) {
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256("zERC20 Verifier"),
                keccak256("1"),
                block.chainid,
                address(verifier)
            )
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, keccak256(abi.encodePacked("\x19\x01", domain, structHash)));
        return abi.encodePacked(r, s, v);
    }

    function _realRoots() internal view returns (bool) {
        return vm.envOr("REAL_ROOT_VERIFIER", false);
    }
}
