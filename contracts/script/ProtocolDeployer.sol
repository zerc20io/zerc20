// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {ERC1967Proxy} from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol";
import {Blocklist} from "../src/Blocklist.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {DepositAddressFactory} from "../src/DepositAddress.sol";
import {Verifier} from "../src/Verifier.sol";
import {ZERC20} from "../src/ZERC20.sol";
import {ZERC20Factory} from "../src/ZERC20Factory.sol";
import {IMergeDeciderVerifier, IRootDeciderVerifier} from "../src/interfaces/INovaDeciderVerifier.sol";
import {IJoinSplitVerifier, IRageExitVerifier} from "../src/interfaces/IPrivateProofVerifier.sol";
import {ITokenRegistry} from "../src/interfaces/ITokenRegistry.sol";
import {CREATE3_FACTORY, ICREATE3Factory} from "./Create3Factory.sol";

/// @notice Deploys the protocol's proxies wired to one another, for Deploy, the indexer fixture and the tests alike,
///         so a changed initializer is written once.
/// @dev Through the CREATE3 factory, since the ledger and Verifier take the factory proxy's address before it exists.
///      Implementations sit at addresses derived from their creation code, so unchanged code is reused; proxies at
///      addresses derived from `deploySalt`. Both are namespaced by `deployer`, the account that calls the CREATE3
///      factory, and the inheriting contract sets both before deploying.
abstract contract ProtocolDeployer {
    struct ProofVerifiers {
        IJoinSplitVerifier joinSplit;
        IRageExitVerifier rageExit;
        IRootDeciderVerifier root;
        IMergeDeciderVerifier merge;
    }

    struct Core {
        Blocklist blocklist;
        CommitmentLedger ledger;
        Verifier verifier;
        ZERC20Factory factory;
        DepositAddressFactory depositAddressFactory;
        address blocklistImpl;
        address ledgerImpl;
        address verifierImpl;
        address factoryImpl;
        address tokenImpl;
        address depositAddressFactoryImpl;
    }

    ICREATE3Factory internal constant CREATE3 = ICREATE3Factory(CREATE3_FACTORY);

    string internal deploySalt;
    address internal deployer;

    /// @dev Every proxy is owned by `owner`; no token exists yet.
    function _deployCore(address owner, ProofVerifiers memory v, address aspPublisher)
        internal
        returns (Core memory c)
    {
        c.blocklistImpl = _code(type(Blocklist).creationCode);
        c.ledgerImpl = _code(type(CommitmentLedger).creationCode);
        c.verifierImpl = _code(type(Verifier).creationCode);
        c.factoryImpl = _code(type(ZERC20Factory).creationCode);
        c.tokenImpl = _code(type(ZERC20).creationCode);
        c.depositAddressFactoryImpl = _code(type(DepositAddressFactory).creationCode);

        ITokenRegistry factory = ITokenRegistry(_instanceAddress("ZERC20Factory"));
        c.blocklist = Blocklist(_proxy("Blocklist", c.blocklistImpl, abi.encodeCall(Blocklist.initialize, (owner))));
        c.ledger = CommitmentLedger(
            _proxy(
                "CommitmentLedger", c.ledgerImpl, abi.encodeCall(CommitmentLedger.initialize, (owner, factory, v.root))
            )
        );
        c.verifier = Verifier(
            _proxy(
                "Verifier",
                c.verifierImpl,
                abi.encodeCall(
                    Verifier.initialize, (owner, factory, c.ledger, v.joinSplit, v.rageExit, v.merge, aspPublisher)
                )
            )
        );
        c.factory = ZERC20Factory(
            _proxy(
                "ZERC20Factory",
                c.factoryImpl,
                abi.encodeCall(
                    ZERC20Factory.initialize, (owner, c.ledger, address(c.verifier), c.blocklist, c.tokenImpl)
                )
            )
        );
        c.depositAddressFactory = _depositAddressFactory(owner, factory, c.depositAddressFactoryImpl);
    }

    /// @dev The deposit address factory owned by `owner` over `registry`, deployed if missing. Its proxy sits at an
    ///      address derived from `implementation`, which holds the clone's code: a changed clone gets a factory of its
    ///      own, at one address on every chain, and the one before keeps serving the addresses it derived.
    function _depositAddressFactory(address owner, ITokenRegistry registry, address implementation)
        internal
        returns (DepositAddressFactory)
    {
        bytes32 salt = keccak256(abi.encode(deploySalt, "DepositAddressFactory", implementation));
        address deployed = CREATE3.getDeployed(deployer, salt);
        if (deployed.code.length == 0) {
            bytes memory initData = abi.encodeCall(DepositAddressFactory.initialize, (owner, registry));
            CREATE3.deploy(
                salt, abi.encodePacked(type(ERC1967Proxy).creationCode, abi.encode(implementation, initData))
            );
        }
        return DepositAddressFactory(deployed);
    }

    /// @dev Deploys `creationCode` at an address derived from its hash, or reuses what is already there.
    function _code(bytes memory creationCode) internal returns (address deployed) {
        bytes32 salt = keccak256(abi.encode("zerc20.code", keccak256(creationCode)));
        deployed = CREATE3.getDeployed(deployer, salt);
        if (deployed.code.length == 0) CREATE3.deploy(salt, creationCode);
    }

    function _proxy(string memory label, address implementation, bytes memory initData) internal returns (address) {
        bytes memory creationCode =
            abi.encodePacked(type(ERC1967Proxy).creationCode, abi.encode(implementation, initData));
        return CREATE3.deploy(_instanceSalt(label), creationCode);
    }

    function _instanceAddress(string memory label) internal view returns (address) {
        return CREATE3.getDeployed(deployer, _instanceSalt(label));
    }

    function _instanceSalt(string memory label) internal view returns (bytes32) {
        return keccak256(abi.encode(deploySalt, label));
    }
}
