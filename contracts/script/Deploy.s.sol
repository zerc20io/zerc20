// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Script} from "forge-std/Script.sol";
import {VmSafe} from "forge-std/Vm.sol";
import {AccessManager} from "@openzeppelin/contracts/access/manager/AccessManager.sol";
import {Blocklist} from "../src/Blocklist.sol";
import {CommitmentLedger} from "../src/CommitmentLedger.sol";
import {Verifier} from "../src/Verifier.sol";
import {ZERC20Factory} from "../src/ZERC20Factory.sol";
import {IMergeDeciderVerifier, IRootDeciderVerifier} from "../src/interfaces/INovaDeciderVerifier.sol";
import {IJoinSplitVerifier, IRageExitVerifier} from "../src/interfaces/IPrivateProofVerifier.sol";
import {Protocol} from "../src/libs/Protocol.sol";
import {JoinSplitGroth16Verifier} from "../src/verifiers/generated/JoinSplitGroth16Verifier.sol";
import {MergeDeciderVerifier} from "../src/verifiers/generated/MergeNovaVerifier.sol";
import {RageExitGroth16Verifier} from "../src/verifiers/generated/RageExitGroth16Verifier.sol";
import {RootDeciderVerifier} from "../src/verifiers/generated/RootNovaVerifier.sol";
import {AcceptAll} from "../test/mocks/AcceptAll.sol";
import {CREATE3_FACTORY, CREATE3_FACTORY_CODE} from "./Create3Factory.sol";
import {DummyUSDC} from "./DummyUSDC.sol";
import {ProtocolDeployer} from "./ProtocolDeployer.sol";

/// @title Deploy
/// @notice Deploys the whole protocol through the CREATE3 factory:
///
///   forge script script/Deploy.s.sol --rpc-url $RPC_URL --broadcast --private-key $PRIVATE_KEY
///
///   DEPLOY_SALT    instance name (default "zerc20.dev"); a salt that was already used reverts
///   ASP_PUBLISHER  the account that publishes ASP roots (required, but on anvil the broadcaster by default)
///   ATTESTERS      comma-separated attester keys (required, but on anvil the broadcaster by default)
///   GUARDIANS      comma-separated accounts that may put the ledger in an emergency: the root prover (default: none)
///   DEV_ACCEPT_ALL_ROOTS  anvil only: the ledger takes roots without a proof (scripts/dev-stack.sh SPEED=fast)
///   DEV_ACCEPT_ALL_MERGES anvil only: the verifier takes merges without a proof (scripts/dev-stack.sh SPEED=fast)
///   DUMMY_USDC     anvil and the testnets only: also a DummyUSDC anyone may mint, and its zUSDC (token 2)
///   NATIVE_NAME, NATIVE_SYMBOL  the chain's native currency, which token 1 is named after (default Ether, ETH:
///                  zERC20 Ether, zETH; on Polygon POL: zERC20 POL, zPOL)
///
/// Verifiers and implementations live at addresses derived from their creation code, so unchanged
/// code (above all the costly Nova deciders) is reused, also by an instance with another DEPLOY_SALT.
/// Proxies, and the AccessManager that owns them all, live at addresses derived from DEPLOY_SALT. The
/// broadcaster holds every role with no delay, so the setup calls run straight through
/// `AccessManager.execute`; handing the roles over is a separate, later step. A fresh anvil node needs
/// `bootstrapAnvil` first.
/// A broadcast writes every address, and the block to index from, to deployments/<chainId>.json.
contract Deploy is Script, ProtocolDeployer {
    struct Deployment {
        address deployer;
        address accessManager;
        address blocklist;
        address ledger;
        address verifier;
        address factory;
        address depositAddressFactory;
        address zeth;
        address usdc; // DUMMY_USDC only
        address zusdc;
        address joinSplitVerifier;
        address rageExitVerifier;
        address rootVerifier;
        address mergeVerifier;
        address blocklistImpl;
        address ledgerImpl;
        address verifierImpl;
        address factoryImpl;
        address tokenImpl;
        address depositAddressFactoryImpl;
    }

    error AlreadyDeployed(string deploySalt);
    error UnexpectedCreate3Factory(bytes32 codehash);
    error AnvilOnly();
    error TestnetOnly();

    /// @dev AccessManager roles besides ADMIN_ROLE (0), which keeps every function not assigned to one.
    uint64 public constant OPERATOR_ROLE = 1;
    uint64 public constant PAUSER_ROLE = 2;

    function run() external returns (Deployment memory) {
        return deploy(vm.envOr("DEPLOY_SALT", string("zerc20.dev")), vm.envOr("DUMMY_USDC", false));
    }

    function deploy(string memory salt, bool dummyUsdc) public returns (Deployment memory d) {
        // a token anyone may mint, listed for good
        require(!dummyUsdc || _testnet(), TestnetOnly());
        deploySalt = salt;
        // Missing on a fresh anvil node: run `bootstrapAnvil` first.
        require(
            CREATE3_FACTORY.codehash == keccak256(CREATE3_FACTORY_CODE),
            UnexpectedCreate3Factory(CREATE3_FACTORY.codehash)
        );

        vm.startBroadcast();
        (, deployer,) = vm.readCallers();
        d.deployer = deployer;
        d.accessManager = _instanceAddress("AccessManager");
        require(d.accessManager.code.length == 0, AlreadyDeployed(deploySalt));

        ProofVerifiers memory v = ProofVerifiers({
            joinSplit: IJoinSplitVerifier(_code(type(JoinSplitGroth16Verifier).creationCode)),
            rageExit: IRageExitVerifier(_code(type(RageExitGroth16Verifier).creationCode)),
            root: IRootDeciderVerifier(_rootVerifier()),
            merge: IMergeDeciderVerifier(_mergeVerifier())
        });
        CREATE3.deploy(
            _instanceSalt("AccessManager"), abi.encodePacked(type(AccessManager).creationCode, abi.encode(deployer))
        );
        // Off anvil the ASP publisher and the attesters must be named: a default would leave both on this key.
        bool anvil = block.chainid == 31337;
        address asp = anvil ? vm.envOr("ASP_PUBLISHER", deployer) : vm.envAddress("ASP_PUBLISHER");
        // Every proxy is owned by the AccessManager.
        _record(d, v, _deployCore(d.accessManager, v, asp));

        // The broadcaster holds every role with no delay, so these run without scheduling.
        AccessManager manager = AccessManager(d.accessManager);
        _roles(manager, d);
        // "zERC20 <name>", not "z<name>": wallets' security scanners flag a name one letter off the underlying's
        // (zUSD Coin) as an impersonator and warn on every transaction to the token
        manager.execute(
            d.factory,
            abi.encodeCall(
                ZERC20Factory.createToken,
                (
                    Protocol.NATIVE,
                    string.concat("zERC20 ", vm.envOr("NATIVE_NAME", string("Ether"))),
                    string.concat("z", vm.envOr("NATIVE_SYMBOL", string("ETH"))),
                    18
                )
            )
        );
        d.zeth = ZERC20Factory(d.factory).tokenById(1);
        if (dummyUsdc) {
            d.usdc = _code(type(DummyUSDC).creationCode);
            DummyUSDC usdc = DummyUSDC(d.usdc);
            manager.execute(
                d.factory,
                abi.encodeCall(
                    ZERC20Factory.createToken,
                    (d.usdc, string.concat("zERC20 ", usdc.name()), string.concat("z", usdc.symbol()), 6)
                )
            );
            d.zusdc = ZERC20Factory(d.factory).tokenById(2);
        }
        address[] memory attesters =
            anvil ? vm.envOr("ATTESTERS", ",", _only(deployer)) : vm.envAddress("ATTESTERS", ",");
        for (uint256 i; i < attesters.length; ++i) {
            manager.execute(d.verifier, abi.encodeCall(Verifier.addAttester, (attesters[i])));
        }
        address[] memory guardians = vm.envOr("GUARDIANS", ",", new address[](0));
        for (uint256 i; i < guardians.length; ++i) {
            manager.execute(d.ledger, abi.encodeCall(CommitmentLedger.setGuardian, (guardians[i], true)));
        }
        vm.stopBroadcast();

        if (vm.isContext(VmSafe.ForgeContext.ScriptBroadcast)) _write(d);
    }

    /// @dev The chains DUMMY_USDC may list a DummyUSDC on: anvil, Sepolia, Base and Arbitrum Sepolia, BNB Smart
    ///      Chain Testnet and Polygon Amoy.
    function _testnet() private view returns (bool) {
        uint256 id = block.chainid;
        return id == 31337 || id == 11155111 || id == 84532 || id == 421614 || id == 97 || id == 80002;
    }

    /// @notice Put the CREATE3 factory on an anvil node (once per node, before `run`):
    ///   forge script script/Deploy.s.sol --sig "bootstrapAnvil()" --rpc-url $RPC_URL
    /// @dev A separate step: code set during `run` is missing from forge's on-chain simulation, which
    ///      then underestimates every transaction's gas.
    function bootstrapAnvil() external {
        vm.rpc(
            "anvil_setCode",
            string.concat('["', vm.toString(CREATE3_FACTORY), '","', vm.toString(CREATE3_FACTORY_CODE), '"]')
        );
    }

    /// @dev The Nova root decider, or on anvil with DEV_ACCEPT_ALL_ROOTS a verifier that accepts anything, for a root
    ///      prover that sends no proof (DEV_SKIP_PROOF): a root then takes seconds instead of half a minute.
    function _rootVerifier() private returns (address) {
        if (!vm.envOr("DEV_ACCEPT_ALL_ROOTS", false)) return _code(type(RootDeciderVerifier).creationCode);
        require(block.chainid == 31337, AnvilOnly());
        return _code(type(AcceptAll).creationCode);
    }

    /// @dev The Nova merge decider, or on anvil with DEV_ACCEPT_ALL_MERGES a verifier that accepts anything, for a merge
    ///      prover that checks each witness and proves nothing (DEV_SKIP_PROOF): a merge then takes seconds, with no
    ///      merge keys.
    function _mergeVerifier() private returns (address) {
        if (!vm.envOr("DEV_ACCEPT_ALL_MERGES", false)) return _code(type(MergeDeciderVerifier).creationCode);
        require(block.chainid == 31337, AnvilOnly());
        return _code(type(AcceptAll).creationCode);
    }

    function _record(Deployment memory d, ProofVerifiers memory v, Core memory c) private pure {
        d.blocklist = address(c.blocklist);
        d.ledger = address(c.ledger);
        d.verifier = address(c.verifier);
        d.factory = address(c.factory);
        d.depositAddressFactory = address(c.depositAddressFactory);
        d.joinSplitVerifier = address(v.joinSplit);
        d.rageExitVerifier = address(v.rageExit);
        d.rootVerifier = address(v.root);
        d.mergeVerifier = address(v.merge);
        d.blocklistImpl = c.blocklistImpl;
        d.ledgerImpl = c.ledgerImpl;
        d.verifierImpl = c.verifierImpl;
        d.factoryImpl = c.factoryImpl;
        d.tokenImpl = c.tokenImpl;
        d.depositAddressFactoryImpl = c.depositAddressFactoryImpl;
    }

    /// @dev The operator may change fees, list tokens, edit the blocklist and name guardians; the pauser may only
    ///      stop. Neither can upgrade, resume or move funds: every other function stays the admin's. The
    ///      broadcaster takes both roles with no delay.
    function _roles(AccessManager manager, Deployment memory d) private {
        manager.labelRole(OPERATOR_ROLE, "OPERATOR");
        manager.labelRole(PAUSER_ROLE, "PAUSER");
        _assign(manager, d.verifier, Verifier.setFee.selector, OPERATOR_ROLE);
        _assign(manager, d.factory, ZERC20Factory.createToken.selector, OPERATOR_ROLE);
        _assign(manager, d.factory, ZERC20Factory.setTokenMetadata.selector, OPERATOR_ROLE);
        _assign(manager, d.blocklist, Blocklist.setBlocked.selector, OPERATOR_ROLE);
        _assign(manager, d.ledger, CommitmentLedger.setGuardian.selector, OPERATOR_ROLE);
        _assign(manager, d.verifier, Verifier.pause.selector, PAUSER_ROLE);
        _assign(manager, d.verifier, Verifier.pauseToken.selector, PAUSER_ROLE);
        _assign(manager, d.ledger, CommitmentLedger.enterEmergency.selector, PAUSER_ROLE);
        _assign(manager, d.verifier, Verifier.revokeAspPublisher.selector, PAUSER_ROLE);
        _assign(manager, d.verifier, Verifier.revokeAttester.selector, PAUSER_ROLE);
        manager.grantRole(OPERATOR_ROLE, deployer, 0);
        manager.grantRole(PAUSER_ROLE, deployer, 0);
    }

    function _assign(AccessManager manager, address target, bytes4 selector, uint64 role) private {
        bytes4[] memory selectors = new bytes4[](1);
        selectors[0] = selector;
        manager.setTargetFunctionRole(target, selectors, role);
    }

    function _only(address account) private pure returns (address[] memory accounts) {
        accounts = new address[](1);
        accounts[0] = account;
    }

    function _write(Deployment memory d) private {
        string memory k = "deployment";
        vm.serializeUint(k, "chainId", block.chainid);
        // the head the script simulated on, at or before every broadcast transaction: the indexer's START_BLOCK
        vm.serializeUint(k, "startBlock", block.number);
        vm.serializeString(k, "deploySalt", deploySalt);
        vm.serializeAddress(k, "create3Factory", CREATE3_FACTORY);
        vm.serializeAddress(k, "deployer", d.deployer);
        vm.serializeAddress(k, "accessManager", d.accessManager);
        vm.serializeAddress(k, "blocklist", d.blocklist);
        vm.serializeAddress(k, "ledger", d.ledger);
        vm.serializeAddress(k, "verifier", d.verifier);
        vm.serializeAddress(k, "factory", d.factory);
        vm.serializeAddress(k, "depositAddressFactory", d.depositAddressFactory);
        vm.serializeAddress(k, "zeth", d.zeth);
        if (d.usdc != address(0)) {
            vm.serializeAddress(k, "usdc", d.usdc);
            vm.serializeAddress(k, "zusdc", d.zusdc);
        }
        vm.serializeAddress(k, "joinSplitVerifier", d.joinSplitVerifier);
        vm.serializeAddress(k, "rageExitVerifier", d.rageExitVerifier);
        vm.serializeAddress(k, "rootVerifier", d.rootVerifier);
        vm.serializeAddress(k, "mergeVerifier", d.mergeVerifier);
        vm.serializeAddress(k, "blocklistImpl", d.blocklistImpl);
        vm.serializeAddress(k, "ledgerImpl", d.ledgerImpl);
        vm.serializeAddress(k, "verifierImpl", d.verifierImpl);
        vm.serializeAddress(k, "factoryImpl", d.factoryImpl);
        vm.serializeAddress(k, "tokenImpl", d.tokenImpl);
        string memory json = vm.serializeAddress(k, "depositAddressFactoryImpl", d.depositAddressFactoryImpl);
        string memory dir = string.concat(vm.projectRoot(), "/deployments");
        vm.createDir(dir, true);
        vm.writeJson(json, string.concat(dir, "/", vm.toString(block.chainid), ".json"));
    }
}
