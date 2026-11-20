//! The protocol contracts' calls, events and structs the nodes use, declared once so that every node encodes and
//! decodes them alike.
// sol! gives `Transacted` a constructor taking each of its ten fields
#![allow(clippy::too_many_arguments)]
use alloy::primitives::Address;
use alloy::providers::Provider;
use alloy::sol;
use anyhow::Result;
use serde::Deserialize;

sol! {
    #[derive(Default, Deserialize)]
    struct Groth16Proof {
        uint256[2] pA;
        uint256[2][2] pB;
        uint256[2] pC;
    }
    #[derive(Deserialize)]
    struct TransactSignals {
        uint256 tokenId;
        uint256 chainId;
        uint256 commitmentRoot;
        uint256 aspRoot;
        uint256 nullifier0;
        uint256 nullifier1;
        uint256 withdrawRecipient;
        uint256 withdrawAmount;
        uint256 withdrawIntent;
        uint256 noteHash1;
        uint256 noteHash2;
    }
    #[derive(Deserialize)]
    struct TransactRequest {
        uint64 rootIndex;
        Groth16Proof proof;
        TransactSignals publicSignals;
        bytes attestation;
    }
    /// Nova decider calldata after `z_i`: the caller rebuilds `i`, `z_0` and `z_i` itself.
    #[derive(Default, Deserialize)]
    struct NovaDeciderProof {
        uint256 challenge;
        uint256[2] runningCmE;
        uint256[2] cmT;
        uint256[2] runningCmW;
        uint256[2] incomingCmW;
        uint256[12] proof;
    }
    #[derive(Deserialize)]
    struct MergeRequest {
        uint64 rootIndex;
        uint256 tokenId;
        uint256 commitmentRoot;
        uint256 aspRoot;
        uint256 noteHash;
        uint256 fee;
        uint256 feeRecipient;
        uint256[] nullifiers;
        NovaDeciderProof proof;
        bytes attestation;
    }

    #[sol(rpc)]
    interface IVerifier {
        event NullifierSpent(uint256 indexed nullifier);
        event Transacted(
            address indexed caller,
            uint32 indexed tokenId,
            uint256 indexed commitmentRoot,
            address withdrawRecipient,
            uint256 withdrawAmount,
            uint256 feeAmount,
            uint256 noteHash1,
            uint256 noteHash2,
            uint64 noteIndex1,
            uint64 noteIndex2
        );
        event Merged(
            address indexed caller,
            uint32 indexed tokenId,
            uint256 indexed commitmentRoot,
            uint256 inputCount,
            uint256 noteHash,
            uint64 noteIndex
        );
        event RageExited(address indexed caller, uint32 indexed tokenId, address recipient, uint256 amount, uint256 nullifier);

        function owner() external view returns (address);
        function ledger() external view returns (address);
        function factory() external view returns (address);
        function aspPublisher() external view returns (address);
        function latestAspRoot() external view returns (uint256);
        function publishAspRoot(uint256 aspRoot) external;
        function transact(TransactRequest calldata request) external;
        function merge(MergeRequest calldata request) external;
        function withdrawFee(uint32 tokenId, uint256 amount) external view returns (uint256);
    }

    #[sol(rpc)]
    interface ILedger {
        struct RootState { uint64 index; uint256 hashChain; uint256 root; }

        event Committed(uint64 indexed index, uint256[4] fields);
        event CheckpointRecorded(uint64 indexed index, uint256 hashChain);
        event RootProved(uint64 indexed oldIndex, uint64 indexed newIndex, uint256 newRoot);
        event Recovered(uint64 indexed oldIndex, uint64 indexed newIndex, uint256 newRoot, address rootVerifier);

        function nextIndex() external view returns (uint64);
        function hashChain() external view returns (uint256);
        function rootState() external view returns (RootState memory);
        function reserveHashChain() external returns (uint64 index, uint256 checkpoint);
        function proveRootTransition(RootState calldata newState, NovaDeciderProof calldata proof) external;
        function bound() external view returns (uint64);
        function enterEmergency(uint64 bound) external;
        function provedRoots(uint64 index, uint256 root) external view returns (bool);
        function provedIn(uint64 index, uint256 root) external view returns (uint32);
    }

    #[sol(rpc)]
    interface IFactory {
        function blocklist() external view returns (address);
        function tokenBeacon() external view returns (address);
        function tokenIdOf(address underlying) external view returns (uint32);
        function tokenById(uint32 tokenId) external view returns (address);
    }

    /// OpenZeppelin's AccessManager, which owns every protocol contract.
    interface IAccessManager {
        event OperationScheduled(
            bytes32 indexed operationId,
            uint32 indexed nonce,
            uint48 schedule,
            address caller,
            address target,
            bytes data
        );
        event RoleGranted(uint64 indexed roleId, address indexed account, uint32 delay, uint48 since, bool newMember);
    }

    /// An ERC-1967 proxy, or a beacon.
    interface IUpgradeable {
        event Upgraded(address indexed implementation);
    }

    #[sol(rpc)]
    interface IBlocklist {
        function isBlocked(address account) external view returns (bool);
    }

    #[sol(rpc)]
    interface IZERC20 {
        function underlyingAsset() external view returns (address);
        function tokenId() external view returns (uint32);
        function decimals() external view returns (uint8);
        function symbol() external view returns (string memory);
        function balanceOf(address account) external view returns (uint256);
        function unwrap(uint256 amount, address receiver) external;
    }

    /// A Chainlink price feed.
    #[sol(rpc)]
    interface IAggregator {
        function decimals() external view returns (uint8);
        function latestRoundData() external view returns (
            uint80 roundId, int256 answer, uint256 startedAt, uint256 updatedAt, uint80 answeredInRound
        );
    }
}

/// `Protocol.NATIVE`: the underlying of a token that wraps the native asset.
pub const NATIVE: Address =
    alloy::primitives::address!("0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE");

/// The ledger the Verifier at `verifier` reads, and the protocol's sanctions list, shared by every token: set once
/// when the factory is initialized, with no setter.
pub async fn ledger_and_blocklist(
    provider: &impl Provider,
    verifier: Address,
) -> Result<(Address, Address)> {
    let v = IVerifier::new(verifier, provider);
    let ledger = v.ledger().call().await?;
    let blocklist = IFactory::new(v.factory().call().await?, provider)
        .blocklist()
        .call()
        .await?;
    Ok((ledger, blocklist))
}
