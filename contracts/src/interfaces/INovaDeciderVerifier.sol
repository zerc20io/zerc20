// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Nova decider calldata after `z_i`, in the order sonobe's decider takes it. The caller rebuilds
///         `i`, `z_0` and `z_i` itself, so a proof is only this part.
struct NovaDeciderProof {
    uint256 challenge;
    uint256[2] runningCmE;
    uint256[2] cmT;
    uint256[2] runningCmW;
    uint256[2] incomingCmW;
    uint256[12] proof;
}

/// @title IRootDeciderVerifier
/// @notice Sonobe-rendered Nova decider verifier for the root circuit.
/// @dev The signature is fixed by sonobe's CycleFold decider template with Nova's fold fragment.
///      The state is [index, hashChain, root]; each step appends one commitment, so `i` is the index delta.
///      Reverts for an invalid proof. With `i == 0` it returns once `z0 == zi`, without a proof.
interface IRootDeciderVerifier {
    /// @notice Verify that `i` folded steps take `z0` to `zi`.
    function verifyDeciderProof(
        uint256 i,
        uint256[3] calldata z0,
        uint256[3] calldata zi,
        uint256 challenge,
        uint256[2] calldata runningCmE,
        uint256[2] calldata cmT,
        uint256[2] calldata runningCmW,
        uint256[2] calldata incomingCmW,
        uint256[12] calldata proof
    ) external view;
}

/// @title IMergeDeciderVerifier
/// @notice Sonobe-rendered Nova decider verifier for the N-input merge circuit.
/// @dev The signature is fixed by sonobe's CycleFold decider template with Nova's fold fragment.
///      The state is [tokenId, chainId, commitmentRoot, aspRoot, nullifierChain, signedChain, noteHash, remaining,
///      fee, feeRecipient].
///      Reverts for an invalid proof. With `i == 0` it returns once `z0 == zi`, without a proof.
interface IMergeDeciderVerifier {
    /// @notice Verify that `i` folded steps take `z0` to `zi`.
    function verifyDeciderProof(
        uint256 i,
        uint256[10] calldata z0,
        uint256[10] calldata zi,
        uint256 challenge,
        uint256[2] calldata runningCmE,
        uint256[2] calldata cmT,
        uint256[2] calldata runningCmW,
        uint256[2] calldata incomingCmW,
        uint256[12] calldata proof
    ) external view;
}
