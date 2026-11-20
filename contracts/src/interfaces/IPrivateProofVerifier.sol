// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Groth16 proof data emitted by snarkjs-compatible Circom provers.
/// @param pA G1 proof element A.
/// @param pB G2 proof element B in the Solidity verifier's coordinate order.
/// @param pC G1 proof element C.
struct Groth16Proof {
    uint256[2] pA;
    uint256[2][2] pB;
    uint256[2] pC;
}

/// @title IJoinSplitVerifier
/// @notice Verifier for the 2-input, 2-note-output, 1-withdraw private transaction circuit.
/// @dev Public-signal order is consensus-critical: outputs precede inputs exactly as emitted by Circom.
interface IJoinSplitVerifier {
    /// @notice Verify a JoinSplit Groth16 proof.
    /// @param pA G1 proof element A.
    /// @param pB G2 proof element B.
    /// @param pC G1 proof element C.
    /// @param publicSignals Eleven circuit public signals in the protocol-defined order.
    /// @return valid True only when the proof verifies for the supplied public signals.
    function verifyProof(
        uint256[2] calldata pA,
        uint256[2][2] calldata pB,
        uint256[2] calldata pC,
        uint256[11] calldata publicSignals
    ) external view returns (bool);
}

/// @title IRageExitVerifier
/// @notice Verifier for the ASP-liveness fallback Rage Exit circuit.
/// @dev Public signals: [nullifier, chainId, commitmentIndex, burnAddress]. The contract authenticates the
///      deposit commitment and its index on the ledger hash chain; the proof shows burn-address ownership.
interface IRageExitVerifier {
    /// @notice Verify a Rage Exit Groth16 proof.
    /// @param pA G1 proof element A.
    /// @param pB G2 proof element B.
    /// @param pC G1 proof element C.
    /// @param publicSignals Four circuit public signals in the protocol-defined order.
    /// @return valid True only when the proof verifies for the supplied public signals.
    function verifyProof(
        uint256[2] calldata pA,
        uint256[2][2] calldata pB,
        uint256[2] calldata pC,
        uint256[4] calldata publicSignals
    ) external view returns (bool);
}
