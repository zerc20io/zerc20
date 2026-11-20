// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {IMergeDeciderVerifier, IRootDeciderVerifier} from "../../src/interfaces/INovaDeciderVerifier.sol";
import {IJoinSplitVerifier, IRageExitVerifier} from "../../src/interfaces/IPrivateProofVerifier.sol";

/// @dev Accepts every proof. Tests, and the indexer's e2e fixture, which needs real events without real proofs.
contract AcceptAll is IJoinSplitVerifier, IRageExitVerifier, IMergeDeciderVerifier, IRootDeciderVerifier {
    function verifyProof(uint256[2] calldata, uint256[2][2] calldata, uint256[2] calldata, uint256[11] calldata)
        external
        pure
        returns (bool)
    {
        return true;
    }

    function verifyProof(uint256[2] calldata, uint256[2][2] calldata, uint256[2] calldata, uint256[4] calldata)
        external
        pure
        returns (bool)
    {
        return true;
    }
    function verifyDeciderProof(
        uint256,
        uint256[10] calldata,
        uint256[10] calldata,
        uint256,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[12] calldata
    ) external pure {}
    function verifyDeciderProof(
        uint256,
        uint256[3] calldata,
        uint256[3] calldata,
        uint256,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[12] calldata
    ) external pure {}
}
