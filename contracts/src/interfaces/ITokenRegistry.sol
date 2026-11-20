// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice The token for each token id: the factory's registry, which the ledger and Verifier trust.
interface ITokenRegistry {
    function tokenById(uint32 tokenId) external view returns (address);
}
