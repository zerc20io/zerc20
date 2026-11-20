// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice The Verifier's stop switch, which a token reads on every balance change.
interface ITokenStop {
    function tokenStopped(uint32 tokenId) external view returns (bool);
}
