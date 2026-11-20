// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice The sanctions list every zERC20 token checks.
interface IBlocklist {
    function isBlocked(address account) external view returns (bool);
}
