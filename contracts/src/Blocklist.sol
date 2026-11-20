// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Initializable} from "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import {Ownable2StepUpgradeable} from "@openzeppelin/contracts-upgradeable/access/Ownable2StepUpgradeable.sol";
import {UUPSUpgradeable} from "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import {IBlocklist} from "./interfaces/IBlocklist.sol";

/// @title Blocklist
/// @notice Shared chain-local sanctions registry referenced by every zERC20 token.
/// @dev UUPS proxy; future implementations must retain this namespace. Owned by the AccessManager: the
///      operator edits the list, the admin upgrades. Writes are idempotent and always emit, so the event
///      log is a replayable audit trail.
contract Blocklist layout at erc7201("zerc20.storage.Blocklist")
    is
    Initializable,
    Ownable2StepUpgradeable,
    UUPSUpgradeable,
    IBlocklist
{
    /// @dev Complete project-owned storage. Append new fields at the end only.
    /// @custom:storage-location erc7201:zerc20.storage.Blocklist
    struct BlocklistStorage {
        mapping(address account => bool) blocked;
    }

    BlocklistStorage private _blocklistStorage;

    event BlocklistUpdated(address indexed account, bool blocked);

    error ZeroAddress();

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    function initialize(address owner_) external initializer {
        __Ownable_init(owner_);
    }

    function isBlocked(address account) external view override returns (bool) {
        return _blocklistStorage.blocked[account];
    }

    function setBlocked(address[] calldata accounts, bool blocked) external onlyOwner {
        for (uint256 i; i < accounts.length; ++i) {
            require(accounts[i] != address(0), ZeroAddress());
            _blocklistStorage.blocked[accounts[i]] = blocked;
            emit BlocklistUpdated(accounts[i], blocked);
        }
    }

    function _authorizeUpgrade(address) internal override onlyOwner {}
}
