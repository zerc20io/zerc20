// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Initializable} from "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import {Ownable2StepUpgradeable} from "@openzeppelin/contracts-upgradeable/access/Ownable2StepUpgradeable.sol";
import {UUPSUpgradeable} from "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import {BeaconProxy} from "@openzeppelin/contracts/proxy/beacon/BeaconProxy.sol";
import {UpgradeableBeacon} from "@openzeppelin/contracts/proxy/beacon/UpgradeableBeacon.sol";
import {CommitmentLedger} from "./CommitmentLedger.sol";
import {Verifier} from "./Verifier.sol";
import {ZERC20} from "./ZERC20.sol";
import {IBlocklist} from "./interfaces/IBlocklist.sol";
import {ITokenRegistry} from "./interfaces/ITokenRegistry.sol";
import {Protocol} from "./libs/Protocol.sol";

/// @title ZERC20Factory
/// @notice Owner-only registry: one ZERC20 beacon proxy per underlying asset (Protocol.NATIVE = native).
///         It is the sole source of truth for `tokenId -> token` used by the ledger and Verifier.
/// @dev UUPS proxy; future implementations must retain this namespace. The Factory owns the token
///      beacon, so the owner upgrades every token at once with `upgradeTokenBeacon`.
///      The owner chooses name, symbol and decimals verbatim, so it carries the display-impersonation
///      responsibility. Owned by the AccessManager: the operator creates and renames tokens, the admin
///      upgrades.
contract ZERC20Factory layout at erc7201("zerc20.storage.ZERC20Factory")
    is
    Initializable,
    Ownable2StepUpgradeable,
    UUPSUpgradeable,
    ITokenRegistry
{
    /// @dev Complete project-owned storage. Append new fields at the end only.
    /// @custom:storage-location erc7201:zerc20.storage.ZERC20Factory
    struct FactoryStorage {
        CommitmentLedger ledger;
        address verifier;
        IBlocklist blocklist;
        UpgradeableBeacon tokenBeacon;
        uint32 tokenCount;
        mapping(uint32 tokenId => address) tokenById;
        mapping(address underlying => uint32) tokenIdOf;
    }

    FactoryStorage private _factoryStorage;

    event TokenCreated(
        uint32 indexed tokenId,
        address indexed token,
        address indexed underlying,
        string name,
        string symbol,
        uint8 decimals
    );
    event TokenBeaconUpgraded(address indexed implementation);
    event TokenMetadataUpdated(uint32 indexed tokenId, string name, string symbol);

    error ZeroAddress();
    error TokenExists(address underlying);
    error UnknownToken(uint32 tokenId);
    error UnderlyingHasNoCode(address underlying);
    error DecimalsMismatch(uint8 expected, uint8 actual);
    error InvalidUnderlyingDecimals(address underlying);
    error EmptyMetadata();
    /// @dev `dependency` was initialized against a different Factory or Ledger.
    error Miswired(address dependency);

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    /// @param tokenImplementation_ Initial ZERC20 implementation behind the token beacon.
    /// @dev The ledger and Verifier are initialized first against this proxy's predicted address, and
    ///      none of the bindings can be changed later. Requiring them to point back here makes a wrong
    ///      prediction revert this deployment instead of leaving an unusable protocol.
    function initialize(
        address owner_,
        CommitmentLedger ledger_,
        address verifier_,
        IBlocklist blocklist_,
        address tokenImplementation_
    ) external initializer {
        require(
            address(ledger_) != address(0) && verifier_ != address(0) && address(blocklist_) != address(0),
            ZeroAddress()
        );
        require(address(ledger_.factory()) == address(this), Miswired(address(ledger_)));
        Verifier v = Verifier(verifier_);
        require(address(v.factory()) == address(this) && address(v.ledger()) == address(ledger_), Miswired(verifier_));
        __Ownable_init(owner_);

        FactoryStorage storage $ = _factoryStorage;
        $.ledger = ledger_;
        $.verifier = verifier_;
        $.blocklist = blocklist_;
        $.tokenBeacon = new UpgradeableBeacon(tokenImplementation_, address(this));
    }

    /// @dev `decimals` must equal the underlying's: 18 for the native asset, otherwise the value its
    ///      `decimals()` returns. Only an ERC-20 without `decimals()` (it is optional) takes the owner's
    ///      value as given. Balances are 1:1 raw units of the underlying, so this keeps amounts meaningful.
    function createToken(address underlying, string calldata name, string calldata symbol, uint8 decimals)
        external
        onlyOwner
        returns (address token)
    {
        FactoryStorage storage $ = _factoryStorage;
        require(underlying != address(0), ZeroAddress());
        require(bytes(name).length != 0 && bytes(symbol).length != 0, EmptyMetadata());
        _requireUnderlyingDecimals(underlying, decimals);
        require($.tokenIdOf[underlying] == 0, TokenExists(underlying));

        uint32 id = ++$.tokenCount;
        token = address(
            new BeaconProxy(
                address($.tokenBeacon),
                abi.encodeCall(
                    ZERC20.initialize, (name, symbol, decimals, id, underlying, $.ledger, $.verifier, $.blocklist)
                )
            )
        );
        $.tokenById[id] = token;
        $.tokenIdOf[underlying] = id;
        emit TokenCreated(id, token, underlying, name, symbol, decimals);
    }

    /// @notice Change a token's name and symbol. Decimals are fixed at creation.
    /// @dev Same display-impersonation responsibility as `createToken`.
    function setTokenMetadata(uint32 tokenId, string calldata name, string calldata symbol) external onlyOwner {
        address token = _factoryStorage.tokenById[tokenId];
        require(token != address(0), UnknownToken(tokenId));
        require(bytes(name).length != 0 && bytes(symbol).length != 0, EmptyMetadata());

        ZERC20(payable(token)).setMetadata(name, symbol);
        emit TokenMetadataUpdated(tokenId, name, symbol);
    }

    /// @notice Point every token at a new ZERC20 implementation.
    function upgradeTokenBeacon(address newImplementation) external onlyOwner {
        _factoryStorage.tokenBeacon.upgradeTo(newImplementation);
        emit TokenBeaconUpgraded(newImplementation);
    }

    function ledger() external view returns (CommitmentLedger) {
        return _factoryStorage.ledger;
    }

    function verifier() external view returns (address) {
        return _factoryStorage.verifier;
    }

    function blocklist() external view returns (IBlocklist) {
        return _factoryStorage.blocklist;
    }

    function tokenBeacon() external view returns (UpgradeableBeacon) {
        return _factoryStorage.tokenBeacon;
    }

    function tokenCount() external view returns (uint32) {
        return _factoryStorage.tokenCount;
    }

    function tokenById(uint32 tokenId) external view returns (address) {
        return _factoryStorage.tokenById[tokenId];
    }

    function tokenIdOf(address underlying) external view returns (uint32) {
        return _factoryStorage.tokenIdOf[underlying];
    }

    function _authorizeUpgrade(address) internal override onlyOwner {}

    function _requireUnderlyingDecimals(address underlying, uint8 decimals) private view {
        if (underlying == Protocol.NATIVE) {
            require(decimals == 18, DecimalsMismatch(18, decimals));
            return;
        }
        require(underlying.code.length != 0, UnderlyingHasNoCode(underlying));

        (bool ok, bytes memory data) = underlying.staticcall(abi.encodeWithSignature("decimals()"));
        if (!ok || data.length < 32) return; // no decimals(): the owner's value stands

        uint256 reported = abi.decode(data, (uint256));
        require(reported <= type(uint8).max, InvalidUnderlyingDecimals(underlying));
        // forge-lint: disable-next-line(unsafe-typecast)
        require(decimals == uint8(reported), DecimalsMismatch(uint8(reported), decimals));
    }
}
