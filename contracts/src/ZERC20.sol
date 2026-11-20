// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {Initializable} from "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import {ERC20Upgradeable} from "@openzeppelin/contracts-upgradeable/token/ERC20/ERC20Upgradeable.sol";
import {
    ERC20PermitUpgradeable
} from "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/ERC20PermitUpgradeable.sol";
import {
    ERC3009Upgradeable
} from "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/draft-ERC3009Upgradeable.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {CommitmentLedger} from "./CommitmentLedger.sol";
import {IBlocklist} from "./interfaces/IBlocklist.sol";
import {ITokenStop} from "./interfaces/ITokenStop.sol";
import {Protocol} from "./libs/Protocol.sol";

/// @title ZERC20
/// @dev Deployed as a beacon proxy per token; the Factory owner upgrades all tokens through the beacon.
///      Future implementations must retain this namespace.
/// @notice Wrapper token (1:1 over an ERC-20 or native asset). Every transfer is appended to the
///         commitment ledger; the Verifier can mint public amounts and append private note hashes.
contract ZERC20 layout at erc7201("zerc20.storage.ZERC20")
    is
    Initializable,
    ERC20Upgradeable,
    ERC20PermitUpgradeable,
    ERC3009Upgradeable,
    ReentrancyGuardTransient
{
    using SafeERC20 for IERC20;

    // forge-lint: disable-next-item(pascal-case-struct) the token's name
    /// @dev Complete project-owned storage. Append new fields at the end only.
    /// @custom:storage-location erc7201:zerc20.storage.ZERC20
    struct ZERC20Storage {
        // Protocol.NATIVE means the native asset.
        address underlyingAsset;
        uint32 tokenId;
        uint8 decimals;
        CommitmentLedger ledger;
        address verifier;
        IBlocklist blocklist;
        // The Factory that created this token; the only caller allowed to change its metadata.
        address factory;
        // Kept here rather than in ERC20Upgradeable's private storage so they can be updated.
        string name;
        string symbol;
    }

    ZERC20Storage private _zerc20Storage;

    event Wrapped(address indexed caller, address indexed receiver, uint256 amount);
    event Unwrapped(address indexed caller, address indexed receiver, uint256 amount);
    event MetadataUpdated(string name, string symbol);

    error ZeroAddress();
    error ZeroAmount();
    error InvalidAmount(uint256 amount);
    error InvalidNoteHash(uint256 noteHash);
    error Unauthorized(address caller);
    error BlockedAddress(address account);
    error InvalidNativeValue(uint256 expected, uint256 actual);
    error InvalidUnderlyingDelta(uint256 expected, uint256 actual);
    error NativeTransferFailed(address receiver, uint256 amount);
    error DirectNativeTransfer();
    error TokenStopped(uint32 tokenId);

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    /// @dev Called by the Factory through the BeaconProxy constructor, so `msg.sender` is the Factory.
    function initialize(
        string memory name_,
        string memory symbol_,
        uint8 decimals_,
        uint32 tokenId_,
        address underlyingAsset_,
        CommitmentLedger ledger_,
        address verifier_,
        IBlocklist blocklist_
    ) external initializer {
        require(
            address(ledger_) != address(0) && verifier_ != address(0) && address(blocklist_) != address(0),
            ZeroAddress()
        );
        _zerc20Storage = ZERC20Storage({
            underlyingAsset: underlyingAsset_,
            tokenId: tokenId_,
            decimals: decimals_,
            ledger: ledger_,
            verifier: verifier_,
            blocklist: blocklist_,
            factory: msg.sender,
            name: name_,
            symbol: symbol_
        });
    }

    modifier onlyVerifier() {
        _onlyVerifier();
        _;
    }

    function _onlyVerifier() private view {
        require(msg.sender == _zerc20Storage.verifier, Unauthorized(msg.sender));
    }

    /// @dev Native value is only accepted through `wrap`, where it is accounted for.
    receive() external payable {
        revert DirectNativeTransfer();
    }

    function name() public view override returns (string memory) {
        return _zerc20Storage.name;
    }

    function symbol() public view override returns (string memory) {
        return _zerc20Storage.symbol;
    }

    /// @dev Fixed for the token's lifetime: balances are 1:1 raw units of the underlying asset.
    function decimals() public view override returns (uint8) {
        return _zerc20Storage.decimals;
    }

    // forge-lint: disable-next-item(mixed-case-function) OpenZeppelin's name
    /// @dev The EIP-712 domain follows the current name, so a rename invalidates outstanding signatures.
    function _EIP712Name() internal view override returns (string memory) {
        return _zerc20Storage.name;
    }

    // forge-lint: disable-next-item(mixed-case-function) OpenZeppelin's name
    function _EIP712Version() internal pure override returns (string memory) {
        return "1";
    }

    function factory() external view returns (address) {
        return _zerc20Storage.factory;
    }

    /// @notice Rename the token (Factory only; the Factory gates it to its owner).
    function setMetadata(string calldata name_, string calldata symbol_) external {
        ZERC20Storage storage $ = _zerc20Storage;
        require(msg.sender == $.factory, Unauthorized(msg.sender));
        $.name = name_;
        $.symbol = symbol_;
        emit MetadataUpdated(name_, symbol_);
    }

    function tokenId() external view returns (uint32) {
        return _zerc20Storage.tokenId;
    }

    /// @dev Protocol.NATIVE means the native asset.
    function underlyingAsset() external view returns (address) {
        return _zerc20Storage.underlyingAsset;
    }

    function ledger() external view returns (CommitmentLedger) {
        return _zerc20Storage.ledger;
    }

    function verifier() external view returns (address) {
        return _zerc20Storage.verifier;
    }

    function blocklist() external view returns (IBlocklist) {
        return _zerc20Storage.blocklist;
    }

    function transfer(address to, uint256 value) public override nonReentrant returns (bool) {
        return super.transfer(to, value);
    }

    /// @custom:blocklist The caller is checked too: as the spender it picks `to` and the amount.
    function transferFrom(address from, address to, uint256 value) public override nonReentrant returns (bool) {
        _requireNotBlocked(msg.sender);
        return super.transferFrom(from, to, value);
    }

    /// @dev Guarded like `transfer`.
    /// @custom:blocklist Unlike `transferFrom`, the caller is not checked: it only relays what `from` signed
    ///                   (`to` and amount included), and `_update` checks `from` and `to`.
    function _transferWithAuthorization(
        address from,
        address to,
        uint256 value,
        uint256 validAfter,
        uint256 validBefore,
        bytes32 nonce
    ) internal override nonReentrant {
        super._transferWithAuthorization(from, to, value, validAfter, validBefore, nonce);
    }

    // ---- public liquidity -------------------------------------------------------------------

    /// @notice Deposit exactly `amount` of the underlying asset and mint zERC20 to `receiver`.
    function wrap(uint256 amount, address receiver) external payable nonReentrant {
        _requireNonZero(receiver, amount);
        _collect(amount);
        // Mint to the caller and forward so a deposit to a burn address becomes a Transfer leaf
        // with a real, screenable and refundable `from` (mints themselves are not committed).
        _mint(msg.sender, amount);
        if (receiver != msg.sender) _transfer(msg.sender, receiver, amount);
        emit Wrapped(msg.sender, receiver, amount);
    }

    /// @notice Burn `amount` and release exactly that much underlying to `receiver`.
    function unwrap(uint256 amount, address receiver) external nonReentrant {
        _requireNonZero(receiver, amount);
        _requireNotBlocked(receiver);
        _burn(msg.sender, amount);
        _release(receiver, amount);
        emit Unwrapped(msg.sender, receiver, amount);
    }

    // ---- Verifier-only ----------------------------------------------------------------------

    /// @notice Append a private output note hash to the ledger (Verifier only).
    function commitNote(uint256 noteHash) external onlyVerifier nonReentrant returns (uint64) {
        require(noteHash < Protocol.FIELD_MODULUS, InvalidNoteHash(noteHash));
        return _commit(Protocol.NOTE_HASH_TAG, noteHash, 0, 0);
    }

    /// @notice Pay out a proof-authorized amount (Verifier only): minted as zERC20, or with `asUnderlying` released as
    ///         the underlying, so the recipient needs no gas to unwrap it.
    function payOut(address recipient, uint256 amount, bool asUnderlying) external onlyVerifier nonReentrant {
        _requireNonZero(recipient, amount);
        if (!asUnderlying) {
            _mint(recipient, amount);
            return;
        }
        // no balance changes, so `_update`'s checks are made here
        _requireNotStopped();
        _requireNotBlocked(recipient);
        _release(recipient, amount);
        emit Unwrapped(msg.sender, recipient, amount);
    }

    // ---- internals --------------------------------------------------------------------------

    /// @dev Every transfer between two real accounts is appended to the ledger. A pause of the Verifier or of
    ///      this token stops every balance change here: wraps, unwraps, transfers and Verifier mints and releases.
    function _update(address from, address to, uint256 amount) internal override {
        _requireNotStopped();
        require(amount < Protocol.AMOUNT_BOUND, InvalidAmount(amount));
        _requireNotBlocked(from);
        _requireNotBlocked(to);
        super._update(from, to, amount);
        // Only transfers between two real accounts become leaves. Mints (from == 0) and burns
        // (to == 0) can never be opened as a burn deposit, and zero transfers need no capacity.
        if (from == address(0) || to == address(0) || amount == 0) return;

        _commit(Protocol.TRANSFER_TAG, uint256(uint160(from)), uint256(uint160(to)), amount);
    }

    function _commit(uint32 tag, uint256 f1, uint256 f2, uint256 f3) private returns (uint64) {
        ZERC20Storage storage $ = _zerc20Storage;
        return $.ledger.commit([Protocol.encode(tag, $.tokenId), f1, f2, f3]);
    }

    function _requireNotStopped() private view {
        ZERC20Storage storage $ = _zerc20Storage;
        require(!ITokenStop($.verifier).tokenStopped($.tokenId), TokenStopped($.tokenId));
    }

    function isBlocked(address account) external view returns (bool) {
        return _zerc20Storage.blocklist.isBlocked(account);
    }

    /// @dev Exempts the Verifier (fee escrow), which is protocol infrastructure, and the zero address, which
    ///      stands for mint/burn legs.
    function _requireNotBlocked(address account) private view {
        ZERC20Storage storage $ = _zerc20Storage;
        if (account == address(0) || account == $.verifier) return;
        require(!$.blocklist.isBlocked(account), BlockedAddress(account));
    }

    function _requireNonZero(address account, uint256 amount) private pure {
        require(account != address(0), ZeroAddress());
        require(amount != 0, ZeroAmount());
    }

    function _collect(uint256 amount) private {
        address asset = _zerc20Storage.underlyingAsset;
        if (asset == Protocol.NATIVE) {
            require(msg.value == amount, InvalidNativeValue(amount, msg.value));
            return;
        }
        require(msg.value == 0, InvalidNativeValue(0, msg.value));
        uint256 before = IERC20(asset).balanceOf(address(this));
        IERC20(asset).safeTransferFrom(msg.sender, address(this), amount);
        uint256 received = IERC20(asset).balanceOf(address(this)) - before;
        require(received == amount, InvalidUnderlyingDelta(amount, received));
    }

    function _release(address receiver, uint256 amount) private {
        address asset = _zerc20Storage.underlyingAsset;
        if (asset == Protocol.NATIVE) {
            (bool ok,) = payable(receiver).call{value: amount}("");
            require(ok, NativeTransferFailed(receiver, amount));
            return;
        }
        uint256 before = IERC20(asset).balanceOf(address(this));
        IERC20(asset).safeTransfer(receiver, amount);
        uint256 spent = before - IERC20(asset).balanceOf(address(this));
        require(spent == amount, InvalidUnderlyingDelta(amount, spent));
    }
}
