// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {Address} from "@openzeppelin/contracts/utils/Address.sol";
import {Clones} from "@openzeppelin/contracts/proxy/Clones.sol";
import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import {MessageHashUtils} from "@openzeppelin/contracts/utils/cryptography/MessageHashUtils.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {Initializable} from "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import {Ownable2StepUpgradeable} from "@openzeppelin/contracts-upgradeable/access/Ownable2StepUpgradeable.sol";
import {UUPSUpgradeable} from "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import {ZERC20} from "./ZERC20.sol";
import {ITokenRegistry} from "./interfaces/ITokenRegistry.sol";
import {FeeSchedule} from "./libs/FeeSchedule.sol";
import {Protocol} from "./libs/Protocol.sol";

/// @title DepositAddress
/// @notice A counterfactual address that wraps whatever underlying it receives into one burn address,
///         so a burn deposit needs nothing more than a plain transfer (e.g. a CEX withdrawal).
/// @dev Deployed by DepositAddressFactory as a CREATE2 clone whose immutable args are
///      `abi.encode(token, burnAddress, refundAddress, refundSigner, feeRecipient, fee, referrer, referralBps)`. The
///      resulting leaf is `Transfer(this, burnAddress, amount)`, so this address is what the ASP screens and where a
///      rage exit refunds to. The referrer is the app that handed the address out, which takes `referralBps` of what is
///      left after the fee; zero when no app does. Fee and referral are part of the address, so they are fixed when the
///      user is handed it.
///      Exactly one of `refundAddress` and `refundSigner` is set. A payer with no key, such as one paying from an
///      exchange, names a refund address, which anyone may refund to. A wallet names a signer instead, a key of its
///      own that appears nowhere else, and picks where a refund goes when it makes one: no deposit names the wallet's
///      account, and a refund needs no address chosen in advance.
contract DepositAddress {
    using SafeERC20 for IERC20;

    error NotRefundable();
    error Expired(uint256 deadline);
    error WrongSigner(address signer);

    receive() external payable {}

    /// @notice Wrap this address's whole underlying balance, less the fee and the referral, into the burn address, and
    ///         pay both to their recipients. Reverts unless the balance exceeds the fee. Permissionless.
    /// @dev The payments come last, and every flush pays out its whole balance: a flush re-entered from a recipient
    ///      either reverts or takes what the outer one still owes, which then reverts.
    function flush() external {
        (ZERC20 token, address burnAddress,,, address feeRecipient, uint256 fee, address referrer, uint16 referralBps) =
            _args();
        address asset = token.underlyingAsset();
        uint256 amount = _balance(asset) - fee;
        uint256 referral = Math.mulDiv(amount, referralBps, FeeSchedule.BPS_DENOMINATOR);
        amount -= referral;
        if (asset == Protocol.NATIVE) {
            token.wrap{value: amount}(amount, burnAddress);
        } else {
            IERC20(asset).forceApprove(address(token), amount);
            token.wrap(amount, burnAddress);
        }
        _send(asset, feeRecipient, fee);
        _send(asset, referrer, referral);
    }

    /// @notice Send this address's whole balance of `asset` (Protocol.NATIVE = native) to the refund
    ///         address: zERC20 minted here by a rage exit, underlying that cannot be wrapped, or a
    ///         wrong token. Permissionless, since the destination is fixed.
    function refund(address asset) external {
        (ZERC20 token,, address refundAddress,,,,,) = _args();
        require(refundAddress != address(0), NotRefundable());
        _refund(token, asset, refundAddress);
    }

    /// @notice Send this address's whole balance of `asset` to `to`, as the refund signer signed it by `deadline`.
    ///         Anyone may send the signature, and pays the gas.
    /// @dev The signature covers the chain and this address, so it moves nothing at the same address on another chain.
    ///      Sent again before `deadline`, it can only send more of `asset` to the same `to`.
    function refundTo(address asset, address to, uint256 deadline, bytes calldata signature) external {
        (ZERC20 token,,, address refundSigner,,,,) = _args();
        require(block.timestamp <= deadline, Expired(deadline));
        bytes32 digest = MessageHashUtils.toEthSignedMessageHash(
            keccak256(abi.encode(block.chainid, address(this), asset, to, deadline))
        );
        address signer = ECDSA.recover(digest, signature);
        require(signer == refundSigner, WrongSigner(signer));
        _refund(token, asset, to);
    }

    /// @dev Underlying that a flush can take is flushed instead, so a refund never undoes a deposit that can still be
    ///      made. Starving the flush of gas does not turn it into a refund: a flush that runs out hands back far less
    ///      gas than the transfer needs.
    function _refund(ZERC20 token, address asset, address to) private {
        if (asset == token.underlyingAsset()) {
            try this.flush() {
                return;
            } catch {}
        }
        _send(asset, to, _balance(asset));
    }

    function _balance(address asset) private view returns (uint256) {
        return asset == Protocol.NATIVE ? address(this).balance : IERC20(asset).balanceOf(address(this));
    }

    /// @dev A zero payment is not made at all, since some ERC-20s revert on a zero transfer.
    function _send(address asset, address to, uint256 value) private {
        if (value == 0) return;
        if (asset == Protocol.NATIVE) Address.sendValue(payable(to), value);
        else IERC20(asset).safeTransfer(to, value);
    }

    function _args()
        private
        view
        returns (
            ZERC20 token,
            address burnAddress,
            address refundAddress,
            address refundSigner,
            address feeRecipient,
            uint256 fee,
            address referrer,
            uint16 referralBps
        )
    {
        return abi.decode(
            Clones.fetchCloneArgs(address(this)), (ZERC20, address, address, address, address, uint256, address, uint16)
        );
    }
}

/// @title DepositAddressFactory
/// @notice Predicts and deploys DepositAddress clones.
/// @dev UUPS proxy; future implementations must retain this namespace. Every deposit address is derived
///      from this proxy's address and `depositImplementation`, so upgrades must never change the latter:
///      that would re-derive every address and strand funds already sent to undeployed ones. Upgrades
///      cannot touch funds at deployed clones (they have no privileged entry points), but an upgrade
///      that stops deploying would strand funds at undeployed ones, so upgrades are the admin's alone.
contract DepositAddressFactory layout at erc7201("zerc20.storage.DepositAddressFactory")
    is
    Initializable,
    Ownable2StepUpgradeable,
    UUPSUpgradeable
{
    /// @dev Complete project-owned storage. Append new fields at the end only.
    /// @custom:storage-location erc7201:zerc20.storage.DepositAddressFactory
    struct DepositAddressFactoryStorage {
        ITokenRegistry registry;
        // Set once at initialization; see the contract note.
        address depositImplementation;
    }

    DepositAddressFactoryStorage private _depositAddressFactoryStorage;

    /// @notice The most a referrer can take: 3% of what is left after the fee, the protocol fee's cap on a withdrawal.
    ///         A frontend picks its own rate, so this bounds what a user of any frontend can lose to it.
    uint16 public constant MAX_REFERRAL_BPS = 300;

    /// @dev `referrer` is indexed, so an app finds every address it handed out that took a deposit.
    event DepositAddressCreated(
        address indexed depositAddress,
        address indexed token,
        address burnAddress,
        address refundAddress,
        address refundSigner,
        address feeRecipient,
        uint256 fee,
        address indexed referrer,
        uint16 referralBps
    );

    error ZeroAddress();
    error UnknownToken(address token);
    error ReferralTooHigh(uint16 referralBps);

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() {
        _disableInitializers();
    }

    function initialize(address owner_, ITokenRegistry registry_) external initializer {
        require(address(registry_) != address(0), ZeroAddress());
        __Ownable_init(owner_);
        _depositAddressFactoryStorage =
            DepositAddressFactoryStorage({registry: registry_, depositImplementation: address(new DepositAddress())});
    }

    function registry() external view returns (ITokenRegistry) {
        return _depositAddressFactoryStorage.registry;
    }

    function depositImplementation() external view returns (address) {
        return _depositAddressFactoryStorage.depositImplementation;
    }

    function predict(
        ZERC20 token,
        address burnAddress,
        address refundAddress,
        address refundSigner,
        address feeRecipient,
        uint256 fee,
        address referrer,
        uint16 referralBps
    ) external view returns (address) {
        return Clones.predictDeterministicAddressWithImmutableArgs(
            _depositAddressFactoryStorage.depositImplementation,
            _args(token, burnAddress, refundAddress, refundSigner, feeRecipient, fee, referrer, referralBps),
            0
        );
    }

    /// @notice Deploy the deposit address if needed, then wrap everything it holds, less `fee` and the referral, into
    ///         `burnAddress`, pay `fee` to `feeRecipient`, and `referralBps` of the rest to `referrer`.
    ///         Permissionless; a relayer pays the gas.
    function flush(
        ZERC20 token,
        address burnAddress,
        address refundAddress,
        address refundSigner,
        address feeRecipient,
        uint256 fee,
        address referrer,
        uint16 referralBps
    ) external returns (address depositAddress) {
        address implementation = _depositAddressFactoryStorage.depositImplementation;
        bytes memory args =
            _args(token, burnAddress, refundAddress, refundSigner, feeRecipient, fee, referrer, referralBps);
        depositAddress = Clones.predictDeterministicAddressWithImmutableArgs(implementation, args, 0);
        if (depositAddress.code.length == 0) {
            Clones.cloneDeterministicWithImmutableArgs(implementation, args, 0);
            emit DepositAddressCreated(
                depositAddress,
                address(token),
                burnAddress,
                refundAddress,
                refundSigner,
                feeRecipient,
                fee,
                referrer,
                referralBps
            );
        }
        DepositAddress(payable(depositAddress)).flush();
    }

    function _authorizeUpgrade(address) internal override onlyOwner {}

    /// @dev Only registered tokens get an address, so a frontend cannot hand out one for a fake token. No address is
    ///      zero but the referrer of one that takes no referral, and the one of the refund address and signer that is
    ///      not used: a payment to a zero recipient would block every ERC-20 flush, or be lost as native.
    function _args(
        ZERC20 token,
        address burnAddress,
        address refundAddress,
        address refundSigner,
        address feeRecipient,
        uint256 fee,
        address referrer,
        uint16 referralBps
    ) private view returns (bytes memory) {
        require(burnAddress != address(0) && feeRecipient != address(0), ZeroAddress());
        require((refundAddress == address(0)) != (refundSigner == address(0)), ZeroAddress());
        require(referrer != address(0) || referralBps == 0, ZeroAddress());
        require(referralBps <= MAX_REFERRAL_BPS, ReferralTooHigh(referralBps));
        require(
            _depositAddressFactoryStorage.registry.tokenById(token.tokenId()) == address(token),
            UnknownToken(address(token))
        );
        return abi.encode(token, burnAddress, refundAddress, refundSigner, feeRecipient, fee, referrer, referralBps);
    }
}
