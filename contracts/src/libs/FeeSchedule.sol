// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {Protocol} from "./Protocol.sol";

/// @notice Tiered fee schedule: the fee rate depends on the size of the amount.
/// @dev A schedule is a list of tiers sorted by `minAmount`. The rate that applies is the one of the
///      LAST tier whose `minAmount` the amount reaches (lower bound inclusive). The rate is applied to
///      the whole amount, not marginally per band.
///
///      Example (minAmount -> feeBps):
///          tiers = [ (0 -> 100), (10e18 -> 50), (100e18 -> 10) ]
///
///          amount         applies    fee
///          5e18           tier 0     1.00%  -> 0.05e18
///          10e18          tier 1     0.50%  -> 0.05e18   (10e18 reaches tier 1's bound)
///          250e18         tier 2     0.10%  -> 0.25e18
///
///      Tiers therefore let large amounts pay a lower rate. A rate never rises from one tier to the
///      next: applied to the whole amount, a higher one would pay out less for a larger amount. A
///      single tier `(0 -> bps)` is a flat fee; no schedule at all means no fee.
library FeeSchedule {
    uint256 internal constant BPS_DENOMINATOR = 10_000; // feeBps of 10_000 is 100%
    /// @dev 3%. Notes leave only through a fee-charging withdrawal, so an uncapped fee could take them;
    ///      only a Verifier upgrade can raise this.
    uint16 internal constant MAX_FEE_BPS = 300;
    uint256 internal constant MAX_TIERS = 16;

    /// @param minAmount Smallest amount (inclusive, raw token units) this tier applies to.
    /// @param feeBps Fee rate in basis points (1 bps = 0.01%).
    struct Tier {
        uint256 minAmount;
        uint16 feeBps;
    }

    /// @param recipient Account the fees are owed to.
    /// @param tiers Fee tiers sorted by strictly increasing `minAmount`, the first being 0, with rates that never rise.
    struct Schedule {
        address recipient;
        Tier[] tiers;
    }

    error InvalidFeeConfig();

    /// @dev Replaces `s` with the given recipient and tiers. Returns whether any tier charges a fee,
    ///      so the caller can apply recipient-specific checks.
    function set(Schedule storage s, address recipient, Tier[] calldata tiers) internal returns (bool charges) {
        charges = _validate(recipient, tiers);

        s.recipient = recipient;
        delete s.tiers;
        for (uint256 i; i < tiers.length; ++i) {
            s.tiers.push(tiers[i]);
        }
    }

    /// @dev Fee owed on a gross `amount`; zero when no schedule is set.
    function quote(Schedule storage s, uint256 amount) internal view returns (uint256) {
        Tier[] storage tiers = s.tiers;

        // Tiers are sorted, so stop at the first bound the amount does not reach.
        uint16 feeBps;
        for (uint256 i; i < tiers.length && amount >= tiers[i].minAmount; ++i) {
            feeBps = tiers[i].feeBps;
        }
        return Math.mulDiv(amount, feeBps, BPS_DENOMINATOR);
    }

    function _validate(address recipient, Tier[] calldata tiers) private pure returns (bool charges) {
        require(tiers.length != 0 && tiers.length <= MAX_TIERS, InvalidFeeConfig());

        uint256 previousMin;
        // Starting from the cap, rates that never rise all stay within it.
        uint16 previousBps = MAX_FEE_BPS;
        for (uint256 i; i < tiers.length; ++i) {
            Tier calldata tier = tiers[i];
            // The first tier must cover every amount (starts at 0); later bounds strictly increase.
            bool orderedBound = i == 0 ? tier.minAmount == 0 : tier.minAmount > previousMin;
            require(
                orderedBound && tier.minAmount < Protocol.AMOUNT_BOUND && tier.feeBps <= previousBps, InvalidFeeConfig()
            );

            charges = charges || tier.feeBps != 0;
            previousMin = tier.minAmount;
            previousBps = tier.feeBps;
        }
        // A fee needs somewhere to go.
        require(!charges || recipient != address(0), InvalidFeeConfig());
    }
}
