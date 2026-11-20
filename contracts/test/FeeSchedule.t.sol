// SPDX-License-Identifier: MIT
pragma solidity 0.8.37;

import {Test} from "forge-std/Test.sol";
import {FeeSchedule} from "../src/libs/FeeSchedule.sol";
import {Protocol} from "../src/libs/Protocol.sol";

/// @dev A schedule in storage, as the Verifier keeps one per token, with `set` taking calldata tiers.
contract FeeScheduleHarness {
    using FeeSchedule for FeeSchedule.Schedule;

    FeeSchedule.Schedule private schedule;

    function set(address to, FeeSchedule.Tier[] calldata tiers) external returns (bool) {
        return schedule.set(to, tiers);
    }

    function quote(uint256 amount) external view returns (uint256) {
        return schedule.quote(amount);
    }

    function recipient() external view returns (address) {
        return schedule.recipient;
    }

    function tierCount() external view returns (uint256) {
        return schedule.tiers.length;
    }
}

contract FeeScheduleTest is Test {
    FeeScheduleHarness fees;
    address recipient = address(0xFEE);

    function setUp() public {
        fees = new FeeScheduleHarness();
    }

    function _tiers(uint256[3] memory mins, uint16[3] memory bps, uint256 n)
        internal
        pure
        returns (FeeSchedule.Tier[] memory tiers)
    {
        tiers = new FeeSchedule.Tier[](n);
        for (uint256 i; i < n; ++i) {
            tiers[i] = FeeSchedule.Tier({minAmount: mins[i], feeBps: bps[i]});
        }
    }

    /// @dev floor(amount * bps / 10_000), computed apart from the library's mulDiv and without overflowing.
    function _rate(uint256 amount, uint16 bps) internal pure returns (uint256) {
        return amount / 10_000 * bps + amount % 10_000 * bps / 10_000;
    }

    function test_noScheduleChargesNothing() public view {
        assertEq(fees.quote(0), 0);
        assertEq(fees.quote(Protocol.AMOUNT_BOUND - 1), 0);
    }

    function test_theLastTierReachedAppliesToTheWholeAmount() public {
        fees.set(recipient, _tiers([uint256(0), 10e18, 100e18], [uint16(100), 50, 10], 3));
        assertEq(fees.quote(5e18), 0.05e18);
        assertEq(fees.quote(10e18 - 1), _rate(10e18 - 1, 100));
        assertEq(fees.quote(10e18), 0.05e18); // the lower bound is inclusive
        assertEq(fees.quote(250e18), 0.25e18);
        assertEq(fees.quote(Protocol.AMOUNT_BOUND - 1), _rate(Protocol.AMOUNT_BOUND - 1, 10));
    }

    function test_feesRoundDown() public {
        fees.set(recipient, _tiers([uint256(0), 0, 0], [uint16(1), 0, 0], 1));
        assertEq(fees.quote(9_999), 0);
        assertEq(fees.quote(10_000), 1);
        assertEq(fees.quote(19_999), 1);
    }

    function test_setReplacesEveryTierAndTheRecipient() public {
        fees.set(recipient, _tiers([uint256(0), 10, 20], [uint16(300), 200, 100], 3));
        assertTrue(fees.set(address(0xBEEF), _tiers([uint256(0), 0, 0], [uint16(50), 0, 0], 1)));
        assertEq(fees.tierCount(), 1);
        assertEq(fees.recipient(), address(0xBEEF));
        assertEq(fees.quote(1e18), 0.005e18); // no tier of the old schedule survives
    }

    function test_aScheduleWithoutAChargeNeedsNoRecipient() public {
        assertFalse(fees.set(address(0), _tiers([uint256(0), 10, 0], [uint16(0), 0, 0], 2)));
        assertEq(fees.quote(1e18), 0);
    }

    function test_rejectsMalformedSchedules() public {
        uint256 bound = Protocol.AMOUNT_BOUND;
        _expectInvalid(recipient, new FeeSchedule.Tier[](0)); // empty
        _expectInvalid(recipient, new FeeSchedule.Tier[](FeeSchedule.MAX_TIERS + 1)); // too many
        _expectInvalid(recipient, _tiers([uint256(1), 0, 0], [uint16(10), 0, 0], 1)); // does not start at 0
        _expectInvalid(recipient, _tiers([uint256(0), 5, 5], [uint16(10), 5, 1], 3)); // bounds repeat
        _expectInvalid(recipient, _tiers([uint256(0), 5, 4], [uint16(10), 5, 1], 3)); // bounds decrease
        _expectInvalid(recipient, _tiers([uint256(0), bound, 0], [uint16(10), 5, 0], 2)); // bound unreachable
        _expectInvalid(recipient, _tiers([uint256(0), 0, 0], [FeeSchedule.MAX_FEE_BPS + 1, 0, 0], 1)); // above cap
        _expectInvalid(recipient, _tiers([uint256(0), 100, 0], [uint16(0), 300, 0], 2)); // a rate that rises
        _expectInvalid(address(0), _tiers([uint256(0), 10, 0], [uint16(1), 0, 0], 2)); // a fee with nowhere to go
    }

    function _expectInvalid(address to, FeeSchedule.Tier[] memory tiers) internal {
        vm.expectRevert(FeeSchedule.InvalidFeeConfig.selector);
        fees.set(to, tiers);
    }

    function test_acceptsTheLimits() public {
        FeeSchedule.Tier[] memory tiers = new FeeSchedule.Tier[](FeeSchedule.MAX_TIERS);
        for (uint256 i; i < tiers.length; ++i) {
            tiers[i] = FeeSchedule.Tier({minAmount: i, feeBps: FeeSchedule.MAX_FEE_BPS});
        }
        tiers[tiers.length - 1].minAmount = Protocol.AMOUNT_BOUND - 1;
        fees.set(recipient, tiers);
        assertEq(fees.tierCount(), FeeSchedule.MAX_TIERS);
        assertEq(fees.quote(10_000), 300);
    }

    /// @dev Up to 16 tiers with strictly increasing bounds and rates that never rise.
    function _fuzzedSchedule(uint256 n, uint256[16] memory gaps, uint16[16] memory bps)
        internal
        returns (FeeSchedule.Tier[] memory tiers)
    {
        n = bound(n, 1, FeeSchedule.MAX_TIERS);
        tiers = new FeeSchedule.Tier[](n);
        uint16 rate = FeeSchedule.MAX_FEE_BPS;
        uint256 minAmount;
        for (uint256 i; i < n; ++i) {
            // 16 gaps below 2^243 keep every bound below AMOUNT_BOUND = 2^248.
            if (i != 0) minAmount += bound(gaps[i], 1, uint256(1) << 243);
            rate = uint16(bound(bps[i], 0, rate));
            tiers[i] = FeeSchedule.Tier({minAmount: minAmount, feeBps: rate});
        }
        fees.set(recipient, tiers);
    }

    function testFuzz_eachTierStartsAtItsBound(uint256 n, uint256[16] memory gaps, uint16[16] memory bps) public {
        FeeSchedule.Tier[] memory tiers = _fuzzedSchedule(n, gaps, bps);
        for (uint256 i; i < tiers.length; ++i) {
            uint256 start = tiers[i].minAmount;
            assertEq(fees.quote(start), _rate(start, tiers[i].feeBps));
            if (i != 0) assertEq(fees.quote(start - 1), _rate(start - 1, tiers[i - 1].feeBps));
        }
    }

    function testFuzz_aLargerAmountNeverPaysOutLess(
        uint256 n,
        uint256[16] memory gaps,
        uint16[16] memory bps,
        uint256 amount
    ) public {
        FeeSchedule.Tier[] memory tiers = _fuzzedSchedule(n, gaps, bps);
        // at a tier's bound, where the rate changes, as often as anywhere else
        uint256 i = amount % tiers.length;
        amount = i != 0 && amount % 2 == 0 ? tiers[i].minAmount - 1 : bound(amount, 0, Protocol.AMOUNT_BOUND - 2);
        assertGe(amount + 1 - fees.quote(amount + 1), amount - fees.quote(amount));
    }

    function testFuzz_quoteNeverExceedsTheCap(uint256 n, uint256[16] memory gaps, uint16[16] memory bps, uint256 amount)
        public
    {
        _fuzzedSchedule(n, gaps, bps);
        amount = bound(amount, 0, Protocol.AMOUNT_BOUND - 1);
        assertLe(fees.quote(amount), _rate(amount, FeeSchedule.MAX_FEE_BPS));
    }
}
