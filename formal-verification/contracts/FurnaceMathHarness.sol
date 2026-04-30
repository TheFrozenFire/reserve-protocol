// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

import { FixLib } from "./_relaxed/Fixed.sol";

/// Math-only harness for FurnaceP1's melt logic.
///
/// Mirrors the body of `_melt`/`melt` from contracts/p1/Furnace.sol but
/// strips the ComponentP1 inheritance (which transitively pulls OZ
/// Upgradeable + cryptography helpers and crashes solc-rocq's optimizer).
///
/// What's kept (faithful to production):
///   - MAX_RATIO constant, ratio storage
///   - payoutRatio = FIX_ONE - powu(FIX_ONE - ratio, numPeriods)
///   - amount = payoutRatio.mulu_toUint(lastPayoutBal)
///   - lastPayout, lastPayoutBal accounting
///
/// What's stubbed (not load-bearing for the math we want to prove):
///   - RToken contract: replaced with a simple uint256 balance var
///   - melt(amount) call: just decrements the balance
///   - Governance + initialization
contract FurnaceMathHarness {
    using FixLib for uint192;

    uint192 public constant MAX_RATIO = 1e14;

    uint192 public ratio;
    uint48 public lastPayout;
    uint256 public lastPayoutBal;
    uint256 public rTokenBalance; // stub for rToken.balanceOf(this)

    constructor(uint192 ratio_, uint256 initialRTokenBalance) {
        require(ratio_ <= MAX_RATIO, "ratio above MAX");
        ratio = ratio_;
        lastPayout = uint48(block.timestamp);
        lastPayoutBal = initialRTokenBalance;
        rTokenBalance = initialRTokenBalance;
    }

    /// Verbatim port of Furnace.melt (sans the actual melt() external call).
    function melt() public {
        if (uint48(block.timestamp) < uint64(lastPayout + 1)) return;

        uint48 numPeriods = uint48((block.timestamp) - lastPayout);
        uint192 payoutRatio = FixLib.minus(uint192(1e18), FixLib.powu(FixLib.minus(uint192(1e18), ratio), numPeriods));
        uint256 amount = FixLib.mulu_toUint(payoutRatio, lastPayoutBal);

        lastPayout += numPeriods;
        lastPayoutBal = rTokenBalance - amount;
        if (amount != 0) {
            // production: rToken.melt(amount); we just decrement.
            rTokenBalance -= amount;
        }
    }

    /// Pure helper exposed for proof: the closed-form payoutRatio at (ratio, N).
    /// Lets the Rocq layer state and prove identities about the formula
    /// without needing to model the melt state-transition.
    function computePayoutRatio(uint192 r, uint48 numPeriods) external pure returns (uint192) {
        return FixLib.minus(uint192(1e18), FixLib.powu(FixLib.minus(uint192(1e18), r), numPeriods));
    }
}
