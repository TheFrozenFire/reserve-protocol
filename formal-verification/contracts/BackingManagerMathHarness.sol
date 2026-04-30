// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

import { FixLib, CEIL } from "./_relaxed/Fixed.sol";

/// Math-only harness for BackingManagerP1.forwardRevenue accounting.
/// Modelled in the Furnace harness shape (storage + constructor + non-pure
/// external entry points), since pure-function-only shape crashes solc-rocq's
/// optimizer.
///
/// Captures the Certora-audited line:
///     needed = basketsNeeded.mul(FIX_ONE + backingBuffer, CEIL)
/// and the per-asset surplus split.
contract BackingManagerMathHarness {
    using FixLib for uint192;

    // Stub state representing post-trade context the production function reads.
    uint192 public basketsHeldBottom;
    uint192 public backingBuffer;
    uint192 public basketsNeeded;
    uint256 public lastMintAmount;
    uint192 public lastNeeded;

    // Per-asset state for the surplus split.
    uint192 public quantity;
    uint192 public bal;
    uint8 public assetDecimals;
    uint256 public rTokenTotal;
    uint256 public rsrTotal;

    // Outputs of the most recent computeSurplusSplit call.
    uint256 public lastRsrAmount;
    uint256 public lastRTokenAmount;
    uint256 public lastDust;

    constructor(uint192 backingBuffer_) {
        backingBuffer = backingBuffer_;
    }

    /// Computes basket-buffer adjustment + needed quantity. Mirrors lines 220-225
    /// of BackingManagerP1::forwardRevenue.
    function computeNewBasketsAndNeeded(uint192 _basketsHeldBottom, uint192 _basketsNeeded)
        external
    {
        basketsHeldBottom = _basketsHeldBottom;
        basketsNeeded = _basketsNeeded;
        uint192 baskets = FixLib.div(_basketsHeldBottom, uint192(1e18) + backingBuffer);
        if (baskets > _basketsNeeded) {
            lastMintAmount = uint256(baskets) - uint256(_basketsNeeded);
            basketsNeeded = baskets;
        } else {
            lastMintAmount = 0;
        }
        // CEIL rounding — the post-#1283 mitigation.
        lastNeeded = FixLib.mul(basketsNeeded, uint192(1e18) + backingBuffer, CEIL);
    }

    /// Computes the per-asset surplus split for a single asset. Mirrors lines
    /// 240-260. Stores the split rather than returning it to fit the working
    /// harness shape.
    function computeSurplusSplit(
        uint192 _quantity,
        uint192 _bal,
        uint8 _decimals,
        uint256 _rTokenTotal,
        uint256 _rsrTotal
    ) external {
        quantity = _quantity;
        bal = _bal;
        assetDecimals = _decimals;
        rTokenTotal = _rTokenTotal;
        rsrTotal = _rsrTotal;

        uint192 req = FixLib.mul(lastNeeded, _quantity, CEIL);
        if (FixLib.lte(_bal, req)) {
            lastRsrAmount = 0;
            lastRTokenAmount = 0;
            lastDust = 0;
            return;
        }
        uint256 delta = FixLib.shiftl_toUint(FixLib.minus(_bal, req), int8(_decimals));
        uint256 totalShares = _rTokenTotal + _rsrTotal;
        require(totalShares > 0, "no shares");
        uint256 tokensPerShare = delta / totalShares;
        if (tokensPerShare == 0) {
            lastRsrAmount = 0;
            lastRTokenAmount = 0;
            lastDust = delta;
            return;
        }
        lastRsrAmount = tokensPerShare * _rsrTotal;
        lastRTokenAmount = tokensPerShare * _rTokenTotal;
        lastDust = delta - (lastRsrAmount + lastRTokenAmount);
    }
}
