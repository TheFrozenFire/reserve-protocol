// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

/// Math-only harness for DistributorP1's `distribute` accounting.
///
/// Strips ComponentP1 inheritance and EnumerableSet machinery. Models the
/// distribution table as a flat array of (rTokenDist, rsrDist) pairs and
/// exposes the same per-destination amount math the production contract uses:
///
///     tokensPerShare = amount / totalShares     (floor)
///     transferAmt[i] = tokensPerShare * numberOfShares[i]
///
/// All reasoning we want to do — share conservation, dust bounds, fairness —
/// is at this level, not at the EnumerableSet/ERC20 level.
contract DistributorMathHarness {
    uint256 public constant MAX_DISTRIBUTION = 10_000;
    uint256 public constant MAX_DESTINATIONS = 100;

    struct RevenueShare {
        uint16 rTokenDist;
        uint16 rsrDist;
    }

    address[] public destinations;
    mapping(address => RevenueShare) public distribution;

    constructor(address[] memory dests, RevenueShare[] memory shares) {
        require(dests.length == shares.length, "len mismatch");
        require(dests.length <= MAX_DESTINATIONS, "too many dests");
        for (uint256 i = 0; i < dests.length; ++i) {
            destinations.push(dests[i]);
            distribution[dests[i]] = shares[i];
        }
    }

    function totals() public view returns (uint256 rTokenTotal, uint256 rsrTotal) {
        for (uint256 i = 0; i < destinations.length; ++i) {
            RevenueShare memory s = distribution[destinations[i]];
            rTokenTotal += s.rTokenDist;
            rsrTotal += s.rsrDist;
        }
    }

    /// Pure helper: compute the per-destination transfer amounts for
    /// `distribute(amount)` against the current distribution table.
    /// Returns the transfer amounts in the same order as `destinations`,
    /// with zero entries for destinations whose share is zero.
    function distributeAmounts(uint256 amount, bool isRSR)
        public
        view
        returns (uint256[] memory transferAmts, uint256 dust)
    {
        (uint256 rTokenTotal, uint256 rsrTotal) = totals();
        uint256 totalShares = isRSR ? rsrTotal : rTokenTotal;
        require(totalShares > 0, "no shares");

        uint256 tokensPerShare = amount / totalShares;
        require(tokensPerShare > 0, "nothing to distribute");

        transferAmts = new uint256[](destinations.length);
        uint256 paidOut;
        for (uint256 i = 0; i < destinations.length; ++i) {
            RevenueShare memory s = distribution[destinations[i]];
            uint256 numberOfShares = isRSR ? s.rsrDist : s.rTokenDist;
            uint256 amt = tokensPerShare * numberOfShares;
            transferAmts[i] = amt;
            paidOut += amt;
        }
        dust = amount - paidOut;
    }
}
