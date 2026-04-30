// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

/// Self-contained reimplementation of ThrottleLib's core math, written so
/// rocq-of-solidity can translate it without pulling in Reserve's exact-
/// pragma-pinned `Fixed.sol` / `Throttle.sol`. The semantics mirror
/// `contracts/libraries/Throttle.sol` line-for-line.
///
/// This is the *first contract translated* on the FV branch. Once we have a
/// pragma-relaxed copy of the production libs (or rebuild rocq-of-solidity
/// at version 0.8.28), we'll point ThrottleHarness.sol at the real source.
contract StandaloneThrottle {
    uint48 constant ONE_HOUR = 3600;

    struct Throttle {
        uint256 amtRate;
        uint192 pctRate;
        uint48 lastTimestamp;
        uint256 lastAvailable;
    }

    Throttle public throttle;

    constructor(uint256 amtRate, uint192 pctRate) {
        throttle.amtRate = amtRate;
        throttle.pctRate = pctRate;
        throttle.lastTimestamp = uint48(block.timestamp);
        throttle.lastAvailable = amtRate;
    }

    function hourlyLimit(uint256 supply) public view returns (uint256 limit) {
        limit = (supply * uint256(throttle.pctRate)) / 1e18;
        if (limit < throttle.amtRate) limit = throttle.amtRate;
    }

    function currentlyAvailable(uint256 limit) public view returns (uint256 available) {
        uint48 delta = uint48(block.timestamp) - throttle.lastTimestamp;
        available = throttle.lastAvailable + (limit * uint256(delta)) / uint256(ONE_HOUR);
        if (available > limit) available = limit;
    }

    function useAvailable(uint256 supply, int256 amount) external {
        if (throttle.amtRate == 0 && throttle.pctRate == 0) return;

        uint256 limit = hourlyLimit(supply);
        uint256 available = currentlyAvailable(limit);

        if (available != throttle.lastAvailable || available == limit) {
            throttle.lastTimestamp = uint48(block.timestamp);
        }

        if (amount > 0) {
            require(uint256(amount) <= available, "supply change throttled");
            available -= uint256(amount);
        } else if (amount < 0) {
            available += uint256(-amount);
        }
        throttle.lastAvailable = available;
    }
}
