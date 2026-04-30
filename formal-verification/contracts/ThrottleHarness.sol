// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

// Imports from formal-verification/contracts/_relaxed/ rather than the
// production tree, because Reserve's libraries pin pragma to exact 0.8.28
// while the rocq-of-solidity solc identifies as 0.8.29-develop. The
// _relaxed/ copies are unmodified except for `^0.8.28` instead of `0.8.28`.
// Once we rebuild solc with PROJECT_VERSION=0.8.28 we'll repoint these
// imports back at the production tree.
import { ThrottleLib } from "./_relaxed/Throttle.sol";

/// Minimal wrapper that exposes ThrottleLib through a contract surface so
/// rocq-of-solidity has something to translate. Mirrors how RToken uses it.
contract ThrottleHarness {
    using ThrottleLib for ThrottleLib.Throttle;

    ThrottleLib.Throttle public issuance;
    ThrottleLib.Throttle public redemption;

    constructor(uint256 amtRate, uint192 pctRate) {
        ThrottleLib.Params memory p = ThrottleLib.Params({ amtRate: amtRate, pctRate: pctRate });
        issuance.params = p;
        issuance.lastTimestamp = uint48(block.timestamp);
        issuance.lastAvailable = amtRate;

        redemption.params = p;
        redemption.lastTimestamp = uint48(block.timestamp);
        redemption.lastAvailable = amtRate;
    }

    function useIssuance(uint256 supply, int256 amount) external {
        issuance.useAvailable(supply, amount);
    }

    function useRedemption(uint256 supply, int256 amount) external {
        redemption.useAvailable(supply, amount);
    }

    function availableIssuance(uint256 supply) external view returns (uint256) {
        return issuance.currentlyAvailable(issuance.hourlyLimit(supply));
    }

    function availableRedemption(uint256 supply) external view returns (uint256) {
        return redemption.currentlyAvailable(redemption.hourlyLimit(supply));
    }
}
