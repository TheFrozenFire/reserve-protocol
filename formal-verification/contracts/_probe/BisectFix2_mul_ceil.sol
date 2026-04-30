// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;
import { FixLib, CEIL } from "../_relaxed/Fixed.sol";
contract BisectFix2_mul_ceil {
    function f(uint192 x, uint192 y) external pure returns (uint192) { return FixLib.mul(x, y, CEIL); }
}
