// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;
import { FixLib, FIX_ONE } from "../_relaxed/Fixed.sol";
contract BisectFix1_div {
    function f(uint192 x, uint192 y) external pure returns (uint192) { return FixLib.div(x, y); }
}
