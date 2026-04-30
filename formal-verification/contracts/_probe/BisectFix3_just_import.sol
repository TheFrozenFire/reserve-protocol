// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;
import { FixLib } from "../_relaxed/Fixed.sol";
contract BisectFix3_just_import {
    function f(uint192 x) external pure returns (uint192) { return x + 1; }
}
