// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

// Probe: does any OZ Upgradeable import trigger the bug?
import "@openzeppelin/contracts-upgradeable/utils/AddressUpgradeable.sol";

contract ImportProbe1 {
    function check(address a) external view returns (bool) {
        return AddressUpgradeable.isContract(a);
    }
}
