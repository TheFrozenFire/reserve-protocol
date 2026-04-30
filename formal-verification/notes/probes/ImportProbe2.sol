// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

// Probe: same code path as Permit but inlining the upgradeable lib's body
// instead of importing it. If this works, the issue is the import, not the
// underlying assembly.

contract ImportProbe2 {
    function isContract(address account) internal view returns (bool) {
        return account.code.length > 0;
    }

    function check(address a) external view returns (bool) {
        return isContract(a);
    }
}
