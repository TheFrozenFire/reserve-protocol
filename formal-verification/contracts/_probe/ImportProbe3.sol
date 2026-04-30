// SPDX-License-Identifier: BlueOak-1.0.0
pragma solidity ^0.8.28;

import "@openzeppelin/contracts-upgradeable/utils/cryptography/SignatureCheckerUpgradeable.sol";

contract ImportProbe3 {
    function check(address signer, bytes32 hash, bytes memory sig) external view returns (bool) {
        return SignatureCheckerUpgradeable.isValidSignatureNow(signer, hash, sig);
    }
}
