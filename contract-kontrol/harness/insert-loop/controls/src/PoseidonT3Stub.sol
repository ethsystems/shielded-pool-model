// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// ASSUMPTION: PoseidonT3.hash replaced by keccak256 of
/// its inputs, reduced into the field. Installed at 0xA1002, the linked PoseidonT3 address.
contract PoseidonT3Stub {
    uint256 constant F = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    function hash(uint256[2] memory x) public pure returns (uint256) {
        return uint256(keccak256(abi.encode(x[0], x[1]))) % F;
    }
}
