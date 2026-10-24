// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
import {InternalLeanIMT, LeanIMTData} from "../vendor/M3/InternalLeanIMT.sol";
import {PoseidonT3} from "poseidon-solidity/PoseidonT3.sol";
contract Harness_M3 {
    LeanIMTData internal tree;
    function insert(uint256 leaf) external returns (uint256) {
        return InternalLeanIMT._insert(tree, leaf);
    }
    function runLoop(uint256 level, uint256 treeDepth, uint256 index, uint256 node)
        external returns (uint256, uint256) {
        LeanIMTData storage self = tree;
        for (; level < treeDepth; ) {
            if ((index >> level) & 1 == 1) {
                node = PoseidonT3.hash([self.sideNodes[level], node]);
            } else {
                self.sideNodes[level] = node;
            }

            unchecked {
                ++level;
            }
        }

        return (level, node);
    }
    function runPost(uint256 treeDepth, uint256 index, uint256 node, uint256 leaf)
        external returns (uint256) {
        LeanIMTData storage self = tree;

        self.size = ++index;

        self.sideNodes[treeDepth] = node;
        self.sideNodes[leaf] = index;

        return node;
    }
}
