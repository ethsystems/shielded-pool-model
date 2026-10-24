// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Minimal harnesses that own one LeanIMTData at slot 0 (size 0, depth 1, sideNodes 2, leaves 3), the
// same slot as ShieldedPool._tree, and call the linked LeanIMT library: the stock library and the three
// mutant libraries of mutants/insert-loop/ (each with its own copy of the LeanIMTData struct).
import {LeanIMT, LeanIMTData} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";
import {LeanIMT_M_FIELD, LeanIMTData as DataField} from "./mutants/LeanIMT_M_FIELD.sol";
import {LeanIMT_M_ZERO, LeanIMTData as DataZero} from "./mutants/LeanIMT_M_ZERO.sol";
import {LeanIMT_M_DUP, LeanIMTData as DataDup} from "./mutants/LeanIMT_M_DUP.sol";

contract TreeHarness {
    LeanIMTData internal tree;

    function insert(uint256 leaf) external returns (uint256) {
        return LeanIMT.insert(tree, leaf);
    }
}

contract TreeHarness_M_FIELD {
    DataField internal tree;

    function insert(uint256 leaf) external returns (uint256) {
        return LeanIMT_M_FIELD.insert(tree, leaf);
    }
}

contract TreeHarness_M_ZERO {
    DataZero internal tree;

    function insert(uint256 leaf) external returns (uint256) {
        return LeanIMT_M_ZERO.insert(tree, leaf);
    }
}

contract TreeHarness_M_DUP {
    DataDup internal tree;

    function insert(uint256 leaf) external returns (uint256) {
        return LeanIMT_M_DUP.insert(tree, leaf);
    }
}
