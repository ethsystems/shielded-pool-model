// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Kontrol checks of the three _insert rejections (InternalLeanIMT.sol:41-47) on a minimal harness,
// from fully symbolic tree storage (any size, any depth, any sideNodes and leaves). PoseidonT3 is
// the keccak stub at 0xA1002 (an assumption; no rejection path hashes). The library runtime is
// created from type(...).creationCode and etched at its linked address. Must-fail siblings run the
// same body against a library with that one check removed (mutants/insert-loop/).

import {Test} from "forge-std/src/Test.sol";
import {KontrolCheats} from "kontrol-cheatcodes/KontrolCheats.sol";
import {PoseidonT3Stub} from "./PoseidonT3Stub.sol";
import {LeanIMT} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";
import {TreeHarness, TreeHarness_M_FIELD, TreeHarness_M_ZERO, TreeHarness_M_DUP} from "./TreeHarness.sol";
import {LeanIMT_M_FIELD} from "./mutants/LeanIMT_M_FIELD.sol";
import {LeanIMT_M_ZERO} from "./mutants/LeanIMT_M_ZERO.sol";
import {LeanIMT_M_DUP} from "./mutants/LeanIMT_M_DUP.sol";

abstract contract TreeRejectionsBase is Test, KontrolCheats {
    uint256 constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    bytes4 constant SEL_FIELD = bytes4(keccak256("LeafGreaterThanSnarkScalarField()"));
    bytes4 constant SEL_ZERO = bytes4(keccak256("LeafCannotBeZero()"));
    bytes4 constant SEL_DUP = bytes4(keccak256("LeafAlreadyExists()"));
    address h;

    function _etchLib(bytes memory init, address at) internal {
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(at, tmp.code);
    }

    function _deploy() internal virtual returns (address);

    function setUp() public {
        vm.etch(address(0xA1002), address(new PoseidonT3Stub()).code);
        h = _deploy();
        kevm.symbolicStorage(h);
    }

    // Calls insert(leaf); returns success and the first four bytes of the return data.
    function _ins(uint256 leaf) internal returns (bool ok, bytes4 sel) {
        (ok,) = h.call(abi.encodeWithSelector(TreeHarness.insert.selector, leaf));
        assembly {
            let n := returndatasize()
            if gt(n, 3) {
                returndatacopy(0, 0, 4)
                sel := and(mload(0), 0xffffffff00000000000000000000000000000000000000000000000000000000)
            }
        }
    }

    function prove_reject_field(uint256 leaf) public {
        vm.assume(leaf >= P);
        (bool ok, bytes4 sel) = _ins(leaf);
        assert(!ok);
        assert(sel == SEL_FIELD);
    }

    function prove_reject_zero() public {
        (bool ok, bytes4 sel) = _ins(0);
        assert(!ok);
        assert(sel == SEL_ZERO);
    }

    function prove_reject_duplicate(uint256 leaf) public {
        vm.assume(leaf != 0 && leaf < P);
        vm.assume(uint256(vm.load(h, keccak256(abi.encode(leaf, uint256(3))))) != 0);
        (bool ok, bytes4 sel) = _ins(leaf);
        assert(!ok);
        assert(sel == SEL_DUP);
    }
}

contract TreeRejections is TreeRejectionsBase {
    function _deploy() internal override returns (address) {
        _etchLib(type(LeanIMT).creationCode, address(0xA1001));
        return address(new TreeHarness());
    }
}

contract TreeRejections_M_FIELD is TreeRejectionsBase {
    function _deploy() internal override returns (address) {
        _etchLib(type(LeanIMT_M_FIELD).creationCode, address(0xA1011));
        return address(new TreeHarness_M_FIELD());
    }
}

contract TreeRejections_M_ZERO is TreeRejectionsBase {
    function _deploy() internal override returns (address) {
        _etchLib(type(LeanIMT_M_ZERO).creationCode, address(0xA1012));
        return address(new TreeHarness_M_ZERO());
    }
}

contract TreeRejections_M_DUP is TreeRejectionsBase {
    function _deploy() internal override returns (address) {
        _etchLib(type(LeanIMT_M_DUP).creationCode, address(0xA1013));
        return address(new TreeHarness_M_DUP());
    }
}
