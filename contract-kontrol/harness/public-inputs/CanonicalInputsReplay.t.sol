// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Concrete replays of CanonicalInputs.t.sol (plain `forge test`, not Kontrol). Each runs a prove_ body with concrete
// arguments on a concrete pool: constructor storage, TOKEN supported through the owner call, empty
// tree (root() == 0, so r = 0 is the current root), registry root 0 unless a test stores another.
// A replay that hits a mutant's violation shows a real execution reaches it. The same arguments on
// the original pool must not fail.

import "./CanonicalInputs.t.sol";
import {stdError} from "forge-std/src/StdError.sol";

uint256 constant PF = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
bytes32 constant BP = bytes32(PF);
bytes32 constant B1 = bytes32(uint256(1));
bytes32 constant B2 = bytes32(uint256(2));
address constant TK = address(0xF00B);
address constant RC = address(0x1234);

abstract contract ConcreteCanonicalInputs is CanonicalInputs {
    function _fresh() internal override {
        if (!pool.supportedTokens(TK)) pool.addSupportedToken(TK);
    }

    function _regRoot(bytes32 v) internal {
        vm.store(address(registry), bytes32(0), v);
    }

    function _validRoot(bytes32 r) internal {
        // validRoots is slot 105 of the pool's storage layout (forge inspect, checked in LOG.md).
        vm.store(address(pool), keccak256(abi.encode(r, uint256(105))), bytes32(uint256(1)));
    }
}

contract CanonicalInputsReplay is ConcreteCanonicalInputs {
    function test_S1d0_c_noncanonical() public {
        this.prove_deposit_canonical(BP, TK, 1, hex"abcd");
    }

    function test_S1d0_root_noncanonical() public {
        _regRoot(BP);
        this.prove_deposit_canonical(B1, TK, 1, hex"abcd");
    }

    function test_S1d0_canonical() public {
        this.prove_deposit_canonical(B1, TK, 1, hex"abcd");
    }

    function test_S1d_split() public {
        this.prove_deposit_canonical_split(BP, TK, 1, hex"00112233", 2);
    }

    function test_S1d0_witness() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_deposit_canonical_mustfail(B1, TK, 1, hex"abcd");
    }

    function test_S1t0_n0_noncanonical() public {
        this.prove_transfer_canonical(BP, B1, B1, B2, bytes32(0), hex"abcd");
    }

    function test_S1t0_c1_noncanonical() public {
        this.prove_transfer_canonical(B1, B2, B1, BP, bytes32(0), hex"abcd");
    }

    function test_S1t0_r_noncanonical() public {
        _validRoot(BP);
        this.prove_transfer_canonical(B1, B2, B1, B2, BP, hex"abcd");
    }

    function test_S1t0_canonical() public {
        this.prove_transfer_canonical(B1, B2, B1, B2, bytes32(0), hex"abcd");
    }

    function test_S1t_split() public {
        this.prove_transfer_canonical_split(B1, BP, B1, B2, bytes32(0), hex"00112233", 3);
    }

    function test_S1t0_witness() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_transfer_canonical_mustfail(B1, B2, B1, B2, bytes32(0), hex"abcd");
    }

    function test_S1w_n_noncanonical() public {
        this.prove_withdraw_canonical(BP, TK, 1, RC, bytes32(0), hex"00ff");
    }

    function test_S1w_r_noncanonical() public {
        _validRoot(BP);
        this.prove_withdraw_canonical(B1, TK, 1, RC, BP, hex"00ff");
    }

    function test_S1w_canonical() public {
        this.prove_withdraw_canonical(B1, TK, 1, RC, bytes32(0), hex"00ff");
    }

    function test_S1w_witness() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_withdraw_canonical_mustfail(B1, TK, 1, RC, bytes32(0), hex"00ff");
    }
}

contract CanonicalInputsReplay_M_DEPOSIT_CANONICAL is ConcreteCanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_CANONICAL(v, r));
    }

    function test_c() public {
        vm.expectRevert(CanonicalInputs.S1NonCanonical.selector);
        this.prove_deposit_canonical(BP, TK, 1, hex"abcd");
    }

    function test_root() public {
        _regRoot(BP);
        vm.expectRevert(CanonicalInputs.S1NonCanonical.selector);
        this.prove_deposit_canonical(B1, TK, 1, hex"abcd");
    }
}

contract CanonicalInputsReplay_M_TRANSFER_CANONICAL is ConcreteCanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_CANONICAL(v, r));
    }

    function test_n0() public {
        vm.expectRevert(CanonicalInputs.S1NonCanonical.selector);
        this.prove_transfer_canonical(BP, B1, B1, B2, bytes32(0), hex"abcd");
    }
}

contract CanonicalInputsReplay_M_WITHDRAW_CANONICAL is ConcreteCanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_CANONICAL(v, r));
    }

    function test_n() public {
        vm.expectRevert(CanonicalInputs.S1NonCanonical.selector);
        this.prove_withdraw_canonical(BP, TK, 1, RC, bytes32(0), hex"00ff");
    }
}

contract CanonicalInputsReplay_M_BOUND_GT is ConcreteCanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_BOUND_GT(v, r));
    }

    function test_w_n_eq_P() public {
        vm.expectRevert(CanonicalInputs.S1NonCanonical.selector);
        this.prove_withdraw_canonical(BP, TK, 1, RC, bytes32(0), hex"00ff");
    }

    function test_w_n_P_plus_1_rejected() public {
        this.prove_withdraw_canonical(bytes32(PF + 1), TK, 1, RC, bytes32(0), hex"00ff");
    }
}

// S2 single-payload witnesses (InputOrderWitness), at the InputOrderReplay points with an empty proof.
contract InputOrderWitnessReplay is InputOrderWitness {
    function _fresh() internal override {
        if (!pool.supportedTokens(TOKEN)) pool.addSupportedToken(TOKEN);
    }

    function test_S2d0_witness() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_deposit_order_mustfail(B1, TOKEN, 1, "abc");
    }

    function test_S2t0_witness() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_transfer_order_mustfail(B1, B2, bytes32(uint256(3)), bytes32(uint256(4)), bytes32(0), "abc");
    }
}
