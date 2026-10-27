// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Concrete replays of PublicInputs.t.sol (plain `forge test`, not Kontrol). Each runs a prove_ body with concrete
// arguments and a concrete pool state in place of the symbolic one: constructor storage, TOKEN
// supported through the owner call, empty tree (root() == 0, so r = 0 is the current root).
// A replay that reaches a mutant's violation shows that violation is reachable by a real
// execution, so the Kontrol failing node it matches is feasible. The same arguments on the
// original pool must not revert.

import "./PublicInputs.t.sol";
import {stdError} from "forge-std/src/StdError.sol";

abstract contract ConcreteFixedTokenWithdraw is FixedTokenWithdraw {
    function _fresh() internal override {
        if (!pool.supportedTokens(TOKEN)) pool.addSupportedToken(TOKEN);
    }
}

abstract contract ConcreteInputOrder is InputOrder {
    function _fresh() internal override {
        if (!pool.supportedTokens(TOKEN)) pool.addSupportedToken(TOKEN);
    }
}

bytes32 constant N1 = bytes32(uint256(1));
bytes32 constant NHI = bytes32((uint256(1) << 253) | 1);
address constant RCP = address(0x1234);

contract FixedTokenWithdrawReplay is ConcreteFixedTokenWithdraw {
    // One call per test: the recording token keeps its counters across calls.
    function test_W_success_original_a() public {
        this.prove_success_fixed_token(N1, 1, RCP, bytes32(0), true, "");
    }

    function test_W_success_original_b() public {
        this.prove_success_fixed_token(NHI, (1 << 128) - 1, address(uint160(type(uint160).max)), bytes32(0), true, hex"00ff");
    }

    function test_W_success_original_c() public {
        this.prove_success_fixed_token(N1, 1, RCP, bytes32(0), false, "");
    }

    function test_W_witness_original() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_fixed_token_mustfail(N1, 1, RCP, bytes32(0), true, "");
    }
}

contract FixedTokenWithdrawReplay_M_LATE_MARK is ConcreteFixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_LATE_MARK(v, r));
    }

    function test_replay() public {
        vm.expectRevert(FixedTokenWithdraw.W6NotMarkedAtPayout.selector);
        this.prove_success_fixed_token(N1, 1, RCP, bytes32(0), true, "");
    }
}

contract FixedTokenWithdrawReplay_M_SWAP_INPUTS is ConcreteFixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SWAP_INPUTS(v, r));
    }

    function test_replay() public {
        vm.expectRevert(FixedTokenWithdraw.W10Inputs.selector);
        this.prove_success_fixed_token(N1, 1, RCP, bytes32(0), true, "");
    }
}

contract FixedTokenWithdrawReplay_M_DROP_BIT253 is ConcreteFixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DROP_BIT253(v, r));
    }

    function test_replay() public {
        vm.expectRevert(FixedTokenWithdraw.W10Inputs.selector);
        this.prove_success_fixed_token(NHI, 1, RCP, bytes32(0), true, "");
    }
}

contract FixedTokenWithdrawReplay_M_PAY_CALLER is ConcreteFixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_CALLER(v, r));
    }

    function test_replay() public {
        vm.expectRevert(FixedTokenWithdraw.W10Args.selector);
        this.prove_success_fixed_token(N1, 1, RCP, bytes32(0), true, "");
    }
}

contract FixedTokenWithdrawReplay_M_SKIP_VERIFIER is ConcreteFixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SKIP_VERIFIER(v, r));
    }

    function test_replay() public {
        vm.expectRevert(FixedTokenWithdraw.W10VerifierBypassed.selector);
        this.prove_success_fixed_token(bytes32(uint256(2)), 1, RCP, bytes32(0), false, "");
    }
}

contract InputOrderReplay is ConcreteInputOrder {
    function test_S2_original() public {
        this.prove_deposit_order_split(N1, TOKEN, 1, "abc", 0);
        this.prove_deposit_order_split(N1, TOKEN, 1, "abc", 2);
        this.prove_deposit_order(N1, TOKEN, 1, "abc");
        this.prove_transfer_order_split(N1, bytes32(uint256(2)), bytes32(uint256(3)), bytes32(uint256(4)), bytes32(0), "abc", 1);
        this.prove_transfer_order(N1, bytes32(uint256(2)), bytes32(uint256(3)), bytes32(uint256(4)), bytes32(0), "abc");
    }

    function test_S2_witness_original() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_deposit_order_split_mustfail(N1, TOKEN, 1, "abc", 0);
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_transfer_order_split_mustfail(N1, bytes32(uint256(2)), bytes32(uint256(3)), bytes32(uint256(4)), bytes32(0), "abc", 1);
    }
}

contract InputOrderReplay_M_DEPOSIT_SWAP_45 is ConcreteInputOrder {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_SWAP_45(v, r));
    }

    function test_replay() public {
        vm.expectRevert(InputOrder.S2Inputs.selector);
        this.prove_deposit_order_split(N1, TOKEN, 1, "abc", 0);
        vm.expectRevert(InputOrder.S2Inputs.selector);
        this.prove_deposit_order(N1, TOKEN, 1, "abc");
    }
}

contract InputOrderReplay_M_TRANSFER_SWAP_45 is ConcreteInputOrder {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_SWAP_45(v, r));
    }

    function test_replay() public {
        vm.expectRevert(InputOrder.S2Inputs.selector);
        this.prove_transfer_order_split(N1, bytes32(uint256(2)), bytes32(uint256(3)), bytes32(uint256(4)), bytes32(0), "abc", 1);
        vm.expectRevert(InputOrder.S2Inputs.selector);
        this.prove_transfer_order(N1, bytes32(uint256(2)), bytes32(uint256(3)), bytes32(uint256(4)), bytes32(0), "abc");
    }
}
