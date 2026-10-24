// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Concrete replays (plain `forge test`, not Kontrol) of WithdrawSuccess.t.sol. Each runs a prove_ body
// with concrete arguments and a concrete pool state: constructor storage, both recording tokens
// supported through the owner call, empty tree (root() == 0, so r = 0 is the current root). A replay
// that reaches a mutant's violation shows that the violation is reachable by a real execution. The
// same arguments on the original pool must not revert. Supporting evidence only.

import "./WithdrawSuccess.t.sol";
import {stdError} from "forge-std/src/StdError.sol";

abstract contract ConcreteWithdraw is WithdrawSuccessProbes {
    function _fresh() internal override {
        if (!pool.supportedTokens(TOKEN)) pool.addSupportedToken(TOKEN);
        if (!pool.supportedTokens(address(other))) pool.addSupportedToken(address(other));
    }
}

bytes32 constant N1 = bytes32(uint256(1));
bytes32 constant NHI = bytes32((uint256(1) << 253) | 1);
address constant RCP = address(0x1234);
address constant WHO = address(0xCA11E5); // a concrete caller for vm.prank
address constant NOCODE = address(0x1234567); // a no-code token address above 0x11

contract WithdrawSuccessReplay is ConcreteWithdraw {
    // One call per test: the recording tokens keep their counters across calls.
    function test_W_success_original_high() public {
        this.prove_success_token_above_0x11(N1, TOKEN, 1, RCP, bytes32(0), true, "");
    }

    function test_W_success_original_low() public {
        this.prove_success_token_above_0x11(N1, address(other), 1, RCP, bytes32(0), true, "");
    }

    function test_two_tokens_original_low_b() public {
        this.prove_success_two_tokens(NHI, address(other), (1 << 128) - 1, address(type(uint160).max), bytes32(0), true, hex"00ff");
    }

    /// The NULHI point and the SKIPV point (acc = false) on the original pool: no violation.
    function test_W_success_original_low_nhi() public {
        this.prove_success_two_tokens(NHI, address(other), 1, RCP, bytes32(0), true, "");
    }

    function test_W_success_original_low_reject() public {
        this.prove_success_two_tokens(N1, address(other), 1, RCP, bytes32(0), false, "");
    }

    function test_token_pick_original_low() public {
        this.prove_success_token_pick(N1, true, 1, RCP, bytes32(0), true, "");
    }

    function test_W_success_original_unsupported_reverts_quietly() public {
        // A token address that is not a contract: withdraw reverts, the body returns (no violation).
        this.prove_success_token_above_0x11(N1, address(0xBEEF), 1, RCP, bytes32(0), true, "");
    }

    /// Scope A, the original pool at a supported no-code token: withdraw reverts, no violation.
    function test_any_token_original_nocode_supported() public {
        pool.addSupportedToken(NOCODE);
        this.prove_success_token_above_0x11(N1, NOCODE, 1, RCP, bytes32(0), true, "");
    }

    function test_W_witness_original_high() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_any_token_mustfail(N1, TOKEN, 1, RCP, bytes32(0), true, "");
    }

    function test_W_witness_original_low() public {
        vm.expectRevert(stdError.assertionError);
        this.prove_witness_other_token_mustfail(N1, 1, RCP, bytes32(0), true, "");
    }
}

contract WithdrawSuccessReplay_M_LATE_MARK is ConcreteWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_LATE_MARK(v, r));
    }

    function test_replay() public {
        vm.expectRevert(WithdrawSuccess.W6NotMarkedAtPayout.selector);
        this.prove_success_token_above_0x11(N1, address(other), 1, RCP, bytes32(0), true, "");
    }

    /// Scope A: the failing node is on the TOKEN branch.
    function test_replay_token() public {
        vm.expectRevert(WithdrawSuccess.W6NotMarkedAtPayout.selector);
        this.prove_success_token_above_0x11(N1, TOKEN, 1, RCP, bytes32(0), true, "");
    }
}

contract WithdrawSuccessReplay_M_SWAP_INPUTS is ConcreteWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SWAP_INPUTS(v, r));
    }

    function test_replay() public {
        vm.expectRevert(WithdrawSuccess.W10Inputs.selector);
        this.prove_success_token_above_0x11(N1, TOKEN, 1, RCP, bytes32(0), true, ""); // the failing node is on the TOKEN branch
    }
}

contract WithdrawSuccessReplay_M_DROP_BIT253 is ConcreteWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DROP_BIT253(v, r));
    }

    function test_replay() public {
        vm.expectRevert(WithdrawSuccess.W10Inputs.selector);
        this.prove_success_token_above_0x11(NHI, address(other), 1, RCP, bytes32(0), true, "");
    }
}

contract WithdrawSuccessReplay_M_PAY_CALLER is ConcreteWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_CALLER(v, r));
    }

    function test_replay() public {
        vm.expectRevert(WithdrawSuccess.W10Args.selector);
        this.prove_success_token_above_0x11(N1, address(other), 1, RCP, bytes32(0), true, "");
    }
}

/// The symbolic-caller body (vm.prank(who)) with a concrete caller.
contract WithdrawSuccessReplay_Caller is ConcreteWithdraw {
    function test_caller_original_other() public {
        this.prove_caller_two_tokens(N1, address(other), 1, RCP, bytes32(0), true, WHO, "");
    }

    function test_caller_original_token() public {
        this.prove_caller_two_tokens(N1, TOKEN, 1, RCP, bytes32(0), true, WHO, "");
    }
}

contract WithdrawSuccessReplay_M_PAY_CALLER_Caller is ConcreteWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_CALLER(v, r));
    }

    function test_replay_prank() public {
        vm.expectRevert(WithdrawSuccess.W10Args.selector);
        this.prove_caller_two_tokens(N1, address(other), 1, RCP, bytes32(0), true, WHO, "");
    }
}

contract WithdrawSuccessReplay_M_SKIP_VERIFIER is ConcreteWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SKIP_VERIFIER(v, r));
    }

    function test_replay() public {
        vm.expectRevert(WithdrawSuccess.W10VerifierBypassed.selector);
        this.prove_success_token_above_0x11(N1, address(other), 1, RCP, bytes32(0), false, "");
    }

    /// Scope A: the failing node is on the TOKEN branch (acc = false).
    function test_replay_token() public {
        vm.expectRevert(WithdrawSuccess.W10VerifierBypassed.selector);
        this.prove_success_token_above_0x11(N1, TOKEN, 1, RCP, bytes32(0), false, "");
    }
}

contract WithdrawSuccessReplay_M_FIXED_TOKEN is ConcreteWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_FIXED_TOKEN(v, r));
    }

    function test_replay_low_token_fails() public {
        vm.expectRevert(WithdrawSuccess.W10WrongToken.selector);
        this.prove_success_token_above_0x11(N1, address(other), 1, RCP, bytes32(0), true, "");
    }

    /// Scope A, a supported token with no code. FIXED_TOKEN pays TOKEN instead and succeeds.
    function test_replay_nocode_token_fails() public {
        pool.addSupportedToken(NOCODE);
        vm.expectRevert(WithdrawSuccess.W10WrongToken.selector);
        this.prove_success_token_above_0x11(N1, NOCODE, 1, RCP, bytes32(0), true, "");
    }

    /// A fixed-token scope (token = TOKEN) cannot see this mutant: the same body passes.
    function test_replay_high_token_passes() public {
        this.prove_success_token_above_0x11(N1, TOKEN, 1, RCP, bytes32(0), true, "");
    }
}
