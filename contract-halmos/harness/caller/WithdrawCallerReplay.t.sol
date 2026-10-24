// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Concrete forge replays of the two mutant counterexamples. Same setUp and body as
// WithdrawCaller.t.sol; only _fresh() differs: a fresh pool with both recording tokens supported by the owner
// (this contract), instead of symbolic storage. The empty tree's root is 0, so r = 0 is known.
// Point (halmos counterexample of both mutants): n = 0, token = other, a = 2^127, rcp = 2^159,
// r = 0, acc = true, who = 0, 65-byte zero proof.

import {stdError} from "forge-std/src/StdError.sol";
import {WithdrawCallerTest, WithdrawCallerMut_LATE_MARKTest, WithdrawCallerMut_PAY_CALLERTest, RecToken} from "./WithdrawCaller.t.sol";

contract WithdrawCallerReplay is WithdrawCallerTest {
    function _fresh() internal override {
        if (!pool.supportedTokens(TOKEN)) pool.addSupportedToken(TOKEN);
        if (!pool.supportedTokens(address(other))) pool.addSupportedToken(address(other));
    }

    /// Stock: the halmos body holds at the counterexample point and at a nonzero caller on TOKEN.
    function test_stock_point() public {
        this.check_withdraw(bytes32(0), address(other), 1 << 127, address(uint160(1 << 159)), bytes32(0), true, address(0), new bytes(65));
        assertEq(other.calls(), 1);
    }

    function test_stock_otherCaller() public {
        this.check_withdraw(bytes32(uint256(7)), TOKEN, 5, address(0x1234), bytes32(0), true, address(0xBEEF), new bytes(65));
        assertEq(RecToken(TOKEN).calls(), 1);
    }
}

contract WithdrawCallerReplay_LATE_MARK is WithdrawCallerMut_LATE_MARKTest {
    function _fresh() internal override {
        if (!pool.supportedTokens(TOKEN)) pool.addSupportedToken(TOKEN);
        if (!pool.supportedTokens(address(other))) pool.addSupportedToken(address(other));
    }

    function test_replay_fails() public {
        vm.expectRevert(stdError.assertionError);
        this.check_withdraw(bytes32(0), address(other), 1 << 127, address(uint160(1 << 159)), bytes32(0), true, address(0), new bytes(65));
    }

    /// Failure kind: the nullifier is unmarked when the token is called (NotMarkedAtPayout), marked after.
    function test_replay_kind() public {
        _fresh();
        verifier.setExp(true, 5, [bytes32(0), bytes32(uint256(uint160(address(other)))), bytes32(uint256(1 << 127)), bytes32(uint256(1 << 159)), bytes32(0), bytes32(0)]);
        other.arm(address(pool), bytes32(0));
        vm.prank(address(0));
        pool.withdraw(new bytes(65), bytes32(0), address(other), 1 << 127, address(uint160(1 << 159)), bytes32(0));
        assertEq(other.calls(), 1);
        assertFalse(other.spentSeen());
        assertTrue(pool.nullifiers(bytes32(0)));
    }
}

contract WithdrawCallerReplay_PAY_CALLER is WithdrawCallerMut_PAY_CALLERTest {
    function _fresh() internal override {
        if (!pool.supportedTokens(TOKEN)) pool.addSupportedToken(TOKEN);
        if (!pool.supportedTokens(address(other))) pool.addSupportedToken(address(other));
    }

    function test_replay_fails() public {
        vm.expectRevert(stdError.assertionError);
        this.check_withdraw(bytes32(0), address(other), 1 << 127, address(uint160(1 << 159)), bytes32(0), true, address(0), new bytes(65));
    }

    /// Failure kind: the payout goes to the caller, not the proof-bound recipient (PayoutArgs).
    function test_replay_kind() public {
        _fresh();
        verifier.setExp(true, 5, [bytes32(0), bytes32(uint256(uint160(address(other)))), bytes32(uint256(1 << 127)), bytes32(uint256(1 << 159)), bytes32(0), bytes32(0)]);
        other.arm(address(pool), bytes32(0));
        vm.prank(address(0xBEEF));
        pool.withdraw(new bytes(65), bytes32(0), address(other), 1 << 127, address(uint160(1 << 159)), bytes32(0));
        assertEq(other.calls(), 1);
        assertEq(other.to(), address(0xBEEF));
        assertTrue(other.spentSeen());
    }
}
