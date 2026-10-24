// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {PoolSymbolicStubTest, FreshHookToken} from "./PoolSymbolicStub.t.sol";
import {ReentrancyGuard} from "@openzeppelin-contracts/utils/ReentrancyGuard.sol";

/// Concrete replay with forge (revm), not Halmos, of the Halmos counterexample for
/// check_P3b_noGuard_freshReentryFails_expectFail, and the same inputs on the guarded pool.
/// Run by forge only; no Halmos run selects this contract.
contract P3bConcreteReplay is PoolSymbolicStubTest {
    bytes32 constant CEX_N = bytes32(0);
    bytes32 constant CEX_M = bytes32(uint256(1) << 253);
    uint256 constant CEX_AMOUNT = 0x8000000000000000040000000;
    address constant CEX_RECIPIENT = address(0x8000000000000000000000000000000000000000);

    function test_noGuard_cex_freshReentrySucceeds() public {
        (FreshHookToken fh, bool ok) = _p3bRun(false, CEX_N, CEX_M, CEX_AMOUNT, CEX_RECIPIENT);
        assertTrue(ok, "outer withdraw");
        assertTrue(fh.fired(), "hook fired");
        assertTrue(fh.freshUnspent(), "m unspent at re-entry");
        assertTrue(fh.reentryOk(), "re-entry succeeded without the guard");
    }

    function test_guarded_sameInputs_freshReentryBlockedByGuard() public {
        (FreshHookToken fh, bool ok) = _p3bRun(true, CEX_N, CEX_M, CEX_AMOUNT, CEX_RECIPIENT);
        assertTrue(ok, "outer withdraw");
        assertTrue(fh.fired(), "hook fired");
        assertTrue(fh.freshUnspent(), "m unspent at re-entry");
        assertFalse(fh.reentryOk(), "re-entry blocked");
        assertEq(fh.reentrySel(), ReentrancyGuard.ReentrancyGuardReentrantCall.selector, "guard error");
    }
}
