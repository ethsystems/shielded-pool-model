// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// G1 events: Halmos 0.3.3 has no log cheatcodes, so the emitted events of the owner functions are
// checked by forge fuzzing (concrete random inputs, not symbolic). Each successful owner call emits exactly
// one log from the pool, with the stated signature and indexed arguments and empty data.

import {Test, Vm} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";

contract OwnerEventsTest is Test {
    ShieldedPool internal pool;
    address internal constant V0 = address(0xBEEF01);
    address internal constant R0 = address(0xBEEF02);

    function setUp() public {
        pool = new ShieldedPool(V0, R0);
    }

    function _one() internal returns (Vm.Log memory l) {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(logs.length, 1);
        l = logs[0];
        assertEq(l.emitter, address(pool));
        assertEq(l.data.length, 0);
    }

    function testFuzz_setVerifier_emitsVerifierUpdated(address x) public {
        vm.assume(x != address(0));
        vm.recordLogs();
        pool.setVerifier(x);
        Vm.Log memory l = _one();
        assertEq(l.topics.length, 3);
        assertEq(l.topics[0], ShieldedPool.VerifierUpdated.selector);
        assertEq(l.topics[1], bytes32(uint256(uint160(V0))));
        assertEq(l.topics[2], bytes32(uint256(uint160(x))));
        assertEq(address(pool.verifier()), x);
    }

    function testFuzz_setRegistry_emitsRegistryUpdated(address x) public {
        vm.assume(x != address(0));
        vm.recordLogs();
        pool.setAttestationRegistry(x);
        Vm.Log memory l = _one();
        assertEq(l.topics.length, 3);
        assertEq(l.topics[0], ShieldedPool.AttestationRegistryUpdated.selector);
        assertEq(l.topics[1], bytes32(uint256(uint160(R0))));
        assertEq(l.topics[2], bytes32(uint256(uint160(x))));
    }

    function testFuzz_transferOwnership_emitsOwnershipTransferred(address x) public {
        vm.assume(x != address(0));
        vm.recordLogs();
        pool.transferOwnership(x);
        Vm.Log memory l = _one();
        assertEq(l.topics.length, 3);
        assertEq(l.topics[0], ShieldedPool.OwnershipTransferred.selector);
        assertEq(l.topics[1], bytes32(uint256(uint160(address(this)))));
        assertEq(l.topics[2], bytes32(uint256(uint160(x))));
    }

    function testFuzz_addRemoveToken_emitTokenAddedRemoved(address x) public {
        vm.assume(x != address(0));
        vm.recordLogs();
        pool.addSupportedToken(x);
        Vm.Log memory l = _one();
        assertEq(l.topics.length, 2);
        assertEq(l.topics[0], ShieldedPool.TokenAdded.selector);
        assertEq(l.topics[1], bytes32(uint256(uint160(x))));
        assertTrue(pool.supportedTokens(x));
        vm.recordLogs();
        pool.removeSupportedToken(x);
        l = _one();
        assertEq(l.topics.length, 2);
        assertEq(l.topics[0], ShieldedPool.TokenRemoved.selector);
        assertEq(l.topics[1], bytes32(uint256(uint160(x))));
        assertFalse(pool.supportedTokens(x));
    }

    /// Non-owner calls revert with OnlyOwner, and no log is recorded (fuzzed caller and argument).
    function testFuzz_nonOwner_reverts(address caller, address x, uint8 which) public {
        vm.assume(caller != address(this));
        bytes memory data;
        uint8 w = which % 5;
        if (w == 0) data = abi.encodeCall(ShieldedPool.addSupportedToken, (x));
        else if (w == 1) data = abi.encodeCall(ShieldedPool.removeSupportedToken, (x));
        else if (w == 2) data = abi.encodeCall(ShieldedPool.setVerifier, (x));
        else if (w == 3) data = abi.encodeCall(ShieldedPool.setAttestationRegistry, (x));
        else data = abi.encodeCall(ShieldedPool.transferOwnership, (x));
        vm.recordLogs();
        vm.prank(caller);
        (bool ok, bytes memory ret) = address(pool).call(data);
        assertFalse(ok);
        assertEq(bytes4(ret), ShieldedPool.OnlyOwner.selector);
        assertEq(vm.getRecordedLogs().length, 0);
    }
}
