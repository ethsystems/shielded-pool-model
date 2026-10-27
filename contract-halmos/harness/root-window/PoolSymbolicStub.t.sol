// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {PoolSymbolicTest} from "./PoolSymbolic.t.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";

/// ASSUMPTION: PoseidonT3.hash is replaced by keccak256 of its inputs, reduced into the field.
/// Same selector and ABI as the library. Results under this stub say nothing about hash values,
/// only about control flow and storage writes.
interface SVMU {
    function createUint256(string calldata name) external returns (uint256);
}

contract PoseidonT3Stub {
    uint256 constant F = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    function hash(uint256[2] memory x) public pure returns (uint256) {
        return uint256(keccak256(abi.encode(x[0], x[1]))) % F;
    }
}

contract PoolSymbolicStubTest is PoolSymbolicTest {
    function _etchPoseidon() internal override {
        vm.etch(address(0xA1002), address(new PoseidonT3Stub()).code);
    }

    // ---- P1 under the stub: deposit from arbitrary storage ----

    function check_P1_nullifierMonotone_symStorage_deposit(bytes32 k, bytes32 c, uint256 amount) public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        vm.assume(pool.nullifiers(k));
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    // ---- P5: tree size never decreases, per entry point ----

    function check_P5_treeSize_reached_deposit(bytes32 c, uint256 amount) public {
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_P5_treeSize_reached_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        uint256 before = pool.getCommitmentCount();
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_P5_treeSize_reached_withdraw(bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        uint256 before = pool.getCommitmentCount();
        try pool.withdraw("", n, address(token), amount, recipient, root) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_P5_treeSize_symStorage_deposit(bytes32 c, uint256 amount) public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_P5_treeSize_symStorage_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 before = pool.getCommitmentCount();
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_P5_treeSize_symStorage_withdraw(bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 before = pool.getCommitmentCount();
        try pool.withdraw("", n, address(token), amount, recipient, root) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: a deposit that grows the tree is reachable, so the P5 deposit check is not vacuous.
    function check_W_P5_depositGrows_expectFail(bytes32 c, uint256 amount) public {
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        vm.assume(ok);
        assert(pool.getCommitmentCount() == before);
    }

    /// Witness: a transfer that succeeds is reachable under the stub.
    function check_W_P1_transferSucceeds_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d) public {
        (bool ok,) = address(pool).call(
            abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], pool.commitmentRoot(), ""))
        );
        assert(!ok);
    }

    // ---- Coverage probes for arbitrary-storage results (tree slots: 0 size, 1 depth) ----

    /// Witness: from arbitrary storage with a full depth-3 tree (size 7), a transfer can succeed.
    function check_W_symStorage_transferDepth3_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root)
        public
    {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        vm.store(address(pool), bytes32(uint256(0)), bytes32(uint256(7)));
        vm.store(address(pool), bytes32(uint256(1)), bytes32(uint256(3)));
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    function _deepTree12() internal {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        vm.store(address(pool), bytes32(uint256(0)), bytes32(uint256(4095)));
        vm.store(address(pool), bytes32(uint256(1)), bytes32(uint256(12)));
    }

    /// P1 with tree depth 12, size 2^12-1: every insert loop runs 12 or 13 iterations (> --loop 8).
    function check_P1_symStorage_transfer_depth12(bytes32 k, bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root)
        public
    {
        _deepTree12();
        vm.assume(pool.nullifiers(k));
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    /// Witness for the probe above: a deep transfer can succeed.
    function check_W_symStorage_transferDepth12_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root)
        public
    {
        _deepTree12();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    /// Witness with symbolic depth >= 9: shows whether a success path survives with a symbolic loop bound.
    function check_W_symStorage_transferSymDepthGe9_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root)
        public
    {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 dep = SVMU(address(svm)).createUint256("depth");
        vm.assume(dep >= 30 && dep < 38);
        vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    // ---- Arbitrary storage with the tree depth as an explicit symbolic value below 40 ----
    // Unconstrained symbolic depth left the path count unchanged between --loop 8 and --loop 40,
    // so deep trees were not explored. These variants store a fresh depth < 40 and run at --loop 44.

    function _symStorageDepthLt40() internal {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 dep = SVMU(address(svm)).createUint256("depth");
        vm.assume(dep < 40);
        vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
    }

    function check_D40_P1_transfer(bytes32 k, bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P1_deposit(bytes32 k, bytes32 c, uint256 amount) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P1_withdraw(bytes32 k, bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        try pool.withdraw("", n, address(token), amount, recipient, root) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P5_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_D40_P5_deposit(bytes32 c, uint256 amount) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_D40_P5_withdraw(bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        try pool.withdraw("", n, address(token), amount, recipient, root) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: success paths exist in the D40 setup (transfer).
    function check_D40_W_transferSucceeds_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _symStorageDepthLt40();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    /// Any entry point, any caller, arbitrary storage, depth < 40.
    function check_D40_P1_anyCall(bytes32 k) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        _anyCall();
        assert(pool.nullifiers(k));
    }

    function check_D40_P5_anyCall() public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        _anyCall();
        assert(pool.getCommitmentCount() >= before);
    }

    /// Any entry point, any caller, arbitrary storage, depth < 8 (run at --loop 12).
    function check_D8_P1_anyCall(bytes32 k) public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 dep = SVMU(address(svm)).createUint256("depth");
        vm.assume(dep < 8);
        vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
        vm.assume(pool.nullifiers(k));
        _anyCall();
        assert(pool.nullifiers(k));
    }

    /// Any entry point, any caller, arbitrary storage, depth < 8 (run at --loop 12).
    function check_D8_P5_anyCall() public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 dep = SVMU(address(svm)).createUint256("depth");
        vm.assume(dep < 8);
        vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
        uint256 before = pool.getCommitmentCount();
        _anyCall();
        assert(pool.getCommitmentCount() >= before);
    }

    // ---- D40 per-function checks for the owner-only state-changing functions ----
    // Arbitrary storage, fresh symbolic depth < 40 (run at --loop 44), any caller (owner or not).
    // Each function has a witness at the deep end (depth 32..39): an owner call that succeeds.

    function _anyCaller() internal returns (address caller) {
        caller = svm.createAddress("caller");
        vm.prank(caller);
    }

    function _symStorageDepthDeep() internal {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 dep = SVMU(address(svm)).createUint256("depth");
        vm.assume(dep >= 32 && dep < 40);
        vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
    }

    function check_D40_P1_addSupportedToken(bytes32 k, address a) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.addSupportedToken(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P5_addSupportedToken(address a) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.addSupportedToken(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: at depth 32..39 the owner call to addSupportedToken can succeed.
    function check_D40_W_addSupportedToken_expectFail(address a) public {
        _symStorageDepthDeep();
        vm.prank(pool.owner());
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.addSupportedToken, (a)));
        assert(!ok);
    }

    function check_D40_P1_removeSupportedToken(bytes32 k, address a) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.removeSupportedToken(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P5_removeSupportedToken(address a) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.removeSupportedToken(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: at depth 32..39 the owner call to removeSupportedToken can succeed.
    function check_D40_W_removeSupportedToken_expectFail(address a) public {
        _symStorageDepthDeep();
        vm.prank(pool.owner());
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.removeSupportedToken, (a)));
        assert(!ok);
    }

    function check_D40_P1_setVerifier(bytes32 k, address a) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.setVerifier(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P5_setVerifier(address a) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.setVerifier(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: at depth 32..39 the owner call to setVerifier can succeed.
    function check_D40_W_setVerifier_expectFail(address a) public {
        _symStorageDepthDeep();
        vm.prank(pool.owner());
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.setVerifier, (a)));
        assert(!ok);
    }

    function check_D40_P1_setAttestationRegistry(bytes32 k, address a) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.setAttestationRegistry(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P5_setAttestationRegistry(address a) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.setAttestationRegistry(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: at depth 32..39 the owner call to setAttestationRegistry can succeed.
    function check_D40_W_setAttestationRegistry_expectFail(address a) public {
        _symStorageDepthDeep();
        vm.prank(pool.owner());
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.setAttestationRegistry, (a)));
        assert(!ok);
    }

    function check_D40_P1_transferOwnership(bytes32 k, address a) public {
        _symStorageDepthLt40();
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.transferOwnership(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_D40_P5_transferOwnership(address a) public {
        _symStorageDepthLt40();
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.transferOwnership(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: at depth 32..39 the owner call to transferOwnership can succeed.
    function check_D40_W_transferOwnership_expectFail(address a) public {
        _symStorageDepthDeep();
        vm.prank(pool.owner());
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transferOwnership, (a)));
        assert(!ok);
    }

    /// Witness for the caller used by the P1/P5 checks: a symbolic caller reaches the owner success path.
    function check_D40_W_anyCaller_expectFail(address a, uint8 which) public {
        _symStorageDepthDeep();
        _anyCaller();
        bytes memory data;
        if (which == 0) data = abi.encodeCall(ShieldedPool.addSupportedToken, (a));
        else if (which == 1) data = abi.encodeCall(ShieldedPool.removeSupportedToken, (a));
        else if (which == 2) data = abi.encodeCall(ShieldedPool.setVerifier, (a));
        else if (which == 3) data = abi.encodeCall(ShieldedPool.setAttestationRegistry, (a));
        else data = abi.encodeCall(ShieldedPool.transferOwnership, (a));
        (bool ok,) = address(pool).call(data);
        assert(!ok);
    }

    // ---- probes: does enableSymbolicStorage make setUp-written slots symbolic? Each must FAIL. ----

    function check_PROBE_ownerSymbolic_expectFail() public {
        _symStorageDepthLt40();
        assert(pool.owner() == address(this));
    }

    function check_PROBE_sizeSymbolic_expectFail() public {
        _symStorageDepthLt40();
        assert(pool.getCommitmentCount() == 4);
    }

    function check_PROBE_spentNullifierSymbolic_expectFail() public {
        _symStorageDepthLt40();
        assert(pool.nullifiers(NUL0));
    }

    function check_PROBE_supportedTokenSymbolic_expectFail() public {
        _symStorageDepthLt40();
        assert(pool.supportedTokens(address(token)));
    }

    // ---- F40 = fresh pool, then symbolic storage. ----
    // The PROBE checks above PASS: enableSymbolicStorage keeps every slot written in setUp concrete
    // (owner, tree size 4, spent NUL0..NUL2, supported tokens, tree side nodes, root buffer).
    // F40 deploys a new pool whose constructor writes only verifier, registry, owner and the
    // reentrancy status, overwrites owner with a symbolic address, and stores a symbolic depth.
    // Everything else in pool storage is unwritten, so symbolic. The reentrancy status stays
    // NOT_ENTERED, which holds between any two external calls.

    function _freshSymPool(uint256 lo, uint256 hi) internal {
        pool = new ShieldedPool(verifierAddr, registryAddr);
        token.mint(address(pool), 1e30);
        vm.prank(user);
        token.approve(address(pool), type(uint256).max);
        svm.enableSymbolicStorage(address(pool));
        vm.store(address(pool), bytes32(uint256(110)), bytes32(uint256(uint160(svm.createAddress("owner")))));
        uint256 dep = SVMU(address(svm)).createUint256("depth");
        vm.assume(dep >= lo && dep < hi);
        vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
    }

    function check_F40PROBE_ownerSymbolic_expectFail(address x) public {
        _freshSymPool(0, 40);
        assert(pool.owner() != x);
    }

    function check_F40PROBE_sizeSymbolic_expectFail() public {
        _freshSymPool(0, 40);
        assert(pool.getCommitmentCount() < 2 ** 200);
    }

    function check_F40PROBE_nullifierSymbolic_expectFail(bytes32 k) public {
        _freshSymPool(0, 40);
        assert(!pool.nullifiers(k));
    }

    function check_F40PROBE_supportedTokenSymbolic_expectFail() public {
        _freshSymPool(0, 40);
        assert(!pool.supportedTokens(address(token)));
    }

    function check_F40PROBE_validRootSymbolic_expectFail(bytes32 r) public {
        _freshSymPool(0, 40);
        assert(!pool.validRoots(r));
    }

    // deposit
    function check_F40_P1_deposit(bytes32 k, bytes32 c, uint256 amount) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_deposit(bytes32 c, uint256 amount) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_F40_W_deposit_expectFail(bytes32 c, uint256 amount) public {
        _freshSymPool(32, 40);
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    // transfer
    function check_F40_P1_transfer(bytes32 k, bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_F40_W_transfer_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPool(32, 40);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    // withdraw
    function check_F40_P1_withdraw(bytes32 k, bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        try pool.withdraw("", n, address(token), amount, recipient, root) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_withdraw(bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        try pool.withdraw("", n, address(token), amount, recipient, root) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_F40_W_withdraw_expectFail(bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        _freshSymPool(32, 40);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.withdraw, ("", n, address(token), amount, recipient, root)));
        assert(!ok);
    }

    // addSupportedToken
    function check_F40_P1_addSupportedToken(bytes32 k, address a) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.addSupportedToken(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_addSupportedToken(address a) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.addSupportedToken(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: symbolic caller, depth 32..39, the call can succeed.
    function check_F40_W_addSupportedToken_expectFail(address a) public {
        _freshSymPool(32, 40);
        _anyCaller();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.addSupportedToken, (a)));
        assert(!ok);
    }

    // removeSupportedToken
    function check_F40_P1_removeSupportedToken(bytes32 k, address a) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.removeSupportedToken(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_removeSupportedToken(address a) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.removeSupportedToken(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: symbolic caller, depth 32..39, the call can succeed.
    function check_F40_W_removeSupportedToken_expectFail(address a) public {
        _freshSymPool(32, 40);
        _anyCaller();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.removeSupportedToken, (a)));
        assert(!ok);
    }

    // setVerifier
    function check_F40_P1_setVerifier(bytes32 k, address a) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.setVerifier(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_setVerifier(address a) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.setVerifier(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: symbolic caller, depth 32..39, the call can succeed.
    function check_F40_W_setVerifier_expectFail(address a) public {
        _freshSymPool(32, 40);
        _anyCaller();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.setVerifier, (a)));
        assert(!ok);
    }

    // setAttestationRegistry
    function check_F40_P1_setAttestationRegistry(bytes32 k, address a) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.setAttestationRegistry(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_setAttestationRegistry(address a) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.setAttestationRegistry(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: symbolic caller, depth 32..39, the call can succeed.
    function check_F40_W_setAttestationRegistry_expectFail(address a) public {
        _freshSymPool(32, 40);
        _anyCaller();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.setAttestationRegistry, (a)));
        assert(!ok);
    }

    // transferOwnership
    function check_F40_P1_transferOwnership(bytes32 k, address a) public {
        _freshSymPool(0, 40);
        vm.assume(pool.nullifiers(k));
        _anyCaller();
        try pool.transferOwnership(a) {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_F40_P5_transferOwnership(address a) public {
        _freshSymPool(0, 40);
        uint256 before = pool.getCommitmentCount();
        _anyCaller();
        try pool.transferOwnership(a) {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Witness: symbolic caller, depth 32..39, the call can succeed.
    function check_F40_W_transferOwnership_expectFail(address a) public {
        _freshSymPool(32, 40);
        _anyCaller();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transferOwnership, (a)));
        assert(!ok);
    }

    // ---- G40 = F40 plus the LeanIMT shape invariant size <= 2^depth (assumed, not checked) ----

    function _freshSymPoolShaped(uint256 lo, uint256 hi) internal {
        _freshSymPool(lo, hi);
        vm.assume(pool.getCommitmentCount() <= 2 ** uint256(vm.load(address(pool), bytes32(uint256(1)))));
    }

    function check_G40_P5_deposit(bytes32 c, uint256 amount) public {
        _freshSymPoolShaped(0, 40);
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_G40_P1_deposit(bytes32 k, bytes32 c, uint256 amount) public {
        _freshSymPoolShaped(0, 40);
        vm.assume(pool.nullifiers(k));
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_G40_W_deposit_expectFail(bytes32 c, uint256 amount) public {
        _freshSymPoolShaped(32, 40);
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    /// Cost probe: F40 setup with depth < 4 (run at --loop 8), deposit, P5.
    function check_F4_P5_deposit(bytes32 c, uint256 amount) public {
        _freshSymPool(0, 4);
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    /// Halmos cannot index a fixed array with a symbolic base slot (NotConcreteError), so this
    /// variant pins historicalRootIndex (slot 104) to a concrete 0. Everything else stays as F40.
    function check_F4i_P5_deposit(bytes32 c, uint256 amount) public {
        _freshSymPool(0, 4);
        vm.store(address(pool), bytes32(uint256(104)), bytes32(0));
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_F40i_P5_deposit(bytes32 c, uint256 amount) public {
        _freshSymPool(0, 40);
        vm.store(address(pool), bytes32(uint256(104)), bytes32(0));
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    // ---- depth cap and depth bands for deposit/transfer ----
    // Cap: 2 ** treeDepth in LeanIMT._insert is checked (Solidity panics for exponent > 255),
    // so a stored depth >= 256 must revert. R checks assume only depth >= 256 on the F40 pool.

    function _freshSymPoolGe(uint256 lo) internal {
        _freshSymPool(lo, type(uint256).max);
    }

    function _setSlot(uint256 slot, uint256 v) internal {
        vm.store(address(pool), bytes32(slot), bytes32(v));
    }

    function check_R256_deposit(bytes32 c, uint256 amount) public {
        _freshSymPoolGe(256);
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    function check_R256_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPoolGe(256);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    function check_R256i_deposit(bytes32 c, uint256 amount) public {
        _freshSymPoolGe(256);
        _setSlot(104, 0);
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    function check_R256i_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPoolGe(256);
        _setSlot(104, 0);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    // Cap witnesses: same F40 pool, depth in [250, 256), size pinned 5 and root index pinned 0
    // (existence only). Success must be reachable, so these must FAIL. Run at --loop 260.
    function check_RW255_deposit_expectFail(bytes32 c, uint256 amount) public {
        _freshSymPool(250, 256);
        _setSlot(0, 5);
        _setSlot(104, 0);
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    function check_RW255_transfer_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPool(250, 256);
        _setSlot(0, 5);
        _setSlot(104, 0);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    // Bands: F40 pool with depth in [lo, hi), root index pinned 0 (NotConcreteError guard).
    // Band bounds come from the environment so one source serves every band.
    function _band() internal {
        _freshSymPool(vm.envUint("BAND_LO"), vm.envUint("BAND_HI"));
        _setSlot(104, 0);
    }

    function check_B_P1_deposit(bytes32 k, bytes32 c, uint256 amount) public {
        _band();
        vm.assume(pool.nullifiers(k));
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_B_P5_deposit(bytes32 c, uint256 amount) public {
        _band();
        uint256 before = pool.getCommitmentCount();
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    function check_B_P1_transfer(bytes32 k, bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _band();
        vm.assume(pool.nullifiers(k));
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    function check_B_P5_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _band();
        uint256 before = pool.getCommitmentCount();
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.getCommitmentCount() >= before);
    }

    // Band witness: depth pinned to BAND_HI - 1 (the band top), size symbolic. Must FAIL.
    function check_B_W_deposit_expectFail(bytes32 c, uint256 amount) public {
        _freshSymPool(vm.envUint("BAND_HI") - 1, vm.envUint("BAND_HI"));
        _setSlot(104, 0);
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    function check_B_W_transfer_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPool(vm.envUint("BAND_HI") - 1, vm.envUint("BAND_HI"));
        _setSlot(104, 0);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    // Cap witness, lighter: depth taken from CAPW_D (concrete), size 5, root index 0. Must FAIL.
    function check_RWc_deposit_expectFail(bytes32 c, uint256 amount) public {
        uint256 dd = vm.envUint("CAPW_D");
        _freshSymPool(dd, dd + 1);
        _setSlot(0, 5);
        _setSlot(104, 0);
        vm.prank(user);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    function check_RWc_transfer_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        uint256 dd = vm.envUint("CAPW_D");
        _freshSymPool(dd, dd + 1);
        _setSlot(0, 5);
        _setSlot(104, 0);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    // ---- P3 re-entry with a FRESH, unspent nullifier ----
    // The inherited check_P3_spentBeforePay re-enters withdraw with the SAME nullifier, which the
    // spent-nullifier check already rejects, so it does not isolate the re-entrancy guard. Here the
    // payout hook re-enters withdraw with a second nullifier m that is unspent at that moment.
    // Each check rebuilds the setUp reached state (same operations, same inputs) on a new pool;
    // check_P3b_replayMatchesSetUp compares both replicas with the setUp pool.
    // Control: ShieldedPoolNoGuard, a harness-local copy of a04b8b3 with nonReentrant removed
    // from withdraw only. There the same re-entry must succeed, so the control check must FAIL.

    function _p3bPool(bool guarded, FreshHookToken fh) internal returns (ShieldedPool p) {
        if (guarded) p = new ShieldedPool(verifierAddr, registryAddr);
        else p = ShieldedPool(address(new ShieldedPoolNoGuard(verifierAddr, registryAddr)));
        p.addSupportedToken(address(token));
        p.addSupportedToken(address(hook));
        p.addSupportedToken(address(fh));
        token.mint(address(p), 1e30);
        hook.mint(address(p), 1e30);
        fh.mint(address(p), 1e30);
        vm.prank(user);
        token.approve(address(p), type(uint256).max);
        vm.prank(user);
        p.deposit("", bytes32(uint256(1)), address(token), 5, user, "");
        vm.prank(user);
        p.deposit("", bytes32(uint256(2)), address(token), 5, user, "");
        p.withdraw("", NUL0, address(token), 1, user, p.commitmentRoot());
        p.transfer("", [NUL1, NUL2], [bytes32(uint256(3)), bytes32(uint256(4))], p.commitmentRoot(), "");
    }

    function _p3bRun(bool guarded, bytes32 n, bytes32 m, uint256 amount, address recipient)
        internal
        returns (FreshHookToken fh, bool ok)
    {
        fh = new FreshHookToken();
        ShieldedPool p = _p3bPool(guarded, fh);
        vm.assume(!p.nullifiers(n));
        vm.assume(!p.nullifiers(m));
        vm.assume(m != n);
        fh.arm(address(p), n, m);
        (ok,) = address(p).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(fh), amount, recipient, p.commitmentRoot()))
        );
    }

    /// Guarded pool: the payout hook of a successful withdraw cannot re-enter withdraw with a fresh nullifier.
    function check_P3b_freshReentryFails(bytes32 n, bytes32 m, uint256 amount, address recipient) public {
        (FreshHookToken fh, bool ok) = _p3bRun(true, n, m, amount, recipient);
        if (ok) assert(!fh.reentryOk());
    }

    /// Guarded pool: on every successful withdraw the hook fired, saw n spent, saw m unspent, and the
    /// re-entry reverted with ReentrancyGuardReentrantCall (the guard, not a nullifier check).
    function check_P3b_freshReentryGuardError(bytes32 n, bytes32 m, uint256 amount, address recipient) public {
        (FreshHookToken fh, bool ok) = _p3bRun(true, n, m, amount, recipient);
        if (ok) {
            assert(fh.fired());
            assert(fh.sawSpent());
            assert(fh.freshUnspent());
            assert(fh.reentrySel() == ReentrancyGuard.ReentrancyGuardReentrantCall.selector);
        }
    }

    /// Witness (must FAIL): the guarded outer withdraw can succeed, so the two checks above are not vacuous.
    function check_W_P3b_withdrawSuccessReachable_expectFail(bytes32 n, bytes32 m, uint256 amount, address recipient)
        public
    {
        (, bool ok) = _p3bRun(true, n, m, amount, recipient);
        assert(!ok);
    }

    /// Control (must FAIL): check_P3b_freshReentryFails on the no-guard copy; the fresh re-entry succeeds there.
    function check_P3b_noGuard_freshReentryFails_expectFail(bytes32 n, bytes32 m, uint256 amount, address recipient)
        public
    {
        (FreshHookToken fh, bool ok) = _p3bRun(false, n, m, amount, recipient);
        if (ok) assert(!fh.reentryOk());
    }

    /// Both replicas equal the setUp pool on root, size, root window and the spent flags NUL0..NUL2.
    function check_P3b_replayMatchesSetUp() public {
        for (uint256 g = 0; g < 2; g++) {
            ShieldedPool p = _p3bPool(g == 0, new FreshHookToken());
            assert(p.commitmentRoot() == pool.commitmentRoot());
            assert(p.getCommitmentCount() == pool.getCommitmentCount());
            assert(p.historicalRootIndex() == pool.historicalRootIndex());
            for (uint256 i = 0; i < 4; i++) {
                assert(p.historicalRoots(i) == pool.historicalRoots(i));
            }
            assert(p.nullifiers(NUL0) && p.nullifiers(NUL1) && p.nullifiers(NUL2));
        }
    }
}

// ---- additions for the P3b checks ----
import {MockERC20} from "../../src/mocks/MockERC20.sol";
import {ReentrancyGuard} from "@openzeppelin-contracts/utils/ReentrancyGuard.sol";
import {ShieldedPoolNoGuard} from "./mutants/ShieldedPoolNoGuard.sol";

/// Payout hook for P3b: during the pool's payout it records whether the spent nullifier is set and
/// whether a second nullifier is still unspent, then re-enters withdraw with that FRESH nullifier.
contract FreshHookToken is MockERC20 {
    address public pool;
    bytes32 public watch;
    bytes32 public fresh;
    bool public armed;
    bool public fired;
    bool public sawSpent;
    bool public freshUnspent;
    bool public reentryOk;
    bytes4 public reentrySel;

    constructor() MockERC20("FreshHook", "FHOOK", 18) {}

    function arm(address _pool, bytes32 _watch, bytes32 _fresh) external {
        pool = _pool;
        watch = _watch;
        fresh = _fresh;
        armed = true;
    }

    function _update(address from, address to, uint256 value) internal override {
        super._update(from, to, value);
        if (armed && !fired && from == pool) {
            fired = true;
            sawSpent = ShieldedPool(pool).nullifiers(watch);
            freshUnspent = !ShieldedPool(pool).nullifiers(fresh);
            bytes memory ret;
            (reentryOk, ret) = pool.call(
                abi.encodeCall(
                    ShieldedPool.withdraw,
                    ("", fresh, address(this), 1, address(this), ShieldedPool(pool).commitmentRoot())
                )
            );
            if (ret.length >= 4) reentrySel = bytes4(ret);
        }
    }
}
