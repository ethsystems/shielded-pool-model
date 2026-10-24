// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {PoolSymbolicTest} from "../root-window/PoolSymbolic.t.sol";
import {PoolSymbolicStubTest, SVMU} from "../root-window/PoolSymbolicStub.t.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";

/// Root-window rule at a04b8b3 (one root per operation, recorded after its last insert).
/// Reached state from PoolSymbolicTest.setUp: deposit 1, deposit 2, withdraw, transfer 3+4.
/// produced[i] = root after i leaves. Post-operation roots: produced[1], produced[2], produced[4].
/// produced[3] is the mid-transfer root.
contract RootWindowTest is PoolSymbolicTest {
    /// One-root-per-operation form of P4 (real Poseidon, symbolic r).
    function check_RW_postOpRootsOnly(bytes32 r) public view {
        if (pool.isKnownRoot(r)) assert(r == produced[1] || r == produced[2] || r == produced[4]);
    }

    /// Exact window contents after the reached history (concrete).
    function check_RW_windowContents() public view {
        assert(pool.historicalRootIndex() == 3);
        assert(pool.historicalRoots(0) == produced[1]);
        assert(pool.historicalRoots(1) == produced[2]);
        assert(pool.historicalRoots(2) == produced[4]);
        assert(pool.historicalRoots(3) == bytes32(0));
    }

    /// After the transfer: post-operation root banked, intermediate root not known (concrete witness).
    function check_RW_transferPostOpNotIntermediate() public view {
        assert(pool.validRoots(produced[4]));
        assert(!pool.validRoots(produced[3]));
        assert(!pool.isKnownRoot(produced[3]));
    }
}

/// Same rule under the PoseidonT3 stub (an assumption, as in the root-window suite), so the transfer can have symbolic outputs.
contract RootWindowStubTest is PoolSymbolicStubTest {
    /// A fresh transfer with symbolic nullifiers and outputs: the post-op root is banked,
    /// the root between its two inserts is not known.
    function check_RWs_transferPostOpNotIntermediate(bytes32 a, bytes32 b, bytes32 c, bytes32 d) public {
        (bool ok,) = address(pool).call(
            abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], pool.commitmentRoot(), ""))
        );
        vm.assume(ok);
        bytes32 mid = shadow.ins(uint256(c));
        bytes32 fin = shadow.ins(uint256(d));
        assert(fin == pool.commitmentRoot());
        assert(pool.validRoots(fin));
        assert(!pool.isKnownRoot(mid));
    }

    function _freshTransfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d) internal returns (bytes32 mid, bytes32 fin) {
        (bool ok,) = address(pool).call(
            abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], pool.commitmentRoot(), ""))
        );
        vm.assume(ok);
        mid = shadow.ins(uint256(c));
        fin = shadow.ins(uint256(d));
    }

    function check_RWsDiag_finIsCurrent(bytes32 a, bytes32 b, bytes32 c, bytes32 d) public {
        (, bytes32 fin) = _freshTransfer(a, b, c, d);
        assert(fin == pool.commitmentRoot());
    }

    function check_RWsDiag_finBanked(bytes32 a, bytes32 b, bytes32 c, bytes32 d) public {
        (, bytes32 fin) = _freshTransfer(a, b, c, d);
        assert(pool.validRoots(fin));
    }

    function check_RWsDiag_midNotKnown(bytes32 a, bytes32 b, bytes32 c, bytes32 d) public {
        (bytes32 mid, bytes32 fin) = _freshTransfer(a, b, c, d);
        assert(!pool.isKnownRoot(mid));
    }

    /// Mid root not known, unless the stub hash makes it collide with a root that IS legitimately
    /// known (the post-op root or a pre-state window root). Real Poseidon collisions are assumed away.
    function check_RWs_midNotKnownModCollision(bytes32 a, bytes32 b, bytes32 c, bytes32 d) public {
        (bytes32 mid, bytes32 fin) = _freshTransfer(a, b, c, d);
        vm.assume(mid != fin && mid != produced[1] && mid != produced[2] && mid != produced[4]);
        assert(!pool.isKnownRoot(mid));
    }

    /// Witness: the guarded path of check_RWs_midNotKnownModCollision is reachable.
    function check_RWs_W_midNoCollision_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d) public {
        (bytes32 mid, bytes32 fin) = _freshTransfer(a, b, c, d);
        vm.assume(mid != fin && mid != produced[1] && mid != produced[2] && mid != produced[4]);
        assert(false);
    }

    function _depthLt40() internal returns (uint256 idx) {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        uint256 dep = SVMU(address(svm)).createUint256("depth");
        vm.assume(dep < 40);
        vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
        idx = pool.historicalRootIndex();
        vm.assume(idx < 100);
    }

    /// One-step rule from arbitrary storage (depth < 40): a successful transfer writes exactly
    /// one window slot, at the old index, holding the post-operation root.
    function check_RWd_transfer(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        uint256 idx = _depthLt40();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        vm.assume(ok);
        bytes32 r = pool.commitmentRoot();
        assert(pool.historicalRootIndex() == (idx + 1) % 100);
        assert(pool.historicalRoots(idx) == r);
        assert(pool.validRoots(r));
    }

    function check_RWd_deposit(bytes32 c, uint256 amount) public {
        uint256 idx = _depthLt40();
        vm.prank(user);
        (bool ok,) =
            address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        vm.assume(ok);
        bytes32 r = pool.commitmentRoot();
        assert(pool.historicalRootIndex() == (idx + 1) % 100);
        assert(pool.historicalRoots(idx) == r);
        assert(pool.validRoots(r));
    }

    /// Witness for check_RWd_transfer: a successful transfer exists in that setup.
    function check_RWd_W_transfer_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _depthLt40();
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    /// Deep witness: with depth 32..39 a successful transfer still exists, so check_RWd_transfer's
    /// PASS covers deep trees (`bounds: []` alone does not show this).
    function check_RWd_Wdeep_transfer_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _depthLt40();
        vm.assume(uint256(vm.load(address(pool), bytes32(uint256(1)))) >= 32);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    // ---- Fresh pool (F40 style): every slot symbolic except verifier, registry, reentrancy
    // status; owner symbolic; depth in [0, 4); root index symbolic in [0, 100).
    // ROOT_INDEX provides a concrete fallback; SYMBOLIC_INDEX=1 selects the generic-layout run.

    function _index() internal returns (uint256 idx) {
        if (vm.envUint("SYMBOLIC_INDEX") == 1) {
            idx = SVMU(address(svm)).createUint256("historicalRootIndex");
            vm.assume(idx < 100);
        } else {
            idx = vm.envUint("ROOT_INDEX");
            require(idx < 100);
        }
    }

    function _freshIdx(uint256 idx) internal {
        _freshSymPool(0, 4);
        _setSlot(104, idx);
    }

    function check_FRW_deposit_index(bytes32 c, uint256 amount) public {
        uint256 idx = _index();
        _freshIdx(idx);
        bytes32 evicted = pool.historicalRoots(idx);
        vm.prank(user);
        (bool ok,) =
            address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        vm.assume(ok);
        bytes32 r = pool.commitmentRoot();
        assert(pool.historicalRootIndex() == (idx + 1) % 100);
        assert(pool.historicalRoots(idx) == r);
        assert(pool.validRoots(r));
        if (evicted != r && evicted != bytes32(0)) assert(!pool.validRoots(evicted));
    }

    function check_FRW_transfer_index(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        uint256 idx = _index();
        _freshIdx(idx);
        bytes32 evicted = pool.historicalRoots(idx);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        vm.assume(ok);
        bytes32 r = pool.commitmentRoot();
        assert(pool.historicalRootIndex() == (idx + 1) % 100);
        assert(pool.historicalRoots(idx) == r);
        assert(pool.validRoots(r));
        if (evicted != r && evicted != bytes32(0)) assert(!pool.validRoots(evicted));
    }

    function check_FRW_W_deposit_expectFail(bytes32 c, uint256 amount) public {
        _freshSymPool(3, 4);
        _setSlot(104, _index());
        vm.prank(user);
        (bool ok,) =
            address(pool).call(abi.encodeCall(ShieldedPool.deposit, ("", c, address(token), amount, user, "")));
        assert(!ok);
    }

    function check_FRW_W_transfer_expectFail(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        _freshSymPool(3, 4);
        _setSlot(104, _index());
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }
}
