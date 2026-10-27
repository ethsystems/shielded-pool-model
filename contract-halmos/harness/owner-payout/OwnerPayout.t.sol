// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Halmos checks W10 (withdraw payout and verifier inputs) and G1 (owner actions) on ShieldedPool
// (ethsystems/pocs a04b8b3). The verifier inputs are kept in storage (no balances,
// so no 2^128 bound), the owner-effect frame covers the whole state, and owner-effect mutants are added.
// Built on the insert-callback and guards suite pattern: a fresh pool deployed inside each check, then symbolic storage.

import {Test} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {PoseidonT3Stub, SymRegistry} from "../insert-callback/InsertCallback.t.sol";

interface SVM9b {
    function createBytes32(string calldata name) external returns (bytes32);
    function createAddress(string calldata name) external returns (address);
    function createUint256(string calldata name) external returns (uint256);
    function enableSymbolicStorage(address) external;
    function snapshotState() external returns (bytes32);
    function snapshotStorage(address) external returns (uint256);
    function createCalldata(string calldata contractName, bool includeViewFunctions) external returns (bytes memory);
}

/// Verifier mock with a storage record. The pool calls verify* through IVerifier's view functions (STATICCALL),
/// so no code under that call can write storage (Halmos raises WriteInStaticContext, an EVM exceptional halt;
/// see check_PROBE_storageWritingVerifierNeverAccepts). The record is made in two phases of one check:
/// TRIP (mode 1): verifyWithdraw reverts with SawWithdraw(length, pi[0..4]); the pool rethrows these bytes.
///   The harness decodes them and writes them into this contract's storage (recLen, rec[0..4]) by setRecord.
/// COMPARE (mode 2): verifyWithdraw returns true if its inputs equal the stored record and otherwise reverts
///   with Diverged. It never returns false. The check asserts that Diverged never occurs, so acceptance does
///   not depend on the inputs being right.
contract RecVerifier is IVerifier {
    error SawWithdraw(uint256 len, bytes32 p0, bytes32 p1, bytes32 p2, bytes32 p3, bytes32 p4);
    error SawOther(bytes4 sig);
    error Diverged();

    uint256 public mode;
    bool public recHit;
    uint256 public recLen;
    bytes32[5] public rec;

    function setMode(uint256 m) external {
        mode = m;
    }

    function setRecord(uint256 len, bytes32 p0, bytes32 p1, bytes32 p2, bytes32 p3, bytes32 p4) external {
        recHit = true;
        recLen = len;
        rec[0] = p0;
        rec[1] = p1;
        rec[2] = p2;
        rec[3] = p3;
        rec[4] = p4;
    }

    function _other() internal view returns (bool) {
        if (mode == 1) revert SawOther(msg.sig);
        if (mode == 2) revert Diverged();
        return true;
    }

    function verifyDeposit(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _other();
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _other();
    }

    function verifyWithdraw(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        if (mode == 1) {
            if (pi.length >= 5) revert SawWithdraw(pi.length, pi[0], pi[1], pi[2], pi[3], pi[4]);
            revert SawWithdraw(pi.length, 0, 0, 0, 0, 0);
        }
        if (mode == 2) {
            if (!recHit || pi.length != recLen || pi.length < 5) revert Diverged();
            if (pi[0] != rec[0] || pi[1] != rec[1] || pi[2] != rec[2] || pi[3] != rec[3] || pi[4] != rec[4]) {
                revert Diverged();
            }
        }
        return true;
    }
}

/// Probe only: a verifier whose verifyWithdraw (same selector, declared non-view) writes its own storage.
contract StoreVerifier {
    uint256 public seen;

    function verifyWithdraw(bytes calldata, bytes32[] calldata pi) external returns (bool) {
        seen = pi.length;
        return true;
    }
}

/// Token mock that records every call it gets, in storage. transfer and transferFrom move nothing and return
/// true. Any other call (fallback) is counted and succeeds with no data. Getters do not count.
contract RecToken {
    uint256 public nTransfer;
    uint256 public nTransferFrom;
    uint256 public nOther;
    address public lastCaller;
    address public lastTo;
    uint256 public lastAmt;

    function transfer(address to, uint256 amt) external returns (bool) {
        nTransfer += 1;
        lastCaller = msg.sender;
        lastTo = to;
        lastAmt = amt;
        return true;
    }

    function transferFrom(address, address, uint256) external returns (bool) {
        nTransferFrom += 1;
        return true;
    }

    fallback() external {
        nOther += 1;
    }

    function calls() external view returns (uint256) {
        return nTransfer + nTransferFrom + nOther;
    }
}

contract OwnerPayoutTest is Test {
    SVM9b internal constant svm = SVM9b(address(uint160(uint256(keccak256("svm cheat code")))));
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    // Storage layout (forge inspect, outputs/storage-layout.txt): tree 0-3, historicalRoots 4-103,
    // historicalRootIndex 104, validRoots 105, nullifiers 106, supportedTokens 107, verifier 108,
    // attestationRegistry 109, owner 110.
    uint256 internal constant SLOT_SUPPORTED = 107;
    uint256 internal constant SLOT_VERIFIER = 108;
    uint256 internal constant SLOT_REGISTRY = 109;
    uint256 internal constant SLOT_OWNER = 110;
    /// Token B lives at a high address (>= 2^159), so token addresses with high bits reach success paths.
    address internal constant HIGH_TOKEN = address(uint160((uint256(0xF) << 156) + 0xB));

    ShieldedPool internal pool;
    RecVerifier internal verifier;
    StoreVerifier internal storeVerifier;
    SymRegistry internal registry;
    RecToken internal tokA;
    RecToken internal tokB;

    function _etchLib(string memory artifact, address at) internal {
        bytes memory init = vm.getCode(artifact);
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(at, tmp.code);
    }

    function setUp() public {
        _etchLib("LeanIMT.sol:LeanIMT", address(0xA1001));
        if (vm.envUint("POSEIDON_STUB") == 1) {
            vm.etch(address(0xA1002), address(new PoseidonT3Stub()).code);
        } else {
            _etchLib("PoseidonT3.sol:PoseidonT3", address(0xA1002));
        }
        verifier = new RecVerifier();
        storeVerifier = new StoreVerifier();
        registry = new SymRegistry();
        tokA = new RecToken();
        vm.etch(HIGH_TOKEN, type(RecToken).runtimeCode);
        tokB = RecToken(HIGH_TOKEN);
    }

    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    /// Fresh pool, symbolic storage. Constructor slots (verifier, registry, owner, reentrancy status) stay
    /// concrete unless a check overwrites them. With BAND_HI != 0 the tree depth is symbolic in
    /// [BAND_LO, BAND_HI), size <= 2^depth is assumed and historicalRootIndex is pinned to 0 (as in the insert-callback suite).
    function _fresh() internal {
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
        svm.enableSymbolicStorage(address(pool));
        bytes32 ar = svm.createBytes32("attRoot");
        registry.set(ar);
        uint256 hi = vm.envUint("BAND_HI");
        if (hi != 0) {
            vm.store(address(pool), bytes32(uint256(104)), bytes32(0));
            vm.assume(uint256(ar) < P);
            uint256 dep = svm.createUint256("depth");
            vm.assume(dep >= vm.envUint("BAND_LO") && dep < hi);
            vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
            vm.assume(pool.getCommitmentCount() <= (uint256(1) << dep));
        }
    }

    /// G1 setup: as _fresh, then the owner slot holds a fresh symbolic address; with allSym the verifier and
    /// registry slots do too (the sweep keeps the mock verifier and registry so that calls can succeed).
    function _freshG(bool allSym) internal {
        _fresh();
        vm.store(address(pool), bytes32(SLOT_OWNER), bytes32(uint256(uint160(svm.createAddress("owner")))));
        if (!allSym) return;
        vm.store(address(pool), bytes32(SLOT_VERIFIER), bytes32(uint256(uint160(svm.createAddress("verifierSlot")))));
        vm.store(address(pool), bytes32(SLOT_REGISTRY), bytes32(uint256(uint160(svm.createAddress("registrySlot")))));
    }

    // ================= W10: withdraw pays transfer(recipient, amount) on `token`, verifier sees the call =================

    function _wdData(bytes memory proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(ShieldedPool.withdraw, (proof, n, t, a, rcp, r));
    }

    /// If the TRIP-phase revert data is SawWithdraw(len, p0..p4), write it into the verifier's storage record.
    function _record(bytes memory ret1) internal {
        if (ret1.length != 196 || bytes4(ret1) != RecVerifier.SawWithdraw.selector) return;
        uint256 len;
        bytes32 w0;
        bytes32 w1;
        bytes32 w2;
        bytes32 w3;
        bytes32 w4;
        assembly {
            len := mload(add(ret1, 36))
            w0 := mload(add(ret1, 68))
            w1 := mload(add(ret1, 100))
            w2 := mload(add(ret1, 132))
            w3 := mload(add(ret1, 164))
            w4 := mload(add(ret1, 196))
        }
        verifier.setRecord(len, w0, w1, w2, w3, w4);
    }

    /// Phase 1 (TRIP): the call cannot succeed; if it reached verifyWithdraw, its inputs go into storage.
    /// Phase 2 (COMPARE): the same call from the same pool state; every verifyWithdraw call must equal the record.
    function _twoPhase(bytes memory data, address caller) internal returns (bool ok2) {
        verifier.setMode(1);
        uint256 p0 = svm.snapshotStorage(address(pool));
        vm.prank(caller);
        (bool ok1, bytes memory ret1) = address(pool).call(data);
        assert(!ok1);
        assert(svm.snapshotStorage(address(pool)) == p0);
        _record(ret1);
        verifier.setMode(2);
        vm.prank(caller);
        bytes memory ret2;
        (ok2, ret2) = address(pool).call(data);
        assert(ok2 || bytes4(ret2) != RecVerifier.Diverged.selector);
    }

    /// Every argument, the caller and every pool mapping and tree slot are symbolic, with full 256-bit ranges
    /// (nullifier and root, amount below 2^128 by the pool's own guard). t can alias any deployed account;
    /// only the two RecTokens (one at a high address) accept a transfer. For every successful withdraw:
    /// exactly one retained call reached the two tokens, and it is transfer(rcp, a) on t, sent by the pool;
    /// the verifier's recorded inputs (storage) are [n, t, a, rcp, r], length 5.
    function check_W10_withdrawPaysAndBindsInputs(
        bytes memory proof,
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        vm.assume(_twoPhase(_wdData(proof, n, t, a, rcp, r), caller));
        // token side
        assert(tokA.calls() + tokB.calls() == 1);
        RecToken moved = tokA.calls() == 1 ? tokA : tokB;
        assert(moved.nTransfer() == 1);
        assert(address(moved) == t);
        assert(moved.lastTo() == rcp);
        assert(moved.lastAmt() == a);
        assert(moved.lastCaller() == address(pool));
        // verifier side, read from storage
        assert(verifier.recHit());
        assert(verifier.recLen() == 5);
        assert(verifier.rec(0) == n);
        assert(verifier.rec(1) == bytes32(uint256(uint160(t))));
        assert(verifier.rec(2) == bytes32(a));
        assert(verifier.rec(3) == bytes32(uint256(uint160(rcp))));
        assert(verifier.rec(4) == r);
    }

    /// Witness (must FAIL): a withdraw can succeed in this setup, so the check above is not vacuous.
    function check_WIT_withdrawSucceeds_expectFail(bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller)
        public
    {
        _fresh();
        assert(!_twoPhase(_wdData("", n, t, a, rcp, r), caller));
    }

    /// Probe (must PASS): with a verifier that writes storage in verifyWithdraw, no withdraw succeeds. The
    /// write happens under the pool's STATICCALL and halts. This is why the record is made in two phases.
    function check_PROBE_storageWritingVerifierNeverAccepts(
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        vm.store(address(pool), bytes32(SLOT_VERIFIER), bytes32(uint256(uint160(address(storeVerifier)))));
        vm.prank(caller);
        (bool ok,) = address(pool).call(_wdData("", n, t, a, rcp, r));
        assert(!ok);
    }

    // ================= G1: owner-only functions =================

    function _call(address caller, bytes memory data) internal returns (bool ok, bytes4 sel, bool same) {
        bytes32 g0 = svm.snapshotState();
        vm.prank(caller);
        bytes memory ret;
        (ok, ret) = address(pool).call(data);
        sel = bytes4(ret);
        same = svm.snapshotState() == g0;
    }

    function _ownerData(uint256 which, address x) internal pure returns (bytes memory) {
        if (which == 0) return abi.encodeCall(ShieldedPool.addSupportedToken, (x));
        if (which == 1) return abi.encodeCall(ShieldedPool.removeSupportedToken, (x));
        if (which == 2) return abi.encodeCall(ShieldedPool.setVerifier, (x));
        if (which == 3) return abi.encodeCall(ShieldedPool.setAttestationRegistry, (x));
        return abi.encodeCall(ShieldedPool.transferOwnership, (x));
    }

    /// Non-owner call: reverts with OnlyOwner and leaves the whole state (storage, balance and code of every
    /// account) as it was. `core` drops the reason and state assertions and keeps only "did not succeed".
    function _nonOwner(uint256 which, address caller, address x, bool core) internal {
        _freshG(true);
        vm.assume(caller != pool.owner());
        (bool ok, bytes4 sel, bool same) = _call(caller, _ownerData(which, x));
        assert(!ok);
        if (core) return;
        assert(sel == ShieldedPool.OnlyOwner.selector);
        assert(same);
    }

    function check_G1_addToken_nonOwnerReverts(address caller, address x) public {
        _nonOwner(0, caller, x, false);
    }

    function check_G1_removeToken_nonOwnerReverts(address caller, address x) public {
        _nonOwner(1, caller, x, false);
    }

    function check_G1_setVerifier_nonOwnerReverts(address caller, address x) public {
        _nonOwner(2, caller, x, false);
    }

    function check_G1_setRegistry_nonOwnerReverts(address caller, address x) public {
        _nonOwner(3, caller, x, false);
    }

    function check_G1_transferOwnership_nonOwnerReverts(address caller, address x) public {
        _nonOwner(4, caller, x, false);
    }

    function check_G1core_addToken_nonOwnerFails(address caller, address x) public {
        _nonOwner(0, caller, x, true);
    }

    function check_G1core_removeToken_nonOwnerFails(address caller, address x) public {
        _nonOwner(1, caller, x, true);
    }

    function check_G1core_setVerifier_nonOwnerFails(address caller, address x) public {
        _nonOwner(2, caller, x, true);
    }

    function check_G1core_setRegistry_nonOwnerFails(address caller, address x) public {
        _nonOwner(3, caller, x, true);
    }

    function check_G1core_transferOwnership_nonOwnerFails(address caller, address x) public {
        _nonOwner(4, caller, x, true);
    }

    /// The one pool slot the owner function may change: supportedTokens[x] or the verifier, registry or owner slot.
    function _updSlot(uint256 which, address x) internal pure returns (bytes32) {
        if (which <= 1) return keccak256(abi.encode(x, SLOT_SUPPORTED));
        if (which == 2) return bytes32(SLOT_VERIFIER);
        if (which == 3) return bytes32(SLOT_REGISTRY);
        return bytes32(SLOT_OWNER);
    }

    /// Storage digests of every other account with storage (the libraries have none and are not called).
    function _others() internal returns (uint256[5] memory d) {
        d[0] = svm.snapshotStorage(address(this));
        d[1] = svm.snapshotStorage(address(verifier));
        d[2] = svm.snapshotStorage(address(registry));
        d[3] = svm.snapshotStorage(address(tokA));
        d[4] = svm.snapshotStorage(address(tokB));
    }

    /// Frame keys. Halmos's generic storage model keeps one array per key width (sevm.py GenericStorage,
    /// simple_hash): plain slots (256-bit keys), single-level mapping entries keccak(k . m) (769-bit keys) and
    /// dynamic-array elements keccak(m2) + i (513-bit keys). One fresh symbolic key per shape covers every slot
    /// of that shape: s (any plain slot), (k, m) (any mapping entry, any key, any base slot), (m2, i).
    struct Pre {
        bool s0;
        bytes32 u;
        bytes32 s;
        bytes32 v0;
        bytes32 k;
        uint256 m;
        bytes32 vm0;
        uint256 m2;
        uint256 i2;
        bytes32 va0;
        bytes32 g0;
        uint256[5] d0;
    }

    function _mapSlot(bytes32 k, uint256 m) internal pure returns (bytes32) {
        return keccak256(abi.encode(k, m));
    }

    function _arrSlot(uint256 m2, uint256 i2) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(abi.encode(m2))) + i2);
    }

    function _frameKeys(Pre memory p) internal {
        address a = address(pool);
        p.s = svm.createBytes32("frameSlot");
        p.v0 = vm.load(a, p.s);
        p.k = svm.createBytes32("frameMapKey");
        p.m = svm.createUint256("frameMapBase");
        p.vm0 = vm.load(a, _mapSlot(p.k, p.m));
        p.m2 = svm.createUint256("frameArrBase");
        p.i2 = svm.createUint256("frameArrIndex");
        p.va0 = vm.load(a, _arrSlot(p.m2, p.i2));
    }

    /// Stated precondition of success and the stated revert reason otherwise.
    function _expect(uint256 which, address x, bool s0) internal pure returns (bool pre, bytes4 err) {
        if (which == 0) {
            pre = x != address(0) && !s0;
            err = x == address(0) ? ShieldedPool.ZeroAddress.selector : ShieldedPool.TokenAlreadySupported.selector;
        } else if (which == 1) {
            pre = s0;
            err = ShieldedPool.TokenNotSupported.selector;
        } else {
            pre = x != address(0);
            err = ShieldedPool.ZeroAddress.selector;
        }
    }

    /// The stated update.
    function _assertUpdate(uint256 which, address x) internal view {
        if (which == 0) assert(pool.supportedTokens(x));
        else if (which == 1) assert(!pool.supportedTokens(x));
        else if (which == 2) assert(address(pool.verifier()) == x);
        else if (which == 3) assert(address(pool.attestationRegistry()) == x);
        else assert(pool.owner() == x);
    }

    /// Everything else unchanged: balances and code of every account (snapshotState bytes 0-15), the storage of
    /// every other account, and every pool slot of each shape other than the updated one (for which 0 and 1 the
    /// update is the mapping entry supportedTokens[x]; for 2-4 it is the plain slot u).
    function _assertFrame(uint256 which, address x, Pre memory p) internal {
        assert(bytes16(svm.snapshotState()) == bytes16(p.g0));
        uint256[5] memory d1 = _others();
        assert(d1[0] == p.d0[0]);
        assert(d1[1] == p.d0[1]);
        assert(d1[2] == p.d0[2]);
        assert(d1[3] == p.d0[3]);
        assert(d1[4] == p.d0[4]);
        address a = address(pool);
        if (which <= 1 || p.s != p.u) assert(vm.load(a, p.s) == p.v0);
        if (which > 1 || p.k != bytes32(uint256(uint160(x))) || p.m != SLOT_SUPPORTED) {
            assert(vm.load(a, _mapSlot(p.k, p.m)) == p.vm0);
        }
        assert(vm.load(a, _arrSlot(p.m2, p.i2)) == p.va0);
    }

    /// Owner call of an owner function with a symbolic argument x (run with --storage-layout generic, so the
    /// frame slot s is a fully symbolic 256-bit slot). It succeeds exactly when the stated precondition holds.
    /// On revert: the stated reason and the whole state unchanged. On success: the stated update, and every
    /// other part of the state unchanged (_assertFrame).
    function _effect(uint256 which, address x) internal {
        _freshG(true);
        Pre memory p;
        address o = pool.owner();
        p.s0 = pool.supportedTokens(x);
        p.u = _updSlot(which, x);
        _frameKeys(p);
        p.d0 = _others();
        p.g0 = svm.snapshotState();
        vm.prank(o);
        (bool ok, bytes memory ret) = address(pool).call(_ownerData(which, x));
        (bool pre, bytes4 err) = _expect(which, x, p.s0);
        if (!pre) {
            assert(!ok);
            assert(bytes4(ret) == err);
            assert(svm.snapshotState() == p.g0);
            return;
        }
        assert(ok);
        _assertUpdate(which, x);
        _assertFrame(which, x, p);
    }

    function check_G1_addToken_ownerEffect(address x) public {
        _effect(0, x);
    }

    function check_G1_removeToken_ownerEffect(address x) public {
        _effect(1, x);
    }

    function check_G1_setVerifier_ownerEffect(address x) public {
        _effect(2, x);
    }

    function check_G1_setRegistry_ownerEffect(address x) public {
        _effect(3, x);
    }

    function check_G1_transferOwnership_ownerEffect(address x) public {
        _effect(4, x);
    }

    /// Sweep over every non-view external function (Halmos createCalldata over the ShieldedPool ABI; view and
    /// pure functions excluded: a symbolic historicalRoots index is a symbolic base slot in the Solidity storage
    /// model). Bounds: bytes arguments of length 0 or 65, initial tree depth 0..3 with size <= 2^depth,
    /// historicalRootIndex 0, Poseidon stub, mock verifier and registry. From a symbolic non-owner caller, after
    /// one call: owner, verifier, registry and supportedTokens[y] (symbolic y) are unchanged.
    function check_G1_sweep_nonOwnerKeepsAdminState(address caller, address y) public {
        _freshG(false);
        vm.assume(caller != pool.owner());
        address o0 = pool.owner();
        address v0 = address(pool.verifier());
        address r0 = address(pool.attestationRegistry());
        bool sy0 = pool.supportedTokens(y);
        bytes memory data = svm.createCalldata("ShieldedPool", false);
        vm.prank(caller);
        address(pool).call(data);
        assert(pool.owner() == o0);
        assert(address(pool.verifier()) == v0);
        assert(address(pool.attestationRegistry()) == r0);
        assert(pool.supportedTokens(y) == sy0);
    }

    /// Witness for the sweep (must FAIL): some non-owner call in the sweep succeeds.
    function check_WIT_sweepSomeCallSucceeds_expectFail(address caller) public {
        _freshG(false);
        vm.assume(caller != pool.owner());
        bytes memory data = svm.createCalldata("ShieldedPool", false);
        vm.prank(caller);
        (bool ok,) = address(pool).call(data);
        assert(!ok);
    }
}

// ---- mutant controls: one test contract per mutant, in OwnerPayoutMutants.t.sol ----
