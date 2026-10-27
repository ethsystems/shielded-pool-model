// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Two narrow Halmos checks on ShieldedPool (ethsystems/pocs a04b8b3) and the LeanIMT library it links
// (zk-kit a171c845). D5: a deposit of a commitment that is already a leaf reaches the library's duplicate
// guard with that commitment and reverts with no retained state change. X1: with the reentrancy status
// set to ENTERED, deposit, transfer and withdraw revert at the guard before any insertion, nullifier write
// or token call. Pattern of the insert-callback suite: a fresh pool per check, then symbolic storage; the real LeanIMT and
// PoseidonT3 code etched at the linked addresses. Mutant controls at the end.
//
// Env read by setUp/_fresh:
//   LIBMODE       0 = LeanIMT at its link address; 1 = LibProbe there, LeanIMT at 0xA1003;
//                 2 = TripLib there (any library call reverts Trip(4)).
//   POSEIDON_STUB 1 = keccak stub for PoseidonT3 (ASSUMPTION, band runs only); 0 = real PoseidonT3.
//   PIN_IDX       1 = historicalRootIndex (slot 104) pinned to 0; 0 = left symbolic.
//   BAND_LO/HI    BAND_HI != 0: tree depth in [BAND_LO, BAND_HI) and size <= 2^depth; 0: no tree bound.

import {Test} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {ReentrancyGuard} from "@openzeppelin-contracts/utils/ReentrancyGuard.sol";
import {ShieldedPool_M_NR_D} from "./mutants/ShieldedPool_M_NR_D.sol";
import {ShieldedPool_M_NR_T} from "./mutants/ShieldedPool_M_NR_T.sol";
import {ShieldedPool_M_NR_W} from "./mutants/ShieldedPool_M_NR_W.sol";
import {ShieldedPool_M_SKIP} from "./mutants/ShieldedPool_M_SKIP.sol";
import {ShieldedPool_M_ARG} from "./mutants/ShieldedPool_M_ARG.sol";

interface SVM {
    function createBytes32(string calldata name) external returns (bytes32);
    function createAddress(string calldata name) external returns (address);
    function createUint256(string calldata name) external returns (uint256);
    function createBool(string calldata name) external returns (bool);
    function enableSymbolicStorage(address) external;
    function snapshotState() external returns (bytes32);
}

/// Tripwire: a mock or library reached in a tripwire run reverts with Trip(id). The pool never catches
/// these reverts (high-level calls, SafeERC20 with bubbling, library delegatecalls), so a call that
/// reached one ends with Trip data, never with a bare 4-byte guard selector.
error Trip(uint256 id);

/// Verifier mock. mode 0: accept; mode 1: return `ans`; mode 2: tripwire Trip(1).
contract SwitchVerifier is IVerifier {
    uint256 public mode;
    bool public ans;

    function set(uint256 m, bool a) external {
        mode = m;
        ans = a;
    }

    function _v() internal view returns (bool) {
        if (mode == 2) revert Trip(1);
        return mode == 0 || ans;
    }

    function verifyDeposit(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _v();
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _v();
    }

    function verifyWithdraw(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _v();
    }
}

/// Registry mock. mode 0: return `root`; mode 2: tripwire Trip(2).
contract SwitchRegistry {
    uint256 public mode;
    bytes32 public root;

    function set(uint256 m, bytes32 r) external {
        mode = m;
        root = r;
    }

    function attestationRoot() external view returns (bytes32) {
        if (mode == 2) revert Trip(2);
        return root;
    }

    function attestationLeaves(bytes32) external pure returns (bool) {
        return false;
    }
}

interface VmLoad {
    function load(address target, bytes32 slot) external view returns (bytes32);
}

/// Token mock. mode 0: moves nothing, counts the call, returns true; mode 1: as mode 0 and records the
/// caller's reentrancy status slot at the first call; mode 2: tripwire Trip(3).
contract SwitchToken {
    VmLoad internal constant VM = VmLoad(address(uint160(uint256(keccak256("hevm cheat code")))));
    bytes32 internal constant LOCK = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;
    uint256 public mode;
    uint256 public calls;
    uint256 public lockAtCall;

    function setMode(uint256 m) external {
        mode = m;
    }

    function _seen() internal {
        if (mode == 2) revert Trip(3);
        calls += 1;
        if (mode == 1 && calls == 1) lockAtCall = uint256(VM.load(msg.sender, LOCK));
    }

    function transferFrom(address, address, uint256) external returns (bool) {
        _seen();
        return true;
    }

    function transfer(address, uint256) external returns (bool) {
        _seen();
        return true;
    }
}

/// X1 library tripwire, etched at the LeanIMT link address: any library call (insert, has, root)
/// reverts with Trip(4).
contract TripLib {
    fallback() external {
        revert Trip(4);
    }
}

/// D5 recorder, etched at the LeanIMT link address. It delegatecalls the real library at 0xA1003, so the
/// library runs unchanged in the pool's storage. Success: the library's return data, unchanged. Revert:
/// the library's revert data followed by the full calldata the probe received (selector, storage slot,
/// leaf), so the caller sees which library call raised the error and with which arguments.
contract LibProbe {
    fallback() external {
        (bool ok, bytes memory ret) = address(0xA1003).delegatecall(msg.data);
        if (!ok) {
            bytes memory out = bytes.concat(ret, msg.data);
            assembly {
                revert(add(out, 32), mload(out))
            }
        }
        assembly {
            return(add(ret, 32), mload(ret))
        }
    }
}

/// ASSUMPTION (as in the root-window and insert-callback suites), used only in band runs: PoseidonT3.hash replaced by keccak256 of its
/// inputs reduced into the field (same selector). Says nothing about hash values.
contract PoseidonT3Stub {
    uint256 constant F = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    function hash(uint256[2] memory x) public pure returns (uint256) {
        return uint256(keccak256(abi.encode(x[0], x[1]))) % F;
    }
}

contract DuplicateLockTest is Test {
    SVM internal constant svm = SVM(address(uint160(uint256(keccak256("svm cheat code")))));
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant MAX_AMOUNT = 1 << 128;
    /// OpenZeppelin 5.x ReentrancyGuard status slot (ERC-7201): 1 NOT_ENTERED, 2 ENTERED.
    bytes32 internal constant LOCK = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;
    bytes4 internal constant LEAF_EXISTS = bytes4(keccak256("LeafAlreadyExists()"));
    bytes4 internal constant GUARD = ReentrancyGuard.ReentrancyGuardReentrantCall.selector;
    bytes4 internal constant INSERT_SEL = bytes4(keccak256("insert(LeanIMTData storage,uint256)"));
    address internal constant LIB = address(0xA1001);
    address internal constant POS = address(0xA1002);
    address internal constant REAL_LIB = address(0xA1003);

    ShieldedPool internal pool;
    SwitchVerifier internal verifier;
    SwitchRegistry internal registry;
    SwitchToken internal token;

    function _etch(string memory artifact, address at) internal {
        bytes memory init = vm.getCode(artifact);
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(at, tmp.code);
    }

    /// The DUP mutant test contract overrides this with the library copy that lacks the duplicate check.
    function _libArtifact() internal pure virtual returns (string memory) {
        return "LeanIMT.sol:LeanIMT";
    }

    function setUp() public {
        uint256 lm = vm.envUint("LIBMODE");
        if (lm == 0) {
            _etch(_libArtifact(), LIB);
        } else if (lm == 1) {
            _etch(_libArtifact(), REAL_LIB);
            vm.etch(LIB, address(new LibProbe()).code);
        } else {
            vm.etch(LIB, address(new TripLib()).code);
        }
        if (vm.envUint("POSEIDON_STUB") == 1) {
            vm.etch(POS, address(new PoseidonT3Stub()).code);
        } else {
            _etch("PoseidonT3.sol:PoseidonT3", POS);
        }
        verifier = new SwitchVerifier();
        registry = new SwitchRegistry();
        token = new SwitchToken();
    }

    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    /// Fresh pool, then symbolic storage. Slots the constructor wrote stay concrete: verifier, registry,
    /// owner and the reentrancy status (1, NOT_ENTERED). Mocks reset to accept / benign.
    function _fresh() internal {
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
        svm.enableSymbolicStorage(address(pool));
        if (vm.envUint("PIN_IDX") == 1) vm.store(address(pool), bytes32(uint256(104)), bytes32(0));
        bytes32 ar = svm.createBytes32("attRoot");
        vm.assume(uint256(ar) < P);
        registry.set(0, ar);
        verifier.set(0, false);
        token.setMode(0);
        uint256 hi = vm.envUint("BAND_HI");
        if (hi != 0) {
            uint256 dep = svm.createUint256("depth");
            vm.assume(dep >= vm.envUint("BAND_LO") && dep < hi);
            vm.store(address(pool), bytes32(uint256(1)), bytes32(dep));
            vm.assume(pool.getCommitmentCount() <= (uint256(1) << dep));
        }
    }

    function _leafIdx(bytes32 x) internal view returns (uint256) {
        return uint256(vm.load(address(pool), keccak256(abi.encode(uint256(x), uint256(3)))));
    }

    function _known(bytes32 r) internal view returns (bool) {
        return r == pool.commitmentRoot() || pool.validRoots(r);
    }

    /// Every deposit guard of ShieldedPool.sol:145-149 and 163 passes (token = the mock token).
    function _depPass(bytes32 c, uint256 a, address f) internal view {
        vm.assume(pool.supportedTokens(address(token)));
        vm.assume(a != 0 && a < MAX_AMOUNT);
        vm.assume(f != address(0));
        vm.assume(uint256(c) < P);
    }

    /// Every transfer guard of ShieldedPool.sol:195-204 and 218 passes.
    function _trPass(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r) internal view {
        vm.assume(n0 != n1);
        vm.assume(!pool.nullifiers(n0) && !pool.nullifiers(n1));
        vm.assume(_known(r));
        vm.assume(uint256(n0) < P && uint256(n1) < P && uint256(c0) < P && uint256(c1) < P && uint256(r) < P);
    }

    /// Every withdraw guard of ShieldedPool.sol:254-263 and 275 passes (token = the mock token).
    function _wdPass(bytes32 n, uint256 a, address rcp, bytes32 r) internal view {
        vm.assume(pool.supportedTokens(address(token)));
        vm.assume(a != 0 && a < MAX_AMOUNT);
        vm.assume(rcp != address(0));
        vm.assume(!pool.nullifiers(n));
        vm.assume(_known(r));
        vm.assume(uint256(n) < P && uint256(r) < P);
    }

    function _dep(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note)
        internal
        returns (bool ok, bytes memory ret)
    {
        vm.prank(f);
        (ok, ret) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, (proof, c, address(token), a, f, note)));
    }

    function _tr(bytes memory proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note)
        internal
        returns (bool ok, bytes memory ret)
    {
        (ok, ret) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, (proof, [n0, n1], [c0, c1], r, note)));
    }

    function _wd(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r)
        internal
        returns (bool ok, bytes memory ret)
    {
        (ok, ret) = address(pool).call(abi.encodeCall(ShieldedPool.withdraw, (proof, n, address(token), a, rcp, r)));
    }

    // ---------------------------------------------------------------------------------------------
    // D5: a deposit of a commitment that is already a leaf (ShieldedPool.sol:169, InternalLeanIMT.sol:45)
    // ---------------------------------------------------------------------------------------------

    /// D5-R. Every other deposit guard passes and the verifier accepts. A commitment c with 0 < c < P and
    /// leaves[c] != 0 makes the deposit revert with exactly the 4-byte LeafAlreadyExists selector, and the
    /// retained state of every account is unchanged. The token is a tripwire, so the exact revert data
    /// also shows that no token call happened.
    function check_D5_dupReverts(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _fresh();
        token.setMode(2);
        _depPass(c, a, f);
        vm.assume(uint256(c) != 0 && _leafIdx(c) != 0);
        bytes32 g0 = svm.snapshotState();
        (bool ok, bytes memory ret) = _dep(proof, c, a, f, note);
        assert(!ok);
        assert(ret.length == 4 && bytes4(ret) == LEAF_EXISTS);
        assert(svm.snapshotState() == g0);
    }

    /// D5-P (LIBMODE=1). Same premises. The library call that raised LeafAlreadyExists was
    /// insert(LeanIMTData storage, uint256) on storage slot 0 (the pool's _tree) with leaf == c.
    /// Revert data seen here: error selector (4) ++ library selector (4) ++ slot (32) ++ leaf (32).
    function check_D5_dupProbe(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _fresh();
        token.setMode(2);
        _depPass(c, a, f);
        vm.assume(uint256(c) != 0 && _leafIdx(c) != 0);
        bytes32 g0 = svm.snapshotState();
        (bool ok, bytes memory ret) = _dep(proof, c, a, f, note);
        assert(!ok);
        assert(ret.length == 72);
        uint256 w0;
        uint256 slot;
        uint256 leaf;
        assembly {
            w0 := mload(add(ret, 32))
            slot := mload(add(ret, 40))
            leaf := mload(add(ret, 72))
        }
        assert(bytes4(bytes32(w0)) == LEAF_EXISTS);
        assert(bytes4(bytes32(w0 << 32)) == INSERT_SEL);
        assert(slot == 0);
        assert(leaf == uint256(c));
        assert(svm.snapshotState() == g0);
    }

    /// D5-U. No guard premise: any caller, token, amount, funder, attestation root, verifier answer and
    /// reentrancy status. A deposit of any c with leaves[c] != 0 never succeeds and leaves retained state
    /// unchanged.
    function check_D5_dupAnyGuards(
        bytes memory proof,
        bytes32 c,
        address tok,
        uint256 a,
        address f,
        address caller,
        bytes memory note
    ) public {
        _fresh();
        vm.store(address(pool), LOCK, bytes32(svm.createUint256("lockStatus")));
        verifier.set(1, svm.createBool("verifierAnswer"));
        registry.set(0, svm.createBytes32("anyAttRoot"));
        vm.assume(_leafIdx(c) != 0);
        bytes32 g0 = svm.snapshotState();
        vm.prank(caller);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, (proof, c, tok, a, f, note)));
        assert(!ok);
        assert(svm.snapshotState() == g0);
    }

    /// D5-C (core, for the mutant controls). D5-R premises with a benign token. Sole assertion: the
    /// deposit does not succeed. A counterexample is a successful duplicate deposit.
    function check_D5_dupCore(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _fresh();
        _depPass(c, a, f);
        vm.assume(uint256(c) != 0 && _leafIdx(c) != 0);
        (bool ok,) = _dep(proof, c, a, f, note);
        assert(!ok);
    }

    /// Witness (must FAIL): under the D5-C premises with a new leaf, a deposit can succeed.
    function check_WIT_D5_newLeafSucceeds_expectFail(bytes32 c, uint256 a, address f) public {
        _fresh();
        _depPass(c, a, f);
        vm.assume(uint256(c) != 0 && _leafIdx(c) == 0);
        (bool ok,) = _dep("", c, a, f, "");
        assert(!ok);
    }

    // ---------------------------------------------------------------------------------------------
    // X1: entry rejection while the reentrancy status is ENTERED (lock held)
    // ---------------------------------------------------------------------------------------------

    function _lock() internal {
        vm.store(address(pool), LOCK, bytes32(uint256(2)));
    }

    function _tripAll() internal {
        verifier.set(2, false);
        registry.set(2, 0);
        token.setMode(2);
    }

    function _guardOnly(bool ok, bytes memory ret) internal pure {
        assert(!ok);
        assert(ret.length == 4 && bytes4(ret) == GUARD);
    }

    function _depData(bytes memory proof, bytes32 c, address tok, uint256 a, address f, bytes memory note)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(ShieldedPool.deposit, (proof, c, tok, a, f, note));
    }

    function _trData(bytes memory proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(ShieldedPool.transfer, (proof, [n0, n1], [c0, c1], r, note));
    }

    function _wdData(bytes memory proof, bytes32 n, address tok, uint256 a, address rcp, bytes32 r)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(ShieldedPool.withdraw, (proof, n, tok, a, rcp, r));
    }

    /// X1-L (LIBMODE=2, every mock a tripwire). Lock held, all arguments, caller and storage symbolic
    /// except the constructor slots: the call reverts with exactly the 4-byte ReentrancyGuardReentrantCall
    /// selector and retained state is unchanged. Exact data excludes any call to the verifier, registry,
    /// library (insertion, root read) or token before the revert.
    function check_X1_lockedDeposit(
        bytes memory proof,
        bytes32 c,
        address tok,
        uint256 a,
        address f,
        address caller,
        bytes memory note
    ) public {
        _fresh();
        _lock();
        _tripAll();
        bytes32 g0 = svm.snapshotState();
        vm.prank(caller);
        (bool ok, bytes memory ret) = address(pool).call(_depData(proof, c, tok, a, f, note));
        _guardOnly(ok, ret);
        assert(svm.snapshotState() == g0);
    }

    function check_X1_lockedTransfer(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        address caller,
        bytes memory note
    ) public {
        _fresh();
        _lock();
        _tripAll();
        bytes32 g0 = svm.snapshotState();
        vm.prank(caller);
        (bool ok, bytes memory ret) = address(pool).call(_trData(proof, n0, n1, c0, c1, r, note));
        _guardOnly(ok, ret);
        assert(svm.snapshotState() == g0);
    }

    function check_X1_lockedWithdraw(
        bytes memory proof,
        bytes32 n,
        address tok,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        _lock();
        _tripAll();
        bytes32 g0 = svm.snapshotState();
        vm.prank(caller);
        (bool ok, bytes memory ret) = address(pool).call(_wdData(proof, n, tok, a, rcp, r));
        _guardOnly(ok, ret);
        assert(svm.snapshotState() == g0);
    }

    /// X1-S (LIBMODE=2, tripwires). The same calls made by STATICCALL. Any SSTORE, TSTORE, LOG or CREATE
    /// before the revert would halt the static frame with empty return data. Exact guard data on every
    /// path therefore shows the guard revert precedes every state write, including the nullifier
    /// writes (ShieldedPool.sol:226-227, 283) and the tree writes inside the library.
    function check_X1s_lockedDeposit(bytes memory proof, bytes32 c, address tok, uint256 a, address f, bytes memory note)
        public
    {
        _fresh();
        _lock();
        _tripAll();
        (bool ok, bytes memory ret) = address(pool).staticcall(_depData(proof, c, tok, a, f, note));
        _guardOnly(ok, ret);
    }

    function check_X1s_lockedTransfer(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        _lock();
        _tripAll();
        (bool ok, bytes memory ret) = address(pool).staticcall(_trData(proof, n0, n1, c0, c1, r, note));
        _guardOnly(ok, ret);
    }

    function check_X1s_lockedWithdraw(bytes memory proof, bytes32 n, address tok, uint256 a, address rcp, bytes32 r)
        public
    {
        _fresh();
        _lock();
        _tripAll();
        (bool ok, bytes memory ret) = address(pool).staticcall(_wdData(proof, n, tok, a, rcp, r));
        _guardOnly(ok, ret);
    }

    /// X1-R (LIBMODE=2, tripwires): arbitrary calldata after the entry's selector, `body` symbolic with the
    /// lengths given by --default-bytes-lengths (non-canonical encodings included). Lock held: the call
    /// reverts with either exactly the guard selector or empty data (the dispatcher's ABI decoder rejects
    /// before the function body; the stock body has no empty revert and every mock and library call
    /// here ends in Trip data). Retained state is unchanged. The same calldata by STATICCALL returns the
    /// same data, so on the guard paths no write precedes the revert.
    function _x1raw(bytes4 sel, bytes memory body, address caller) internal {
        _fresh();
        _lock();
        _tripAll();
        bytes memory data = bytes.concat(sel, body);
        bytes32 g0 = svm.snapshotState();
        vm.prank(caller);
        (bool ok, bytes memory ret) = address(pool).call(data);
        assert(!ok);
        assert(ret.length == 0 || (ret.length == 4 && bytes4(ret) == GUARD));
        assert(svm.snapshotState() == g0);
        (bool sok, bytes memory sret) = address(pool).staticcall(data);
        assert(!sok);
        assert(keccak256(sret) == keccak256(ret));
    }

    function check_X1raw_lockedDeposit(bytes memory body, address caller) public {
        _x1raw(ShieldedPool.deposit.selector, body, caller);
    }

    function check_X1raw_lockedTransfer(bytes memory body, address caller) public {
        _x1raw(ShieldedPool.transfer.selector, body, caller);
    }

    function check_X1raw_lockedWithdraw(bytes memory body, address caller) public {
        _x1raw(ShieldedPool.withdraw.selector, body, caller);
    }

    /// X1-C (core, for the mutant controls; LIBMODE=0, benign mocks). Lock held and every other guard
    /// passes. Sole assertion: the call does not succeed. A counterexample is a successful call while
    /// the lock is held.
    function check_X1core_lockedWithdraw(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _fresh();
        _lock();
        _wdPass(n, a, rcp, r);
        (bool ok,) = _wd(proof, n, a, rcp, r);
        assert(!ok);
    }

    function check_X1core_lockedDeposit(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _fresh();
        _lock();
        _depPass(c, a, f);
        vm.assume(uint256(c) != 0 && _leafIdx(c) == 0);
        (bool ok,) = _dep(proof, c, a, f, note);
        assert(!ok);
    }

    function check_X1core_lockedTransfer(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        _lock();
        _trPass(n0, n1, c0, c1, r);
        vm.assume(uint256(c0) != 0 && uint256(c1) != 0 && c0 != c1 && _leafIdx(c0) == 0 && _leafIdx(c1) == 0);
        (bool ok,) = _tr(proof, n0, n1, c0, c1, r, note);
        assert(!ok);
    }

    /// X1-ACQ observation (separate obligation, scoped evidence only). Deposit (ShieldedPool.sol:178) and
    /// withdraw (:286) each make one non-static external call, the token call; it is their only point
    /// where a callee can re-enter with a writable context. On every successful call, exactly one token
    /// call happens, the status slot reads ENTERED (2) at that call, and NOT_ENTERED (1) after return.
    function check_X1acq_withdraw(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _fresh();
        token.setMode(1);
        _wdPass(n, a, rcp, r);
        (bool ok,) = _wd(proof, n, a, rcp, r);
        vm.assume(ok);
        assert(token.calls() == 1);
        assert(token.lockAtCall() == 2);
        assert(uint256(vm.load(address(pool), LOCK)) == 1);
    }

    function check_X1acq_deposit(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _fresh();
        token.setMode(1);
        _depPass(c, a, f);
        (bool ok,) = _dep(proof, c, a, f, note);
        vm.assume(ok);
        assert(token.calls() == 1);
        assert(token.lockAtCall() == 2);
        assert(uint256(vm.load(address(pool), LOCK)) == 1);
    }

    /// Witnesses (must FAIL): the X1-C premises with the status left at NOT_ENTERED; the call can succeed.
    function check_WIT_X1_unlockedWithdrawSucceeds_expectFail(bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _fresh();
        _wdPass(n, a, rcp, r);
        (bool ok,) = _wd("", n, a, rcp, r);
        assert(!ok);
    }

    function check_WIT_X1_unlockedDepositSucceeds_expectFail(bytes32 c, uint256 a, address f) public {
        _fresh();
        _depPass(c, a, f);
        vm.assume(uint256(c) != 0 && _leafIdx(c) == 0);
        (bool ok,) = _dep("", c, a, f, "");
        assert(!ok);
    }

    function check_WIT_X1_unlockedTransferSucceeds_expectFail(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r)
        public
    {
        _fresh();
        _trPass(n0, n1, c0, c1, r);
        vm.assume(uint256(c0) != 0 && uint256(c1) != 0 && c0 != c1 && _leafIdx(c0) == 0 && _leafIdx(c1) == 0);
        (bool ok,) = _tr("", n0, n1, c0, c1, r, "");
        assert(!ok);
    }

    /// X1-S instrument sanity (LIBMODE=0, benign mocks): with the status at NOT_ENTERED, a STATICCALL into
    /// withdraw reaches the guard's own SSTORE (ENTERED) and halts with empty return data. So a write
    /// before the revert is visible to the X1-S checks as `ret.length == 0`.
    function check_SANITY_staticWriteHaltsEmpty(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r)
        public
    {
        _fresh();
        (bool ok, bytes memory ret) = address(pool).staticcall(_wdData(proof, n, address(token), a, rcp, r));
        assert(!ok);
        assert(ret.length == 0);
    }

    /// X1-S with benign mocks and every withdraw guard passing (LIBMODE=0). Lock held: exact guard data.
    /// On the NR_W mutant the first write reached is the nullifier SSTORE (ShieldedPool.sol:283).
    function check_X1s_lockedWithdrawBenign(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _fresh();
        _lock();
        _wdPass(n, a, rcp, r);
        (bool ok, bytes memory ret) = address(pool).staticcall(_wdData(proof, n, address(token), a, rcp, r));
        _guardOnly(ok, ret);
    }

    /// Probe (must FAIL): the lock slot this harness writes is the slot the guard reads. With status 1
    /// and benign mocks, a withdraw can succeed; with status 2 (X1core_lockedWithdraw) it cannot.
    function check_PROBE_lockSlotIsConcreteOne_expectFail() public {
        _fresh();
        assert(uint256(vm.load(address(pool), LOCK)) != 1);
    }
}

// ---- mutant controls: each must FAIL the named checks ----

contract DuplicateLockMut_DUPTest is DuplicateLockTest {
    function _libArtifact() internal pure override returns (string memory) {
        return "LeanIMT_M_DUP.sol:LeanIMT_M_DUP";
    }
}

contract DuplicateLockMut_SKIPTest is DuplicateLockTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SKIP(v, r));
    }
}

contract DuplicateLockMut_ARGTest is DuplicateLockTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_ARG(v, r));
    }
}

contract DuplicateLockMut_NR_DTest is DuplicateLockTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_D(v, r));
    }
}

contract DuplicateLockMut_NR_TTest is DuplicateLockTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_T(v, r));
    }
}

contract DuplicateLockMut_NR_WTest is DuplicateLockTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_W(v, r));
    }
}
