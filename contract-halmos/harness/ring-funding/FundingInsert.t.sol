// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The insert-callback checks, plus the deposit funding call (D6) and a symbolic root index, on ShieldedPool (ethsystems/pocs a04b8b3) and the LeanIMT
// library it links (zk-kit a171c845), by Halmos. Built on the guards suite pattern: a fresh pool
// deployed inside each check, then symbolic storage; the real LeanIMT and PoseidonT3 code etched at the
// linked addresses. Mutant controls at the end.

import {Test} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {ReentrancyGuard} from "@openzeppelin-contracts/utils/ReentrancyGuard.sol";
import {ShieldedPool_M_D6_CALLER} from "./mutants/ShieldedPool_M_D6_CALLER.sol";
import {ShieldedPool_M_D6} from "./mutants/ShieldedPool_M_D6.sol";
import {ShieldedPool_M_NR_D} from "./mutants/ShieldedPool_M_NR_D.sol";
import {ShieldedPool_M_NR_T} from "./mutants/ShieldedPool_M_NR_T.sol";
import {ShieldedPool_M_NR_W} from "./mutants/ShieldedPool_M_NR_W.sol";
import {ShieldedPool_M_ORD_D} from "./mutants/ShieldedPool_M_ORD_D.sol";
import {ShieldedPool_M_ORD_W} from "./mutants/ShieldedPool_M_ORD_W.sol";
import {ShieldedPool_M_INS_D} from "./mutants/ShieldedPool_M_INS_D.sol";
import {ShieldedPool_M_SWAP_T} from "./mutants/ShieldedPool_M_SWAP_T.sol";

interface SVM {
    function createBytes32(string calldata name) external returns (bytes32);
    function createAddress(string calldata name) external returns (address);
    function createUint256(string calldata name) external returns (uint256);
    function enableSymbolicStorage(address) external;
    function snapshotState() external returns (bytes32);
}

interface VmLoad {
    function load(address target, bytes32 slot) external view returns (bytes32);
}

/// Verifier mock. ACCEPT (mode 0): every verify* returns true. BIND (mode 1): verifyDeposit returns
/// true only if publicInputs[0] == w0; verifyTransfer only if publicInputs[2] == w0 and [3] == w1.
contract BindVerifier is IVerifier {
    uint256 public mode;
    bytes32 public w0;
    bytes32 public w1;

    function set(uint256 m, bytes32 a, bytes32 b) external {
        mode = m;
        w0 = a;
        w1 = b;
    }

    function verifyDeposit(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        return mode == 0 || pi[0] == w0;
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        return mode == 0 || (pi[2] == w0 && pi[3] == w1);
    }

    function verifyWithdraw(bytes calldata, bytes32[] calldata) external pure returns (bool) {
        return true;
    }
}

contract SymRegistry {
    bytes32 public root;

    function set(bytes32 r) external {
        root = r;
    }

    function attestationRoot() external view returns (bytes32) {
        return root;
    }

    function attestationLeaves(bytes32) external pure returns (bool) {
        return false;
    }
}

/// Token mock with a hook. transferFrom and transfer move nothing and return true. On the FIRST token
/// call only, the hook records pool storage as seen at that moment (X2) and, if configured, calls back
/// into one pool entry point with fresh symbolic arguments (X1), recording whether that inner call
/// succeeded and its revert selector. Later token calls (from a successful inner call) only count.
contract HookToken {
    VmLoad internal constant VM = VmLoad(address(uint160(uint256(keccak256("hevm cheat code")))));

    address public pool;
    bytes32 public watchLeaf;
    bytes32 public watchNullifier;
    uint256 public reenterKind; // 0 none, 1 deposit, 2 transfer, 3 withdraw
    bytes32 public i0;
    bytes32 public i1;
    bytes32 public i2;
    bytes32 public i3;
    bytes32 public i4;
    uint256 public iamt;
    address public iaddr;

    uint256 public calls;
    address public fromArg;
    address public toArg;
    uint256 public amountArg;
    uint256 public watchIndex;

    function setIndex(uint256 idx) external { watchIndex = idx; }
    bool public innerTried;
    bool public innerOk;
    bytes4 public innerSel;
    uint256 public atSize;
    uint256 public atLeafIndex;
    bytes32 public atRoot;
    bool public atRootValid;
    bytes32 public atHist0;
    bool public atSpent;

    function setPool(address p) external {
        pool = p;
    }

    function watch(bytes32 leaf, bytes32 nullifier) external {
        watchLeaf = leaf;
        watchNullifier = nullifier;
    }

    function setReenter(uint256 kind, bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 e, uint256 amt, address who)
        external
    {
        reenterKind = kind;
        i0 = a;
        i1 = b;
        i2 = c;
        i3 = d;
        i4 = e;
        iamt = amt;
        iaddr = who;
    }

    function _hook() internal {
        calls += 1;
        if (calls != 1) return;
        ShieldedPool p = ShieldedPool(pool);
        atSize = p.getCommitmentCount();
        atLeafIndex = uint256(VM.load(pool, keccak256(abi.encode(uint256(watchLeaf), uint256(3)))));
        atRoot = p.commitmentRoot();
        atRootValid = p.validRoots(atRoot);
        atHist0 = p.historicalRoots(watchIndex);
        atSpent = p.nullifiers(watchNullifier);
        if (reenterKind == 0) return;
        bytes memory data;
        if (reenterKind == 1) {
            data = abi.encodeCall(ShieldedPool.deposit, ("", i0, address(this), iamt, address(this), ""));
        } else if (reenterKind == 2) {
            data = abi.encodeCall(ShieldedPool.transfer, ("", [i0, i1], [i2, i3], i4, ""));
        } else {
            data = abi.encodeCall(ShieldedPool.withdraw, ("", i0, address(this), iamt, iaddr, i4));
        }
        (bool ok, bytes memory ret) = pool.call(data);
        innerTried = true;
        innerOk = ok;
        innerSel = bytes4(ret);
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        fromArg = from;
        toArg = to;
        amountArg = amount;
        _hook();
        return true;
    }

    function transfer(address, uint256) external returns (bool) {
        _hook();
        return true;
    }
}

/// ASSUMPTION (as in the root-window suite), used only in runs with POSEIDON_STUB=1: PoseidonT3.hash is
/// replaced by keccak256 of its inputs reduced into the field (same selector). The real Poseidon on
/// symbolic inputs exhausts the 3G cap within 7 s. Results under the stub say nothing about hash
/// values, only about control flow, the leaf-index map, the size, the spent map and call order.
contract PoseidonT3Stub {
    uint256 constant F = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    function hash(uint256[2] memory x) public pure returns (uint256) {
        return uint256(keccak256(abi.encode(x[0], x[1]))) % F;
    }
}

contract FundingInsertTest is Test {
    SVM internal constant svm = SVM(address(uint160(uint256(keccak256("svm cheat code")))));
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant MAX_AMOUNT = 1 << 128;
    bytes4 internal constant LEAF_EXISTS = bytes4(keccak256("LeafAlreadyExists()"));
    bytes4 internal constant LEAF_ZERO = bytes4(keccak256("LeafCannotBeZero()"));
    uint256 internal constant DEP = 1;
    uint256 internal constant TR = 2;
    uint256 internal constant WD = 3;

    ShieldedPool internal pool;
    BindVerifier internal verifier;
    SymRegistry internal registry;
    HookToken internal token;

    function _etchLib(string memory artifact, address at) internal {
        bytes memory init = vm.getCode(artifact);
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(at, tmp.code);
    }

    /// The mutant DUP test contract overrides this with the library copy that lacks the duplicate check.
    function _libArtifact() internal pure virtual returns (string memory) {
        return "LeanIMT.sol:LeanIMT";
    }

    function setUp() public {
        _etchLib(_libArtifact(), address(0xA1001));
        if (vm.envUint("POSEIDON_STUB") == 1) {
            vm.etch(address(0xA1002), address(new PoseidonT3Stub()).code);
        } else {
            _etchLib("PoseidonT3.sol:PoseidonT3", address(0xA1002));
        }
        verifier = new BindVerifier();
        registry = new SymRegistry();
        token = new HookToken();
    }

    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    /// Fresh pool, symbolic storage, historicalRootIndex (slot 104) symbolic below 100
    /// or selected by ROOT_INDEX. With BAND_HI != 0 the tree depth (slot 1) is a fresh symbolic value in
    /// [BAND_LO, BAND_HI) and the LeanIMT shape size <= 2^depth is assumed. With BAND_HI == 0 the
    /// tree slots are left as they are: symbolic, any size and any depth.
    function _fresh() internal {
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
        svm.enableSymbolicStorage(address(pool));
        uint256 idx;
        if (vm.envUint("SYMBOLIC_INDEX") == 1) {
            idx = svm.createUint256("historicalRootIndex");
            vm.assume(idx < 100);
        } else {
            idx = vm.envUint("ROOT_INDEX");
            require(idx < 100);
        }
        vm.store(address(pool), bytes32(uint256(104)), bytes32(idx));
        token.setIndex(idx);
        bytes32 ar = svm.createBytes32("attRoot");
        vm.assume(uint256(ar) < P);
        registry.set(ar);
        token.setPool(address(pool));
        verifier.set(0, 0, 0);
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

    /// Every deposit guard of ShieldedPool.sol:145-149 and 163 passes (token = the hook token).
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

    /// Every withdraw guard of ShieldedPool.sol:254-263 and 275 passes (token = the hook token).
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

    // ---- D5 / T11 (a): a leaf already in the tree is rejected (InternalLeanIMT.sol:41-46) ----

    /// Deposit of a commitment already in the tree, every other guard passing, accept-all verifier:
    /// reverts with LeafAlreadyExists (LeafCannotBeZero for c = 0), no state change, no token call.
    function check_D5a_depositLeafInTree_reverts(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note)
        public
    {
        _fresh();
        _depPass(c, a, f);
        vm.assume(_leafIdx(c) != 0);
        bytes32 g0 = svm.snapshotState();
        (bool ok, bytes memory ret) = _dep(proof, c, a, f, note);
        assert(!ok);
        assert(bytes4(ret) == (c == 0 ? LEAF_ZERO : LEAF_EXISTS));
        assert(svm.snapshotState() == g0);
        assert(token.calls() == 0);
    }

    /// Transfer whose first output is already in the tree: reverts as above, no state change.
    function check_T11a0_transferOut0InTree_reverts(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        _trPass(n0, n1, c0, c1, r);
        vm.assume(_leafIdx(c0) != 0);
        bytes32 g0 = svm.snapshotState();
        (bool ok, bytes memory ret) = _tr(proof, n0, n1, c0, c1, r, note);
        assert(!ok);
        assert(bytes4(ret) == (c0 == 0 ? LEAF_ZERO : LEAF_EXISTS));
        assert(svm.snapshotState() == g0);
    }

    /// Transfer whose second output is already in the tree (the first is new): reverts with
    /// LeafAlreadyExists after the first insert, no state change. Depth band (the first insert loops).
    function check_T11a1_transferOut1InTree_reverts(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        _trPass(n0, n1, c0, c1, r);
        vm.assume(c0 != 0 && _leafIdx(c0) == 0 && c1 != c0);
        vm.assume(_leafIdx(c1) != 0);
        bytes32 g0 = svm.snapshotState();
        (bool ok, bytes memory ret) = _tr(proof, n0, n1, c0, c1, r, note);
        assert(!ok);
        assert(bytes4(ret) == (c1 == 0 ? LEAF_ZERO : LEAF_EXISTS));
        assert(svm.snapshotState() == g0);
    }

    /// T11 (c): a transfer whose two output commitments are equal (and new) reverts with
    /// LeafAlreadyExists at the second insert, no state change. Depth band.
    function check_T11c_equalOutputs_reverts(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        _trPass(n0, n1, c, c, r);
        vm.assume(c != 0 && _leafIdx(c) == 0);
        bytes32 g0 = svm.snapshotState();
        (bool ok, bytes memory ret) = _tr(proof, n0, n1, c, c, r, note);
        assert(!ok);
        assert(bytes4(ret) == LEAF_EXISTS);
        assert(svm.snapshotState() == g0);
    }

    /// D5 by sequence: a deposit of c succeeds, then a second deposit of the same c (other arguments
    /// fresh and symbolic, every guard passing) reverts with LeafAlreadyExists. Depth band.
    function check_D5s_depositTwice_reverts(bytes32 c, uint256 a, address f) public {
        _fresh();
        _depPass(c, a, f);
        (bool ok1,) = _dep("", c, a, f, "");
        vm.assume(ok1);
        uint256 a2 = svm.createUint256("a2");
        address f2 = svm.createAddress("f2");
        _depPass(c, a2, f2);
        bytes32 g0 = svm.snapshotState();
        (bool ok, bytes memory ret) = _dep("", c, a2, f2, "");
        assert(!ok);
        assert(bytes4(ret) == LEAF_EXISTS);
        assert(svm.snapshotState() == g0);
    }

    // ---- D5 / T11 (b): the public commitments are the inserted leaves, in order ----

    /// A successful deposit (verifier accepts only if public input 0 == c) inserts exactly c, as the
    /// next leaf: leaves[c] = old size + 1 and size = old size + 1. Depth band.
    function check_D5b_depositInsertsCommitment(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note)
        public
    {
        _fresh();
        _depPass(c, a, f);
        vm.assume(_leafIdx(c) == 0);
        verifier.set(1, c, 0);
        uint256 s0 = pool.getCommitmentCount();
        (bool ok,) = _dep(proof, c, a, f, note);
        vm.assume(ok);
        assert(_leafIdx(c) == s0 + 1);
        assert(pool.getCommitmentCount() == s0 + 1);
    }

    /// A successful transfer (verifier accepts only if public inputs 2, 3 == c0, c1) inserts c0 as
    /// leaf s0 + 1 and then c1 as leaf s0 + 2; size grows by 2. Depth band.
    function check_T11b_transferInsertsOutputsInOrder(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        _trPass(n0, n1, c0, c1, r);
        vm.assume(_leafIdx(c0) == 0 && _leafIdx(c1) == 0);
        verifier.set(1, c0, c1);
        uint256 s0 = pool.getCommitmentCount();
        (bool ok,) = _tr(proof, n0, n1, c0, c1, r, note);
        vm.assume(ok);
        assert(_leafIdx(c0) == s0 + 1);
        assert(_leafIdx(c1) == s0 + 2);
        assert(pool.getCommitmentCount() == s0 + 2);
    }

    // ---- X1: re-entry from the token call is rejected ----

    function _setInner(uint256 inner) internal {
        token.setReenter(
            inner,
            svm.createBytes32("i0"),
            svm.createBytes32("i1"),
            svm.createBytes32("i2"),
            svm.createBytes32("i3"),
            svm.createBytes32("i4"),
            svm.createUint256("iamt"),
            svm.createAddress("iaddr")
        );
    }

    /// Outer deposit (every guard passing, leaf new), the token hook re-enters `inner` with fresh
    /// symbolic arguments: whenever the hook ran, the inner call reverted with ReentrancyGuardReentrantCall.
    function _x1Deposit(uint256 inner, bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) internal {
        _fresh();
        _depPass(c, a, f);
        _setInner(inner);
        _dep(proof, c, a, f, note);
        vm.assume(token.innerTried());
        assert(!token.innerOk());
        assert(token.innerSel() == ReentrancyGuard.ReentrancyGuardReentrantCall.selector);
    }

    function _x1Withdraw(uint256 inner, bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) internal {
        _fresh();
        _wdPass(n, a, rcp, r);
        _setInner(inner);
        _wd(proof, n, a, rcp, r);
        vm.assume(token.innerTried());
        assert(!token.innerOk());
        assert(token.innerSel() == ReentrancyGuard.ReentrancyGuardReentrantCall.selector);
    }

    function check_X1_depositReentersDeposit(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _x1Deposit(DEP, proof, c, a, f, note);
    }

    function check_X1_depositReentersTransfer(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _x1Deposit(TR, proof, c, a, f, note);
    }

    function check_X1_depositReentersWithdraw(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _x1Deposit(WD, proof, c, a, f, note);
    }

    function check_X1_withdrawReentersDeposit(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _x1Withdraw(DEP, proof, n, a, rcp, r);
    }

    function check_X1_withdrawReentersTransfer(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _x1Withdraw(TR, proof, n, a, rcp, r);
    }

    function check_X1_withdrawReentersWithdraw(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _x1Withdraw(WD, proof, n, a, rcp, r);
    }

    /// Transfer moves no tokens: a successful transfer makes no call to the token. Depth band.
    function check_X1_transferNoTokenCall(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        _trPass(n0, n1, c0, c1, r);
        (bool ok,) = _tr(proof, n0, n1, c0, c1, r, note);
        vm.assume(ok);
        assert(token.calls() == 0);
    }

    /// Witness for the check above: a transfer can succeed in the band (must FAIL).
    function check_WIT_transferSucceeds_expectFail(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r) public {
        _fresh();
        _trPass(n0, n1, c0, c1, r);
        (bool ok,) = _tr("", n0, n1, c0, c1, r, "");
        assert(!ok);
    }

    // ---- X2: state updates finish before the token is called ----

    /// At the moment deposit calls transferFrom, the tree already holds c as leaf s0 + 1, the size is
    /// s0 + 1, and the new root is recorded (validRoots and the watched historicalRoots index).
    function check_X2_depositTreeUpdatedBeforeTokenCall(
        bytes memory proof,
        bytes32 c,
        uint256 a,
        address f,
        bytes memory note
    ) public {
        _fresh();
        _depPass(c, a, f);
        token.watch(c, 0);
        uint256 s0 = pool.getCommitmentCount();
        _dep(proof, c, a, f, note);
        vm.assume(token.calls() >= 1);
        assert(token.atLeafIndex() == s0 + 1);
        assert(token.atSize() == s0 + 1);
        assert(token.atRootValid());
        assert(token.atHist0() == token.atRoot());
        assert(token.atRoot() == pool.commitmentRoot());
    }

    /// At the moment withdraw calls transfer, the nullifier is already marked spent.
    function check_X2_withdrawSpentBeforeTokenCall(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r)
        public
    {
        _fresh();
        _wdPass(n, a, rcp, r);
        token.watch(0, n);
        _wd(proof, n, a, rcp, r);
        vm.assume(token.calls() >= 1);
        assert(token.atSpent());
    }

    function check_D6_successBinding(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _fresh();
        _depPass(c, a, f);
        address caller = svm.createAddress("depositCaller");
        vm.prank(caller);
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.deposit, (proof, c, address(token), a, f, note)));
        vm.assume(ok);
        assert(f == caller);
        assert(token.fromArg() == f);
        assert(token.toArg() == address(pool));
        assert(token.amountArg() == a);
        assert(token.calls() == 1);
    }

    function check_D6_successWitness_expectFail(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _fresh();
        _depPass(c, a, f);
        (bool ok,) = _dep(proof, c, a, f, note);
        assert(!ok);
    }

    // ---- probes ----

    /// The leaf-index slot read by vm.load is symbolic and the one the library reads: a deposit of a
    /// leaf with index 0 can succeed (must FAIL). Depth band.
    function check_PROBE_depositNewLeafSucceeds_expectFail(bytes32 c, uint256 a, address f) public {
        _fresh();
        _depPass(c, a, f);
        vm.assume(_leafIdx(c) == 0);
        (bool ok,) = _dep("", c, a, f, "");
        assert(!ok);
    }

    /// The leaf-index slot can be nonzero (must FAIL).
    function check_PROBE_leafIndexSymbolic_expectFail(bytes32 c) public {
        _fresh();
        assert(_leafIdx(c) == 0);
    }
}

// ---- mutant controls: each must FAIL the named checks ----

contract FundingInsertMut_DUPTest is FundingInsertTest {
    function _libArtifact() internal pure override returns (string memory) {
        return "LeanIMT_M_DUP.sol:LeanIMT_M_DUP";
    }
}

contract FundingInsertMut_NR_DTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_D(v, r));
    }
}

contract FundingInsertMut_NR_TTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_T(v, r));
    }
}

contract FundingInsertMut_NR_WTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_W(v, r));
    }
}

contract FundingInsertMut_ORD_DTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_ORD_D(v, r));
    }
}

contract FundingInsertMut_ORD_WTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_ORD_W(v, r));
    }
}

contract FundingInsertMut_INS_DTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_INS_D(v, r));
    }
}

contract FundingInsertMut_SWAP_TTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SWAP_T(v, r));
    }
}

contract FundingInsertMut_D6Test is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_D6(v, r));
    }
}

contract FundingInsertMut_D6_CALLERTest is FundingInsertTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_D6_CALLER(v, r));
    }
}
