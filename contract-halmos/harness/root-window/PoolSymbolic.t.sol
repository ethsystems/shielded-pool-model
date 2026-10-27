// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {MockVerifier} from "../../src/mocks/MockCompositeVerifier.sol";
import {MockERC20} from "../../src/mocks/MockERC20.sol";
import {LeanIMT, LeanIMTData} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";

/// Independent LeanIMT fed the same leaves one at a time: its roots are every prefix root.
contract ShadowTree {
    using LeanIMT for LeanIMTData;
    LeanIMTData t;

    function ins(uint256 leaf) external returns (bytes32) {
        t.insert(leaf);
        return bytes32(t.root());
    }
}

interface SVM {
    function createCalldata(string calldata contractName) external returns (bytes memory);
    function createAddress(string calldata name) external returns (address);
    function createBytes32(string calldata name) external returns (bytes32);
    function enableSymbolicStorage(address) external;
}

/// Registry stub: fixed attestation root, so no PoseidonT5 on the deposit path.
contract StubRegistry {
    function attestationRoot() external pure returns (bytes32) {
        return bytes32(uint256(7));
    }
}

/// Token whose transfer hook observes the pool mid-withdraw (property 3).
/// It records the nullifier flag the pool exposes during the payout, then
/// tries to re-enter withdraw with the same nullifier.
contract HookToken is MockERC20 {
    ShieldedPool public pool;
    bytes32 public watch;
    bool public armed;
    bool public fired;
    bool public sawSpent;
    bool public reentryOk;

    constructor() MockERC20("Hook", "HOOK", 18) {}

    function arm(ShieldedPool _pool, bytes32 _watch) external {
        pool = _pool;
        watch = _watch;
        armed = true;
    }

    function _update(address from, address to, uint256 value) internal override {
        super._update(from, to, value);
        if (armed && !fired && from == address(pool)) {
            fired = true;
            sawSpent = pool.nullifiers(watch);
            (reentryOk,) = address(pool).call(
                abi.encodeCall(ShieldedPool.withdraw, ("", watch, address(this), 1, address(this), pool.commitmentRoot()))
            );
        }
    }
}

contract PoolSymbolicTest is Test {
    SVM constant svm = SVM(address(uint160(uint256(keccak256("svm cheat code")))));

    ShieldedPool pool;
    MockERC20 token;
    HookToken hook;
    ShadowTree shadow;
    address verifierAddr;
    address registryAddr;
    address user = address(0x1111);

    bytes32 constant NUL0 = bytes32(uint256(0xa0));
    bytes32 constant NUL1 = bytes32(uint256(0xa1));
    bytes32 constant NUL2 = bytes32(uint256(0xa2));

    /// Ghost list of every root the contract has exposed as its current root.
    bytes32[] produced;

    function _etchLib(string memory artifact, address at) internal {
        bytes memory init = vm.getCode(artifact);
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(at, tmp.code);
    }

    function _etchPoseidon() internal virtual {
        _etchLib("PoseidonT3.sol:PoseidonT3", address(0xA1002));
    }

    function setUp() public {
        _etchPoseidon();
        _etchLib("LeanIMT.sol:LeanIMT", address(0xA1001));
        MockVerifier verifier = new MockVerifier(); // always true: verifier soundness stays assumed
        StubRegistry registry = new StubRegistry();
        pool = new ShieldedPool(address(verifier), address(registry));
        verifierAddr = address(verifier);
        registryAddr = address(registry);
        token = new MockERC20("T", "T", 18);
        hook = new HookToken();
        pool.addSupportedToken(address(token));
        pool.addSupportedToken(address(hook));
        token.mint(user, 1e30);
        token.mint(address(pool), 1e30);
        hook.mint(address(pool), 1e30);
        vm.prank(user);
        token.approve(address(pool), type(uint256).max);

        // Reached state: four insertions, three spent nullifiers.
        // `produced` holds the root of every prefix of the leaf sequence, including the empty tree.
        shadow = new ShadowTree();
        produced.push(bytes32(0));
        vm.prank(user);
        pool.deposit("", bytes32(uint256(1)), address(token), 5, user, "");
        produced.push(shadow.ins(1));
        vm.prank(user);
        pool.deposit("", bytes32(uint256(2)), address(token), 5, user, "");
        produced.push(shadow.ins(2));
        pool.withdraw("", NUL0, address(token), 1, user, pool.commitmentRoot());
        pool.transfer("", [NUL1, NUL2], [bytes32(uint256(3)), bytes32(uint256(4))], pool.commitmentRoot(), "");
        produced.push(shadow.ins(3));
        produced.push(shadow.ins(4));
        assert(produced[4] == pool.commitmentRoot());
    }

    function _anyCall() internal returns (bool ok) {
        bytes memory data = svm.createCalldata("ShieldedPool");
        address caller = svm.createAddress("caller");
        vm.prank(caller);
        (ok,) = address(pool).call(data);
    }

    // ---- Property 1: nullifier set only grows ----

    /// Any single call to any public entry point, from any caller, from the reached state.
    function check_P1_nullifierMonotone_anyCall(bytes32 k) public {
        vm.assume(pool.nullifiers(k));
        _anyCall();
        assert(pool.nullifiers(k));
    }

    /// Reached state, transfer only, symbolic arguments (narrower than anyCall).
    function check_P1_nullifierMonotone_reached_transfer(bytes32 k, bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root)
        public
    {
        vm.assume(pool.nullifiers(k));
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    /// Reached state, deposit only, symbolic arguments.
    function check_P1_nullifierMonotone_reached_deposit(bytes32 k, bytes32 c, uint256 amount) public {
        vm.assume(pool.nullifiers(k));
        vm.prank(user);
        try pool.deposit("", c, address(token), amount, user, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    /// Two consecutive arbitrary calls.
    function check_P1_nullifierMonotone_twoCalls(bytes32 k) public {
        vm.assume(pool.nullifiers(k));
        _anyCall();
        _anyCall();
        assert(pool.nullifiers(k));
    }

    /// Arbitrary pool storage (symbolic), withdraw with symbolic arguments.
    function check_P1_nullifierMonotone_symStorage_withdraw(
        bytes32 k,
        bytes32 n,
        uint256 amount,
        address recipient,
        bytes32 root
    ) public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        vm.assume(pool.nullifiers(k));
        try pool.withdraw("", n, address(token), amount, recipient, root) {} catch {}
        assert(pool.nullifiers(k));
    }

    /// Arbitrary pool storage (symbolic), transfer with symbolic arguments.
    function check_P1_nullifierMonotone_symStorage_transfer(
        bytes32 k,
        bytes32 a,
        bytes32 b,
        bytes32 c,
        bytes32 d,
        bytes32 root
    ) public {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        vm.assume(pool.nullifiers(k));
        try pool.transfer("", [a, b], [c, d], root, "") {} catch {}
        assert(pool.nullifiers(k));
    }

    /// Keep the external contracts concrete so calls resolve; everything else stays symbolic.
    function _pinExternals() internal {
        vm.store(address(pool), bytes32(uint256(108)), bytes32(uint256(uint160(verifierAddr))));
        vm.store(address(pool), bytes32(uint256(109)), bytes32(uint256(uint160(registryAddr))));
    }

    // ---- Property 2: a spent nullifier cannot be spent again ----

    function check_P2_withdrawSpentReverts(bytes32 n, uint256 amount, address recipient, bytes32 root) public {
        vm.assume(pool.nullifiers(n));
        (bool ok,) = address(pool).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(token), amount, recipient, root))
        );
        assert(!ok);
    }

    function check_P2_transferSpentReverts(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root) public {
        vm.assume(pool.nullifiers(a) || pool.nullifiers(b));
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    /// Arbitrary pool storage: same claims without relying on the reached state.
    function check_P2_withdrawSpentReverts_symStorage(bytes32 n, uint256 amount, address recipient, bytes32 root)
        public
    {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        vm.assume(pool.nullifiers(n));
        (bool ok,) = address(pool).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(token), amount, recipient, root))
        );
        assert(!ok);
    }

    function check_P2_transferSpentReverts_symStorage(bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 root)
        public
    {
        svm.enableSymbolicStorage(address(pool));
        _pinExternals();
        vm.assume(pool.nullifiers(a) || pool.nullifiers(b));
        (bool ok,) = address(pool).call(abi.encodeCall(ShieldedPool.transfer, ("", [a, b], [c, d], root, "")));
        assert(!ok);
    }

    /// Fresh nullifier: the first withdraw may succeed, the second with the same nullifier must not.
    function check_P2_withdrawTwiceSecondReverts(bytes32 n, uint256 amount, address recipient) public {
        bytes32 root = pool.commitmentRoot();
        (bool ok1,) = address(pool).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(token), amount, recipient, root))
        );
        vm.assume(ok1);
        (bool ok2,) = address(pool).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(token), amount, recipient, root))
        );
        assert(!ok2);
    }

    // ---- Property 3: nullifier is marked spent before the token transfer ----

    function check_P3_spentBeforePay(bytes32 n, uint256 amount, address recipient) public {
        vm.assume(!pool.nullifiers(n));
        hook.arm(pool, n);
        (bool ok,) = address(pool).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(hook), amount, recipient, pool.commitmentRoot()))
        );
        if (ok) {
            assert(hook.fired());
            assert(hook.sawSpent());
            assert(!hook.reentryOk());
        }
    }

    // ---- Property 4: isKnownRoot accepts only roots the contract produced ----

    function _isProduced(bytes32 r) internal view returns (bool) {
        for (uint256 i = 0; i < produced.length; i++) {
            if (produced[i] == r) return true;
        }
        return false;
    }

    function check_P4_knownRootsOnly_reached(bytes32 r) public view {
        if (pool.isKnownRoot(r)) assert(_isProduced(r));
    }

    /// The first P4 version: only post-transaction roots are known. On the contract before its fix (one
    /// root per operation) it failed: the root between the two insertions of a transfer was a valid root
    /// no transaction ever ended on. At ethsystems/pocs a04b8b3 it must PASS.
    function check_P4v1_postTxRootsOnly(bytes32 r) public view {
        bool postTx = r == produced[0] || r == produced[1] || r == produced[2] || r == produced[4];
        if (pool.isKnownRoot(r)) assert(postTx);
    }

    // ---- Reachability witnesses: each MUST fail, proving the guarded success path is not vacuous ----

    function check_W_P3_withdrawSuccessReachable_expectFail(bytes32 n, uint256 amount, address recipient) public {
        vm.assume(!pool.nullifiers(n));
        hook.arm(pool, n);
        (bool ok,) = address(pool).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(hook), amount, recipient, pool.commitmentRoot()))
        );
        assert(!ok);
    }

    function check_W_P2_firstWithdrawReachable_expectFail(bytes32 n, uint256 amount, address recipient) public {
        (bool ok1,) = address(pool).call(
            abi.encodeCall(ShieldedPool.withdraw, ("", n, address(token), amount, recipient, pool.commitmentRoot()))
        );
        assert(!ok1);
    }

    /// Side check: the empty-tree root 0 is known only while the tree is empty.
    function check_P4_zeroRootNotKnownAfterInsert() public view {
        assert(pool.getCommitmentCount() > 0);
        assert(!pool.isKnownRoot(bytes32(0)));
    }

    // ---- Property 5 (stretch): tree size never decreases ----

    function check_P5_treeSizeMonotone_anyCall() public {
        uint256 before = pool.getCommitmentCount();
        _anyCall();
        assert(pool.getCommitmentCount() >= before);
    }
}
