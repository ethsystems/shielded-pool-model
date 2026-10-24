// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The pre-verifier rejection guards of ShieldedPool (ethsystems/pocs a04b8b3) under Kontrol 1.0.255
// with the stock KEVM, where a `bytes` test argument has one symbolic length in 0..2^30 (KEVM abi.md,
// the `ensures` of the #bytes encoding rule) and symbolic content.
// Property per guard: with every earlier guard of the same function passing and this guard's
// condition failing, the pool call reverts and its revert selector is this guard's error. The
// verifier reverts with a different marker on every call, so it was not reached. No storage check
// after the call: unchanged storage follows from the revert (KEVM call semantics).
// Mutant siblings (one guard removed each) run the same prove_ body and must FAIL.

import {Test} from "forge-std/src/Test.sol";
import {KontrolCheats} from "kontrol-cheatcodes/KontrolCheats.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {LeanIMT} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";
import {ShieldedPool_M_DEPOSIT_TOKEN} from "./mutants/ShieldedPool_M_DEPOSIT_TOKEN.sol";
import {ShieldedPool_M_DEPOSIT_ZERO_AMOUNT} from "./mutants/ShieldedPool_M_DEPOSIT_ZERO_AMOUNT.sol";
import {ShieldedPool_M_DEPOSIT_AMOUNT_MAX} from "./mutants/ShieldedPool_M_DEPOSIT_AMOUNT_MAX.sol";
import {ShieldedPool_M_DEPOSIT_ZERO_FUNDER} from "./mutants/ShieldedPool_M_DEPOSIT_ZERO_FUNDER.sol";
import {ShieldedPool_M_DEPOSIT_FUNDER_CALLER} from "./mutants/ShieldedPool_M_DEPOSIT_FUNDER_CALLER.sol";
import {ShieldedPool_M_TRANSFER_SAME_NULLIFIERS} from "./mutants/ShieldedPool_M_TRANSFER_SAME_NULLIFIERS.sol";
import {ShieldedPool_M_TRANSFER_SPENT_FIRST} from "./mutants/ShieldedPool_M_TRANSFER_SPENT_FIRST.sol";
import {ShieldedPool_M_TRANSFER_SPENT_SECOND} from "./mutants/ShieldedPool_M_TRANSFER_SPENT_SECOND.sol";
import {ShieldedPool_M_TRANSFER_ROOT} from "./mutants/ShieldedPool_M_TRANSFER_ROOT.sol";
import {ShieldedPool_M_WITHDRAW_ZERO_AMOUNT} from "./mutants/ShieldedPool_M_WITHDRAW_ZERO_AMOUNT.sol";
import {ShieldedPool_M_WITHDRAW_AMOUNT_MAX} from "./mutants/ShieldedPool_M_WITHDRAW_AMOUNT_MAX.sol";
import {ShieldedPool_M_WITHDRAW_SPENT} from "./mutants/ShieldedPool_M_WITHDRAW_SPENT.sol";
import {ShieldedPool_M_WITHDRAW_ROOT} from "./mutants/ShieldedPool_M_WITHDRAW_ROOT.sol";

/// Always-trip verifier: every verify* call reverts with VerifierReached(selector). The pool's
/// high-level call re-throws it unchanged, so "revert data is not the marker" means "not reached".
contract TripVerifier is IVerifier {
    error VerifierReached(bytes4 which);

    function verifyDeposit(bytes calldata, bytes32[] calldata) external pure returns (bool) {
        revert VerifierReached(msg.sig);
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata) external pure returns (bool) {
        revert VerifierReached(msg.sig);
    }

    function verifyWithdraw(bytes calldata, bytes32[] calldata) external pure returns (bool) {
        revert VerifierReached(msg.sig);
    }
}

/// Registry whose root is slot 0, made symbolic in each proof (deposit public input 4 symbolic).
contract SymRegistry {
    bytes32 public root;

    function attestationRoot() external view returns (bytes32) {
        return root;
    }
}

contract RejectGuards is Test, KontrolCheats {
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant MAX_AMOUNT = 1 << 128;
    bytes32 internal constant REENTRANCY_SLOT = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;

    ShieldedPool internal pool;
    TripVerifier internal verifier;
    SymRegistry internal registry;

    function setUp() public {
        // Real LeanIMT code at the linked address (commitmentRoot() delegatecalls it). PoseidonT3 is
        // not reached on any path here (no insertion before the verifier).
        bytes memory init = type(LeanIMT).creationCode;
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(address(0xA1001), tmp.code);
        verifier = new TripVerifier();
        registry = new SymRegistry();
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
    }

    /// Mutant test contracts override this to deploy a copy with one guard removed.
    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    /// Arbitrary pool storage, then re-pin the two external addresses and the reentrancy status
    /// (NOT_ENTERED, as the constructor leaves it). Registry root symbolic.
    function _fresh() internal {
        kevm.symbolicStorage(address(pool));
        vm.store(address(pool), bytes32(uint256(108)), bytes32(uint256(uint160(address(verifier)))));
        vm.store(address(pool), bytes32(uint256(109)), bytes32(uint256(uint160(address(registry)))));
        vm.store(address(pool), REENTRANCY_SLOT, bytes32(uint256(1)));
        kevm.symbolicStorage(address(registry));
    }

    /// One call from `caller`. Asserts it reverts; returns the first 4 bytes of the revert data,
    /// copied to scratch offset 0 (a fixed offset, away from the symbolic-length encoding).
    /// The caller asserts the selector equals the guard's error, which differs from
    /// TripVerifier.VerifierReached, so the verifier was not reached.
    function _reject(address caller, bytes memory data) internal returns (bytes4 sel) {
        address p = address(pool);
        bool ok;
        vm.prank(caller);
        assembly {
            ok := call(gas(), p, 0, add(data, 0x20), mload(data), 0, 0)
            if gt(returndatasize(), 3) {
                returndatacopy(0, 0, 4)
                sel := and(mload(0), 0xffffffff00000000000000000000000000000000000000000000000000000000)
            }
        }
        assert(!ok);
    }

    function _known(bytes32 r) internal view returns (bool) {
        return r == pool.commitmentRoot() || pool.validRoots(r);
    }

    // Each check assumes every earlier guard passes (all assumptions are made before the call, while
    // memory is small). Across one function's chain this covers every input that fails some guard:
    // the first failing guard's check applies to it.

    // ---- deposit, ShieldedPool.sol:145-149 ----

    function _depPass(uint256 k, address t, uint256 a, address f, address caller) internal view {
        if (k > 1) vm.assume(pool.supportedTokens(t));
        if (k > 2) vm.assume(a != 0);
        if (k > 3) vm.assume(a < MAX_AMOUNT);
        if (k > 4) vm.assume(f != address(0));
        if (k > 5) vm.assume(caller == f);
    }

    function _dep(bytes calldata proof, bytes32 c, address t, uint256 a, address f, bytes calldata note)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(ShieldedPool.deposit.selector, proof, c, t, a, f, note);
    }

    function prove_deposit_token(bytes calldata proof, bytes32 c, address t, uint256 a, address f, bytes calldata note, address caller)
        public
    {
        _fresh();
        vm.assume(!pool.supportedTokens(t));
        assert(_reject(caller, _dep(proof, c, t, a, f, note)) == ShieldedPool.UnsupportedToken.selector);
    }

    function prove_deposit_zero_amount(bytes calldata proof, bytes32 c, address t, address f, bytes calldata note, address caller) public {
        _fresh();
        _depPass(2, t, 0, f, caller);
        assert(_reject(caller, _dep(proof, c, t, 0, f, note)) == ShieldedPool.ZeroAmount.selector);
    }

    function prove_deposit_amount_max(bytes calldata proof, bytes32 c, address t, uint256 a, address f, bytes calldata note, address caller)
        public
    {
        _fresh();
        _depPass(3, t, a, f, caller);
        vm.assume(a >= MAX_AMOUNT);
        assert(_reject(caller, _dep(proof, c, t, a, f, note)) == ShieldedPool.AmountTooLarge.selector);
    }

    function prove_deposit_zero_funder(bytes calldata proof, bytes32 c, address t, uint256 a, bytes calldata note, address caller) public {
        _fresh();
        _depPass(4, t, a, address(0), caller);
        assert(_reject(caller, _dep(proof, c, t, a, address(0), note)) == ShieldedPool.ZeroAddress.selector);
    }

    function prove_deposit_funder_caller(bytes calldata proof, bytes32 c, address t, uint256 a, address f, bytes calldata note, address caller)
        public
    {
        _fresh();
        _depPass(5, t, a, f, caller);
        vm.assume(caller != f);
        assert(_reject(caller, _dep(proof, c, t, a, f, note)) == ShieldedPool.FundingAddressMismatch.selector);
    }

    // ---- transfer, ShieldedPool.sol:195-204 ----

    function _trPass(uint256 k, bytes32 n0, bytes32 n1, bytes32 r) internal view {
        if (k > 1) vm.assume(n0 != n1);
        if (k > 2) vm.assume(!pool.nullifiers(n0));
        if (k > 3) vm.assume(!pool.nullifiers(n1));
        if (k > 4) vm.assume(_known(r));
    }

    function _tr(bytes calldata proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes calldata note)
        internal
        pure
        returns (bytes memory)
    {
        bytes32[2] memory ns = [n0, n1];
        bytes32[2] memory cs = [c0, c1];
        return abi.encodeWithSelector(ShieldedPool.transfer.selector, proof, ns, cs, r, note);
    }

    function prove_transfer_same_nullifiers(bytes calldata proof, bytes32 n, bytes32 c0, bytes32 c1, bytes32 r, bytes calldata note, address caller)
        public
    {
        _fresh();
        assert(_reject(caller, _tr(proof, n, n, c0, c1, r, note)) == ShieldedPool.IdenticalNullifiers.selector);
    }

    function prove_transfer_spent_first(
        bytes calldata proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes calldata note,
        address caller
    ) public {
        _fresh();
        _trPass(2, n0, n1, r);
        vm.assume(pool.nullifiers(n0));
        assert(_reject(caller, _tr(proof, n0, n1, c0, c1, r, note)) == ShieldedPool.NullifierAlreadySpent.selector);
    }

    function prove_transfer_spent_second(
        bytes calldata proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes calldata note,
        address caller
    ) public {
        _fresh();
        _trPass(3, n0, n1, r);
        vm.assume(pool.nullifiers(n1));
        assert(_reject(caller, _tr(proof, n0, n1, c0, c1, r, note)) == ShieldedPool.NullifierAlreadySpent.selector);
    }

    function prove_transfer_root(
        bytes calldata proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes calldata note,
        address caller
    ) public {
        _fresh();
        _trPass(4, n0, n1, r);
        vm.assume(!_known(r));
        assert(_reject(caller, _tr(proof, n0, n1, c0, c1, r, note)) == ShieldedPool.InvalidRoot.selector);
    }

    // ---- withdraw, ShieldedPool.sol:254-263 (withdraw has no payload) ----

    function _wdPass(uint256 k, bytes32 n, address t, uint256 a, address rcp, bytes32 r) internal view {
        if (k > 1) vm.assume(pool.supportedTokens(t));
        if (k > 2) vm.assume(a != 0);
        if (k > 3) vm.assume(a < MAX_AMOUNT);
        if (k > 4) vm.assume(rcp != address(0));
        if (k > 5) vm.assume(!pool.nullifiers(n));
        if (k > 6) vm.assume(_known(r));
    }

    function _wd(bytes calldata proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(ShieldedPool.withdraw.selector, proof, n, t, a, rcp, r);
    }

    function prove_withdraw_zero_amount(bytes calldata proof, bytes32 n, address t, address rcp, bytes32 r, address caller) public {
        _fresh();
        _wdPass(2, n, t, 0, rcp, r);
        assert(_reject(caller, _wd(proof, n, t, 0, rcp, r)) == ShieldedPool.ZeroAmount.selector);
    }

    function prove_withdraw_amount_max(bytes calldata proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller)
        public
    {
        _fresh();
        _wdPass(3, n, t, a, rcp, r);
        vm.assume(a >= MAX_AMOUNT);
        assert(_reject(caller, _wd(proof, n, t, a, rcp, r)) == ShieldedPool.AmountTooLarge.selector);
    }

    function prove_withdraw_spent(bytes calldata proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller)
        public
    {
        _fresh();
        _wdPass(5, n, t, a, rcp, r);
        vm.assume(pool.nullifiers(n));
        assert(_reject(caller, _wd(proof, n, t, a, rcp, r)) == ShieldedPool.NullifierAlreadySpent.selector);
    }

    function prove_withdraw_root(bytes calldata proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller)
        public
    {
        _fresh();
        _wdPass(6, n, t, a, rcp, r);
        vm.assume(!_known(r));
        assert(_reject(caller, _wd(proof, n, t, a, rcp, r)) == ShieldedPool.InvalidRoot.selector);
    }
}

// ---- mutant siblings: the same prove_ bodies against a pool with one guard removed ----
// Run only the matching prove_ in each (e.g. RejectGuards_M_DEPOSIT_TOKEN.prove_deposit_token); each must FAIL.

contract RejectGuards_M_DEPOSIT_TOKEN is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_TOKEN(v, r));
    }
}

contract RejectGuards_M_DEPOSIT_ZERO_AMOUNT is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_ZERO_AMOUNT(v, r));
    }
}

contract RejectGuards_M_DEPOSIT_AMOUNT_MAX is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_AMOUNT_MAX(v, r));
    }
}

contract RejectGuards_M_DEPOSIT_ZERO_FUNDER is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_ZERO_FUNDER(v, r));
    }
}

contract RejectGuards_M_DEPOSIT_FUNDER_CALLER is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_FUNDER_CALLER(v, r));
    }
}

contract RejectGuards_M_TRANSFER_SAME_NULLIFIERS is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_SAME_NULLIFIERS(v, r));
    }
}

contract RejectGuards_M_TRANSFER_SPENT_FIRST is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_SPENT_FIRST(v, r));
    }
}

contract RejectGuards_M_TRANSFER_SPENT_SECOND is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_SPENT_SECOND(v, r));
    }
}

contract RejectGuards_M_TRANSFER_ROOT is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_ROOT(v, r));
    }
}

contract RejectGuards_M_WITHDRAW_ZERO_AMOUNT is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_ZERO_AMOUNT(v, r));
    }
}

contract RejectGuards_M_WITHDRAW_AMOUNT_MAX is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_AMOUNT_MAX(v, r));
    }
}

contract RejectGuards_M_WITHDRAW_SPENT is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_SPENT(v, r));
    }
}

contract RejectGuards_M_WITHDRAW_ROOT is RejectGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_ROOT(v, r));
    }
}
