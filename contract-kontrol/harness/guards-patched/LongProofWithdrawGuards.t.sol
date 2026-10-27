// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The withdraw rejection guards of ShieldedPool (ethsystems/pocs a04b8b3) under Kontrol 1.0.255 with
// the patched KEVM (abi.md without `ensures lengthBytes(BS) <=Int 1073741824` on the #bytes encoding
// rule), so the `proof` argument has one symbolic length below 2^64 and symbolic content.
// Same property as RejectGuards.t.sol (every earlier guard passes, this guard fails; the call
// reverts with this guard's selector, never the verifier marker). Two changes, forced by Solidity:
//  1. The scalars travel in a memory struct, which keeps legacy codegen below the stack limit.
//  2. The pool is called with a high-level try/catch call. It encodes the arguments at the free
//     memory pointer without allocating them, so no Panic(0x41) for encodings near 2^64 bytes
//     (abi.encodeWithSelector allocates and would panic).
// The prove_noncanonical_* checks are part of the same test contract; they do not close in
// Kontrol 1.0.255 (README.md) and no run of this package selects them.

import {Test} from "forge-std/src/Test.sol";
import {KontrolCheats} from "kontrol-cheatcodes/KontrolCheats.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {LeanIMT} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";
import {ShieldedPool_M_WITHDRAW_ZERO_AMOUNT} from "./mutants/ShieldedPool_M_WITHDRAW_ZERO_AMOUNT.sol";
import {ShieldedPool_M_WITHDRAW_AMOUNT_MAX} from "./mutants/ShieldedPool_M_WITHDRAW_AMOUNT_MAX.sol";
import {ShieldedPool_M_WITHDRAW_SPENT} from "./mutants/ShieldedPool_M_WITHDRAW_SPENT.sol";
import {ShieldedPool_M_WITHDRAW_ROOT} from "./mutants/ShieldedPool_M_WITHDRAW_ROOT.sol";

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

contract SymRegistry {
    bytes32 public root;

    function attestationRoot() external view returns (bytes32) {
        return root;
    }
}

abstract contract LongProofGuardsBase is Test, KontrolCheats {
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant MAX_AMOUNT = 1 << 128;
    bytes32 internal constant REENTRANCY_SLOT = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;

    ShieldedPool internal pool;
    TripVerifier internal verifier;
    SymRegistry internal registry;

    function setUp() public {
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

    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    function _fresh() internal {
        kevm.symbolicStorage(address(pool));
        vm.store(address(pool), bytes32(uint256(108)), bytes32(uint256(uint160(address(verifier)))));
        vm.store(address(pool), bytes32(uint256(109)), bytes32(uint256(uint160(address(registry)))));
        vm.store(address(pool), REENTRANCY_SLOT, bytes32(uint256(1)));
        kevm.symbolicStorage(address(registry));
    }

    function _known(bytes32 r) internal view returns (bool) {
        return r == pool.commitmentRoot() || pool.validRoots(r);
    }

    /// Guard selector, or the pool decoder's empty revert when the proof is too long for a second
    /// dynamic offset (only possible above 2^63 bytes). Never the verifier marker.
    function _ok(bytes4 sel, bytes4 guard, uint256 proofLen) internal pure returns (bool) {
        return sel == guard || (sel == bytes4(0) && proofLen > 2 ** 63);
    }
}

contract LongProofWithdrawGuards is LongProofGuardsBase {
    struct Wd {
        bytes32 n;
        address t;
        uint256 a;
        address rcp;
        bytes32 r;
        address caller;
    }

    function _pass(uint256 k, Wd memory x) internal view {
        if (k > 1) vm.assume(pool.supportedTokens(x.t));
        if (k > 2) vm.assume(x.a != 0);
        if (k > 3) vm.assume(x.a < MAX_AMOUNT);
        if (k > 4) vm.assume(x.rcp != address(0));
        if (k > 5) vm.assume(!pool.nullifiers(x.n));
        if (k > 6) vm.assume(_known(x.r));
    }

    /// Withdraw has one `bytes`, so the pool's decoder has no second offset to reject: exact selector.
    function _run(Wd memory x, bytes calldata proof, bytes4 guard) internal {
        bytes4 sel;
        vm.prank(x.caller);
        try pool.withdraw(proof, x.n, x.t, x.a, x.rcp, x.r) {
            assert(false);
        } catch (bytes memory ret) {
            sel = bytes4(ret);
        }
        assert(sel == guard);
    }

    function prove_withdraw_zero_amount(bytes32 n, address t, address rcp, bytes32 r, address caller, bytes calldata proof) public {
        _fresh();
        Wd memory x = Wd(n, t, 0, rcp, r, caller);
        _pass(2, x);
        _run(x, proof, ShieldedPool.ZeroAmount.selector);
    }

    function prove_withdraw_amount_max(bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller, bytes calldata proof)
        public
    {
        _fresh();
        Wd memory x = Wd(n, t, a, rcp, r, caller);
        _pass(3, x);
        vm.assume(a >= MAX_AMOUNT);
        _run(x, proof, ShieldedPool.AmountTooLarge.selector);
    }

    function prove_withdraw_spent(bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller, bytes calldata proof)
        public
    {
        _fresh();
        Wd memory x = Wd(n, t, a, rcp, r, caller);
        _pass(5, x);
        vm.assume(pool.nullifiers(n));
        _run(x, proof, ShieldedPool.NullifierAlreadySpent.selector);
    }

    function prove_withdraw_root(bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller, bytes calldata proof)
        public
    {
        _fresh();
        Wd memory x = Wd(n, t, a, rcp, r, caller);
        _pass(6, x);
        vm.assume(!_known(r));
        _run(x, proof, ShieldedPool.InvalidRoot.selector);
    }

    // ---- canonical inputs of withdraw (:275), split per input word: n, t, a, rcp, r. t and rcp are addresses and
    // a < 2^128 after the earlier guards, so only n and r can be noncanonical; _rest checks that.
    function prove_noncanonical_nullifier(bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller, bytes calldata proof) public {
        _fresh();
        Wd memory x = Wd(n, t, a, rcp, r, caller);
        _pass(7, x);
        vm.assume(uint256(n) >= P);
        _run(x, proof, ShieldedPool.PublicInputGeFieldModulus.selector);
    }

    function prove_noncanonical_root(bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller, bytes calldata proof) public {
        _fresh();
        Wd memory x = Wd(n, t, a, rcp, r, caller);
        _pass(7, x);
        vm.assume(uint256(n) < P);
        vm.assume(uint256(r) >= P);
        _run(x, proof, ShieldedPool.PublicInputGeFieldModulus.selector);
    }

    function prove_noncanonical_other(bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller, bytes calldata proof) public {
        _fresh();
        Wd memory x = Wd(n, t, a, rcp, r, caller);
        _pass(7, x);
        vm.assume(uint256(n) < P);
        vm.assume(uint256(r) < P);
        vm.assume(uint256(uint160(t)) >= P || a >= P || uint256(uint160(rcp)) >= P);
        _run(x, proof, ShieldedPool.PublicInputGeFieldModulus.selector);
    }
}

// Must-fail siblings: the same body against a pool with one withdraw guard removed. The first one
// was run with the earlier harness; the other three are added in this package.
contract LongProofWithdrawGuards_M_WITHDRAW_ZERO_AMOUNT is LongProofWithdrawGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_ZERO_AMOUNT(v, r));
    }
}

contract LongProofWithdrawGuards_M_WITHDRAW_AMOUNT_MAX is LongProofWithdrawGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_AMOUNT_MAX(v, r));
    }
}

contract LongProofWithdrawGuards_M_WITHDRAW_SPENT is LongProofWithdrawGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_SPENT(v, r));
    }
}

contract LongProofWithdrawGuards_M_WITHDRAW_ROOT is LongProofWithdrawGuards {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_ROOT(v, r));
    }
}
