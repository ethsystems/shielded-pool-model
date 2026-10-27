// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Canonical public inputs (rule S1) for ShieldedPool (ethsystems/pocs a04b8b3), for the PATCHED KEVM (abi.md:456
// without the 2^30 `ensures`), so every `bytes` argument has a symbolic length < 2^64 and symbolic
// content. Property, per entry point: every call that reaches the verifier carries only canonical
// public inputs (each word < P, the BN254 scalar field modulus).
// Design notes (as in PublicInputs.t.sol, which this file imports for the registry and the S2 bodies):
//  - The test contract calls the pool itself. No vm.prank with a symbolic caller (a symbolic
//    caller makes foundry_loadAccount split once per account, and earlier checks stalled there). deposit requires msg.sender ==
//    fundingAddress, so the funding address is this test contract.
//  - Pool storage is symbolic with three pins (slot 108 = verifier, 109 = registry, reentrancy
//    slot = 1). Registry storage is symbolic. The token address is a symbolic argument.
//  - The verifier checks every input word itself: any word >= P reverts NonCanonical(); otherwise
//    it reverts Reached(). The pool does not catch either, so no state change follows the verifier
//    call. Each entry point makes exactly one verifier call [read], so stopping there loses nothing.
//  - After the pool call the test reads the revert selector through scratch memory only (_sel).
//  - No per-word split: the verifier's own loop branches per word.

import {Test} from "forge-std/src/Test.sol";
import {KontrolCheats} from "kontrol-cheatcodes/KontrolCheats.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {LeanIMT} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";
import {SymRegistry, InputOrder} from "./PublicInputs.t.sol";
import {ShieldedPool_M_DEPOSIT_CANONICAL} from "./mutants/ShieldedPool_M_DEPOSIT_CANONICAL.sol";
import {ShieldedPool_M_TRANSFER_CANONICAL} from "./mutants/ShieldedPool_M_TRANSFER_CANONICAL.sol";
import {ShieldedPool_M_WITHDRAW_CANONICAL} from "./mutants/ShieldedPool_M_WITHDRAW_CANONICAL.sol";
import {ShieldedPool_M_BOUND_GT} from "./mutants/ShieldedPool_M_BOUND_GT.sol";

contract CanonVerifier is IVerifier {
    error NonCanonical();
    error Reached();

    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    function _chk(bytes32[] calldata pi) internal pure {
        for (uint256 i = 0; i < pi.length; i++) {
            if (uint256(pi[i]) >= P) revert NonCanonical();
        }
        revert Reached();
    }

    function verifyDeposit(bytes calldata, bytes32[] calldata pi) external pure returns (bool) {
        _chk(pi);
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata pi) external pure returns (bool) {
        _chk(pi);
    }

    function verifyWithdraw(bytes calldata, bytes32[] calldata pi) external pure returns (bool) {
        _chk(pi);
    }
}

abstract contract CanonicalBase is Test, KontrolCheats {
    bytes32 internal constant REENTRANCY_SLOT = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;

    ShieldedPool internal pool;
    CanonVerifier internal verifier;
    SymRegistry internal registry;

    function setUp() public {
        bytes memory init = type(LeanIMT).creationCode;
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(address(0xA1001), tmp.code);
        verifier = new CanonVerifier();
        registry = new SymRegistry();
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
    }

    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    function _fresh() internal virtual {
        kevm.symbolicStorage(address(pool));
        vm.store(address(pool), bytes32(uint256(108)), bytes32(uint256(uint160(address(verifier)))));
        vm.store(address(pool), bytes32(uint256(109)), bytes32(uint256(uint160(address(registry)))));
        vm.store(address(pool), REENTRANCY_SLOT, bytes32(uint256(1)));
        kevm.symbolicStorage(address(registry));
    }

    /// Selector of the last call's revert data, through scratch memory only.
    function _sel() internal pure returns (bytes4 s) {
        assembly {
            mstore(0, 0)
            if gt(returndatasize(), 3) { returndatacopy(0, 0, 4) }
            s := mload(0)
        }
    }
}

contract CanonicalInputs is CanonicalBase {
    error S1NonCanonical();
    error S1Returned();

    struct Tr {
        bytes32 n0;
        bytes32 n1;
        bytes32 c0;
        bytes32 c1;
        bytes32 r;
    }

    /// A call that returns is a failure (the verifier never says yes). A NonCanonical revert from
    /// the verifier is the S1 violation. Witness bodies must FAIL: the verifier is reached.
    function _check(bool ok, bytes4 sel, bool witness) internal pure {
        if (ok) revert S1Returned();
        if (sel == CanonVerifier.NonCanonical.selector) revert S1NonCanonical();
        if (witness) assert(sel != CanonVerifier.Reached.selector);
    }

    function _dep(bytes32 c, address t, uint256 a, bytes calldata proof, bytes calldata note, bool witness)
        internal
    {
        bool ok;
        bytes4 sel;
        try pool.deposit(proof, c, t, a, address(this), note) {
            ok = true;
        } catch {
            sel = _sel();
        }
        _check(ok, sel, witness);
    }

    function _tr(Tr memory x, bytes calldata proof, bytes calldata note, bool witness) internal {
        bool ok;
        bytes4 sel;
        try pool.transfer(proof, [x.n0, x.n1], [x.c0, x.c1], x.r, note) {
            ok = true;
        } catch {
            sel = _sel();
        }
        _check(ok, sel, witness);
    }

    function _wd(bytes32 n, address t, uint256 a, address rcp, bytes32 r, bytes calldata proof, bool witness)
        internal
    {
        bool ok;
        bytes4 sel;
        try pool.withdraw(proof, n, t, a, rcp, r) {
            ok = true;
        } catch {
            sel = _sel();
        }
        _check(ok, sel, witness);
    }

    /// Deposit: empty proof, payload of symbolic length and content.
    function prove_deposit_canonical(bytes32 c, address t, uint256 a, bytes calldata note) public {
        _fresh();
        _dep(c, t, a, note[:0], note, false);
    }

    function prove_witness_deposit_canonical_mustfail(bytes32 c, address t, uint256 a, bytes calldata note) public {
        _fresh();
        _dep(c, t, a, note[:0], note, true);
    }

    /// Deposit: proof = blob[:s], payload = blob[s:], both symbolic length and content.
    function prove_deposit_canonical_split(bytes32 c, address t, uint256 a, bytes calldata blob, uint256 s) public {
        vm.assume(s <= blob.length);
        _fresh();
        _dep(c, t, a, blob[:s], blob[s:], false);
    }

    function prove_transfer_canonical(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes calldata note) public {
        _fresh();
        _tr(Tr(n0, n1, c0, c1, r), note[:0], note, false);
    }

    function prove_witness_transfer_canonical_mustfail(
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes calldata note
    ) public {
        _fresh();
        _tr(Tr(n0, n1, c0, c1, r), note[:0], note, true);
    }

    function prove_transfer_canonical_split(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes calldata blob, uint256 s)
        public
    {
        vm.assume(s <= blob.length);
        _fresh();
        _tr(Tr(n0, n1, c0, c1, r), blob[:s], blob[s:], false);
    }

    /// Withdraw: proof of symbolic length and content (the only bytes argument).
    function prove_withdraw_canonical(bytes32 n, address t, uint256 a, address rcp, bytes32 r, bytes calldata proof) public {
        _fresh();
        _wd(n, t, a, rcp, r, proof, false);
    }

    function prove_witness_withdraw_canonical_mustfail(bytes32 n, address t, uint256 a, address rcp, bytes32 r, bytes calldata proof)
        public
    {
        _fresh();
        _wd(n, t, a, rcp, r, proof, true);
    }
}

// S2 non-vacuity for the single-payload bodies of InputOrder (it has witnesses only for its blob bodies).
contract InputOrderWitness is InputOrder {
    function prove_witness_deposit_order_mustfail(bytes32 c, address t, uint256 a, bytes calldata note) public {
        _fresh();
        _depS2(c, t, a, note[:0], note, true);
    }

    function prove_witness_transfer_order_mustfail(
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes calldata note
    ) public {
        _fresh();
        _trS2(Tr(n0, n1, c0, c1, r), note[:0], note, true);
    }
}

// Must-fail siblings: the same bodies against a pool with one canonicality check removed
// (mutants/make.py).
contract CanonicalInputs_M_DEPOSIT_CANONICAL is CanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_CANONICAL(v, r));
    }
}

contract CanonicalInputs_M_TRANSFER_CANONICAL is CanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_CANONICAL(v, r));
    }
}

contract CanonicalInputs_M_WITHDRAW_CANONICAL is CanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WITHDRAW_CANONICAL(v, r));
    }
}

contract CanonicalInputs_M_BOUND_GT is CanonicalInputs {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_BOUND_GT(v, r));
    }
}
