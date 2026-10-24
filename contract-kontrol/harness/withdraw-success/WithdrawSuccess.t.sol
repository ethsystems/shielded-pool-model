// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Withdraw success path of ShieldedPool (ethsystems/pocs a04b8b3), rules W6 and W10, on the patched
// KEVM (abi.md without the 2^30 `ensures` of the #bytes encoding rule), so every `bytes` argument has a
// symbolic length below 2^64 and symbolic content. Three token scopes share one body (_body):
//  A `prove_success_token_above_0x11`: the token argument is any address above 0x11 except the
//    cheatcode account;
//  B `prove_success_two_tokens`: the token argument is symbolic, assumed to be one of the two
//    recording tokens;
//  C `prove_success_token_pick`: a symbolic bit picks one of the two recording tokens, so the token
//    is concrete on each branch.
// The caller is the test contract, except in `prove_caller_two_tokens` (vm.prank with a symbolic
// caller; a probe that does not close in Kontrol 1.0.255).
// Design notes:
//  - Pool storage is symbolic (kevm.symbolicStorage) with three pins: slot 108 = verifier, slot
//    109 = registry, reentrancy slot = 1 (NOT_ENTERED). Registry storage is symbolic.
//  - The test contract calls the pool itself. No vm.prank with a symbolic caller: there
//    foundry_loadAccount splits once per existing account, with an unconstrained default branch
//    that splits again in the same way.
//  - Two recording tokens, TOKEN at a fixed address and `other` at its CREATE address (both with
//    bit 159 set). Both are armed. On success exactly one retained transfer must reach the two
//    tokens, on the token the call (and the verifier inputs) named.
//  - IVerifier functions are view: the pool calls them with STATICCALL, so the verifier cannot
//    write storage. The test stores the expected inputs (full 256-bit words, from its own
//    arguments) and a symbolic `accept` flag in the verifier before the call; the verifier compares
//    word by word and reverts Diverged() on any difference. The pool does not catch it.
//  - After the pool call the test reads only through scratch memory (returndatacopy to 0,
//    staticcall output to 0), never at the free pointer, where the symbolic-length encoding lies.

import {Test} from "forge-std/src/Test.sol";
import {KontrolCheats} from "kontrol-cheatcodes/KontrolCheats.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {LeanIMT} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";
import {ShieldedPool_M_LATE_MARK} from "./mutants/ShieldedPool_M_LATE_MARK.sol";
import {ShieldedPool_M_SWAP_INPUTS} from "./mutants/ShieldedPool_M_SWAP_INPUTS.sol";
import {ShieldedPool_M_DROP_BIT253} from "./mutants/ShieldedPool_M_DROP_BIT253.sol";
import {ShieldedPool_M_PAY_CALLER} from "./mutants/ShieldedPool_M_PAY_CALLER.sol";
import {ShieldedPool_M_SKIP_VERIFIER} from "./mutants/ShieldedPool_M_SKIP_VERIFIER.sol";
import {ShieldedPool_M_FIXED_TOKEN} from "./mutants/ShieldedPool_M_FIXED_TOKEN.sol";

contract CmpVerifier is IVerifier {
    error Diverged();
    error Matched();

    bool internal accept;
    uint256 internal expLen;
    bytes32[6] internal exp;

    function setExp(bool acc, uint256 len, bytes32[6] calldata e) external {
        accept = acc;
        expLen = len;
        exp = e;
    }

    function _same(bytes32[] calldata pi) internal view returns (bool) {
        if (pi.length != expLen) return false;
        for (uint256 i = 0; i < pi.length; i++) {
            if (pi[i] != exp[i]) return false;
        }
        return true;
    }

    /// S2: stop at the verifier, so no tree insertion runs.
    function verifyDeposit(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        if (!_same(pi)) revert Diverged();
        revert Matched();
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        if (!_same(pi)) revert Diverged();
        revert Matched();
    }

    /// W10: the answer is the symbolic `accept`, given only for the expected inputs.
    function verifyWithdraw(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        if (!_same(pi)) revert Diverged();
        return accept;
    }
}

contract SymRegistry {
    bytes32 public root;

    function attestationRoot() external view returns (bytes32) {
        return root;
    }
}

/// Recording token. transfer() records its arguments, its caller, and the pool's nullifier flag
/// for the watched key AT THE TIME OF THE CALL (W6). Any other selector is counted in `others`.
contract RecToken {
    address internal pool;
    bytes32 internal watch;
    uint256 public calls;
    uint256 public others;
    address public from;
    address public to;
    uint256 public amt;
    bool public spentSeen;

    function arm(address p, bytes32 w) external {
        pool = p;
        watch = w;
    }

    function transfer(address t, uint256 v) external returns (bool) {
        calls += 1;
        from = msg.sender;
        to = t;
        amt = v;
        spentSeen = ShieldedPool(pool).nullifiers(watch);
        return true;
    }

    fallback() external {
        others += 1;
    }
}

abstract contract WithdrawSuccessBase is Test, KontrolCheats {
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    bytes32 internal constant REENTRANCY_SLOT = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;
    address internal constant TOKEN = address(uint160((uint256(0xF) << 156) | 0xB));

    ShieldedPool internal pool;
    CmpVerifier internal verifier;
    SymRegistry internal registry;
    RecToken internal other;

    function setUp() public {
        bytes memory init = type(LeanIMT).creationCode;
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(address(0xA1001), tmp.code);
        verifier = new CmpVerifier();
        registry = new SymRegistry();
        RecToken t = new RecToken();
        vm.etch(TOKEN, address(t).code);
        other = new RecToken();
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
    function _sel() internal view returns (bytes4 s) {
        assembly {
            mstore(0, 0)
            if gt(returndatasize(), 3) { returndatacopy(0, 0, 4) }
            s := mload(0)
        }
    }

    /// One-word getter result, through scratch memory only.
    function _get(address c, bytes4 s) internal view returns (uint256 v) {
        assembly {
            mstore(0, s)
            if iszero(staticcall(gas(), c, 0, 4, 0, 0x20)) { revert(0, 0) }
            v := mload(0)
        }
    }

    function _get1(address c, bytes4 s, bytes32 k) internal view returns (uint256 v) {
        assembly {
            mstore(0, s)
            mstore(4, k)
            if iszero(staticcall(gas(), c, 0, 0x24, 0, 0x20)) { revert(0, 0) }
            v := mload(0)
        }
    }
}

contract WithdrawSuccess is WithdrawSuccessBase {
    error W10Inputs();
    error W10VerifierBypassed();
    error W6NotMarkedAtPayout();
    error W6NotMarkedAfter();
    error W10Calls();
    error W10Args();
    error W10WrongToken();

    function _wd(bytes calldata proof, bytes32 n, address token, uint256 a, address rcp, bytes32 r, bool acc)
        internal
        returns (bool ok, bytes4 sel)
    {
        verifier.setExp(
            acc, 5, [n, bytes32(uint256(uint160(token))), bytes32(a), bytes32(uint256(uint160(rcp))), r, bytes32(0)]
        );
        RecToken(TOKEN).arm(address(pool), n);
        other.arm(address(pool), n);
        if (pranked) vm.prank(caller);
        try pool.withdraw(proof, n, token, a, rcp, r) {
            ok = true;
        } catch {
            sel = _sel();
        }
    }

    bool internal pranked;
    address internal caller;

    /// W6 and W10, every path, for the token argument `token`. Any call: the verifier never saw inputs
    /// other than [n, token, a, rcp, r] (else Diverged surfaces). A successful call: the verifier said
    /// yes (acc); exactly one retained recorded call reached the two tokens, and it went to `token`;
    /// the nullifier was already marked when that token was called (W6) and is marked after; the call
    /// was transfer(rcp, a) from the pool; neither token recorded any other call.
    function _body(bytes calldata proof, bytes32 n, address token, uint256 a, address rcp, bytes32 r, bool acc)
        internal
    {
        _fresh();
        (bool ok, bytes4 sel) = _wd(proof, n, token, a, rcp, r, acc);
        if (!ok) {
            if (sel == CmpVerifier.Diverged.selector) revert W10Inputs();
            return;
        }
        if (!acc) revert W10VerifierBypassed();
        uint256 cA = _get(TOKEN, RecToken(TOKEN).calls.selector);
        uint256 cB = _get(address(other), RecToken(TOKEN).calls.selector);
        if (cA + cB != 1) revert W10Calls();
        address moved = cA == 1 ? TOKEN : address(other);
        if (moved != token) revert W10WrongToken();
        if (_get(moved, RecToken(TOKEN).spentSeen.selector) != 1) revert W6NotMarkedAtPayout();
        if (_get1(address(pool), pool.nullifiers.selector, n) != 1) revert W6NotMarkedAfter();
        if (_get(TOKEN, RecToken(TOKEN).others.selector) != 0) revert W10Calls();
        if (_get(address(other), RecToken(TOKEN).others.selector) != 0) revert W10Calls();
        if (_get(moved, RecToken(TOKEN).to.selector) != uint256(uint160(rcp))) revert W10Args();
        if (_get(moved, RecToken(TOKEN).amt.selector) != a) revert W10Args();
        if (_get(moved, RecToken(TOKEN).from.selector) != uint256(uint160(address(pool)))) revert W10Args();
    }

    /// Scope A: the token is any address above 0x11 except the cheatcode account.
    /// 0x00..0x11 excluded: KEVM's isPrecompiledAccount is 0 < t <= #precompiledAccountsUB(SCHED),
    /// at most 17 over all schedules, and without this bound the no-account branch stalls on
    /// #precompiled(token).
    function prove_success_token_above_0x11(bytes32 n, address token, uint256 a, address rcp, bytes32 r, bool acc, bytes calldata proof)
        public
    {
        vm.assume(token != address(vm));
        vm.assume(uint160(token) > 0x11);
        _body(proof, n, token, a, rcp, r, acc);
    }

    /// Scope B: the token is symbolic and assumed to be one of the two recording tokens.
    function prove_success_two_tokens(bytes32 n, address token, uint256 a, address rcp, bytes32 r, bool acc, bytes calldata proof)
        public
    {
        vm.assume(token == TOKEN || token == address(other));
        _body(proof, n, token, a, rcp, r, acc);
    }

    /// Scope C: a symbolic bit picks one of the two recording tokens (concrete on each branch).
    function prove_success_token_pick(bytes32 n, bool pick, uint256 a, address rcp, bytes32 r, bool acc, bytes calldata proof)
        public
    {
        _body(proof, n, pick ? address(other) : TOKEN, a, rcp, r, acc);
    }

    /// Scope B with a symbolic caller (vm.prank). Probe only.
    function prove_caller_two_tokens(
        bytes32 n,
        address token,
        uint256 a,
        address rcp,
        bytes32 r,
        bool acc,
        address who,
        bytes calldata proof
    ) public {
        vm.assume(token == TOKEN || token == address(other));
        pranked = true;
        caller = who;
        _body(proof, n, token, a, rcp, r, acc);
    }

    /// Non-vacuity: MUST FAIL. A successful withdraw exists in this environment (scope A).
    function prove_witness_any_token_mustfail(
        bytes32 n,
        address token,
        uint256 a,
        address rcp,
        bytes32 r,
        bool acc,
        bytes calldata proof
    ) public {
        vm.assume(token != address(vm));
        _fresh();
        (bool ok,) = _wd(proof, n, token, a, rcp, r, acc);
        assert(!ok);
    }

    /// Non-vacuity, scope B: MUST FAIL. Must fail for the low token too: see prove_W2_witness_other_mustfail.
    function prove_witness_two_tokens_mustfail(
        bytes32 n,
        address token,
        uint256 a,
        address rcp,
        bytes32 r,
        bool acc,
        bytes calldata proof
    ) public {
        vm.assume(token == TOKEN || token == address(other));
        _fresh();
        (bool ok,) = _wd(proof, n, token, a, rcp, r, acc);
        assert(!ok);
    }

    /// Non-vacuity for the low token `other`: MUST FAIL (a withdraw naming `other` succeeds).
    function prove_witness_other_token_mustfail(bytes32 n, uint256 a, address rcp, bytes32 r, bool acc, bytes calldata proof)
        public
    {
        _fresh();
        (bool ok,) = _wd(proof, n, address(other), a, rcp, r, acc);
        assert(!ok);
    }

    /// Non-vacuity for scope C: MUST FAIL.
    function prove_witness_token_pick_mustfail(
        bytes32 n,
        bool pick,
        uint256 a,
        address rcp,
        bytes32 r,
        bool acc,
        bytes calldata proof
    ) public {
        _fresh();
        (bool ok,) = _wd(proof, n, pick ? address(other) : TOKEN, a, rcp, r, acc);
        assert(!ok);
    }
}

// Must-fail siblings: the same bodies against a pool with one change (mutants/make.py).
contract WithdrawSuccess_M_LATE_MARK is WithdrawSuccess {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_LATE_MARK(v, r));
    }
}

contract WithdrawSuccess_M_SWAP_INPUTS is WithdrawSuccess {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SWAP_INPUTS(v, r));
    }
}

contract WithdrawSuccess_M_DROP_BIT253 is WithdrawSuccess {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DROP_BIT253(v, r));
    }
}

contract WithdrawSuccess_M_PAY_CALLER is WithdrawSuccess {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_CALLER(v, r));
    }
}

contract WithdrawSuccess_M_SKIP_VERIFIER is WithdrawSuccess {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SKIP_VERIFIER(v, r));
    }
}

contract WithdrawSuccess_M_FIXED_TOKEN is WithdrawSuccess {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_FIXED_TOKEN(v, r));
    }
}
