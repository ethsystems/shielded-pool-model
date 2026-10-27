// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Withdraw success path with one fixed token (rules W6, W10) and the input order of deposit and
// transfer (rule S2) for ShieldedPool (ethsystems/pocs a04b8b3), for the PATCHED KEVM (abi.md:456 without the 2^30 `ensures`), so every
// `bytes` argument has a symbolic length < 2^64 and symbolic content.
// Design notes:
//  - Pool storage is symbolic (kevm.symbolicStorage) with three pins: slot 108 = verifier, slot
//    109 = registry, reentrancy slot = 1 (NOT_ENTERED). Registry storage is symbolic.
//  - The test contract calls the pool itself. No vm.prank with a symbolic caller: there
//    foundry_loadAccount splits once per account, with an unconstrained default branch that splits again.
//    withdraw and transfer never read msg.sender; deposit requires msg.sender == fundingAddress,
//    so the funding address is this test contract.
//  - The token lives at a fixed high address (bit 159 set). A second token ("other") must never
//    be called.
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
import {ShieldedPool_M_DEPOSIT_SWAP_45} from "./mutants/ShieldedPool_M_DEPOSIT_SWAP_45.sol";
import {ShieldedPool_M_TRANSFER_SWAP_45} from "./mutants/ShieldedPool_M_TRANSFER_SWAP_45.sol";

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

abstract contract PublicInputsBase is Test, KontrolCheats {
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

contract FixedTokenWithdraw is PublicInputsBase {
    error W10Inputs();
    error W10VerifierBypassed();
    error W6NotMarkedAtPayout();
    error W6NotMarkedAfter();
    error W10Calls();
    error W10Args();
    error W10OtherToken();

    function _wd(bytes calldata proof, bytes32 n, uint256 a, address rcp, bytes32 r, bool acc)
        internal
        returns (bool ok, bytes4 sel)
    {
        verifier.setExp(
            acc, 5, [n, bytes32(uint256(uint160(TOKEN))), bytes32(a), bytes32(uint256(uint160(rcp))), r, bytes32(0)]
        );
        RecToken(TOKEN).arm(address(pool), n);
        try pool.withdraw(proof, n, TOKEN, a, rcp, r) {
            ok = true;
        } catch {
            sel = _sel();
        }
    }

    /// W6 and W10, every path. Any call: the verifier never saw inputs other than
    /// [n, token, a, rcp, r] (else Diverged surfaces). A successful call: the verifier said yes
    /// (acc), the nullifier was already marked when the token was called (W6) and is marked after;
    /// the token got exactly one call, transfer(rcp, a) from the pool; the other token got none.
    function prove_success_fixed_token(bytes32 n, uint256 a, address rcp, bytes32 r, bool acc, bytes calldata proof) public {
        _fresh();
        (bool ok, bytes4 sel) = _wd(proof, n, a, rcp, r, acc);
        if (!ok) {
            if (sel == CmpVerifier.Diverged.selector) revert W10Inputs();
            return;
        }
        if (!acc) revert W10VerifierBypassed();
        if (_get(TOKEN, RecToken(TOKEN).spentSeen.selector) != 1) revert W6NotMarkedAtPayout();
        if (_get1(address(pool), pool.nullifiers.selector, n) != 1) revert W6NotMarkedAfter();
        if (_get(TOKEN, RecToken(TOKEN).calls.selector) != 1) revert W10Calls();
        if (_get(TOKEN, RecToken(TOKEN).others.selector) != 0) revert W10Calls();
        if (_get(TOKEN, RecToken(TOKEN).to.selector) != uint256(uint160(rcp))) revert W10Args();
        if (_get(TOKEN, RecToken(TOKEN).amt.selector) != a) revert W10Args();
        if (_get(TOKEN, RecToken(TOKEN).from.selector) != uint256(uint160(address(pool)))) revert W10Args();
        if (_get(address(other), RecToken(TOKEN).calls.selector) != 0) revert W10OtherToken();
        if (_get(address(other), RecToken(TOKEN).others.selector) != 0) revert W10OtherToken();
    }

    /// Non-vacuity: MUST FAIL. A successful withdraw exists in this environment.
    function prove_witness_fixed_token_mustfail(bytes32 n, uint256 a, address rcp, bytes32 r, bool acc, bytes calldata proof)
        public
    {
        _fresh();
        (bool ok,) = _wd(proof, n, a, rcp, r, acc);
        assert(!ok);
    }
}

contract InputOrder is PublicInputsBase {
    error S2Inputs();
    error S2Returned();

    struct Tr {
        bytes32 n0;
        bytes32 n1;
        bytes32 c0;
        bytes32 c1;
        bytes32 r;
    }

    function _pc(bytes calldata note) internal pure returns (bytes32) {
        return bytes32(uint256(keccak256(note)) % P);
    }

    function _check(bool ok, bytes4 sel, bool witness) internal pure {
        if (ok) revert S2Returned();
        if (sel == CmpVerifier.Diverged.selector) revert S2Inputs();
        if (witness) assert(sel != CmpVerifier.Matched.selector);
    }

    function _depS2(bytes32 c, address t, uint256 a, bytes calldata proof, bytes calldata note, bool witness) internal {
        verifier.setExp(
            true,
            6,
            [
                c,
                bytes32(uint256(uint160(t))),
                bytes32(a),
                bytes32(uint256(uint160(address(this)))),
                registry.root(),
                _pc(note)
            ]
        );
        bool ok;
        bytes4 sel;
        try pool.deposit(proof, c, t, a, address(this), note) {
            ok = true;
        } catch {
            sel = _sel();
        }
        _check(ok, sel, witness);
    }

    function _trS2(Tr memory x, bytes calldata proof, bytes calldata note, bool witness) internal {
        verifier.setExp(true, 6, [x.n0, x.n1, x.c0, x.c1, x.r, _pc(note)]);
        bool ok;
        bytes4 sel;
        try pool.transfer(proof, [x.n0, x.n1], [x.c0, x.c1], x.r, note) {
            ok = true;
        } catch {
            sel = _sel();
        }
        _check(ok, sel, witness);
    }

    /// S2 deposit: proof = blob[:s], payload = blob[s:], both symbolic length and content.
    function prove_deposit_order_split(bytes32 c, address t, uint256 a, bytes calldata blob, uint256 s) public {
        vm.assume(s <= blob.length);
        _fresh();
        _depS2(c, t, a, blob[:s], blob[s:], false);
    }

    function prove_witness_deposit_order_split_mustfail(bytes32 c, address t, uint256 a, bytes calldata blob, uint256 s) public {
        vm.assume(s <= blob.length);
        _fresh();
        _depS2(c, t, a, blob[:s], blob[s:], true);
    }

    /// S2 deposit, fallback: empty proof, payload symbolic length and content.
    function prove_deposit_order(bytes32 c, address t, uint256 a, bytes calldata note) public {
        _fresh();
        _depS2(c, t, a, note[:0], note, false);
    }

    function prove_transfer_order_split(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes calldata blob, uint256 s)
        public
    {
        vm.assume(s <= blob.length);
        _fresh();
        _trS2(Tr(n0, n1, c0, c1, r), blob[:s], blob[s:], false);
    }

    function prove_witness_transfer_order_split_mustfail(
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes calldata blob,
        uint256 s
    ) public {
        vm.assume(s <= blob.length);
        _fresh();
        _trS2(Tr(n0, n1, c0, c1, r), blob[:s], blob[s:], true);
    }

    function prove_transfer_order(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes calldata note) public {
        _fresh();
        _trS2(Tr(n0, n1, c0, c1, r), note[:0], note, false);
    }
}

// Must-fail siblings: the same bodies against a pool with one change (mutants/make.py).
contract FixedTokenWithdraw_M_LATE_MARK is FixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_LATE_MARK(v, r));
    }
}

contract FixedTokenWithdraw_M_SWAP_INPUTS is FixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SWAP_INPUTS(v, r));
    }
}

contract FixedTokenWithdraw_M_DROP_BIT253 is FixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DROP_BIT253(v, r));
    }
}

contract FixedTokenWithdraw_M_PAY_CALLER is FixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_CALLER(v, r));
    }
}

contract FixedTokenWithdraw_M_SKIP_VERIFIER is FixedTokenWithdraw {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_SKIP_VERIFIER(v, r));
    }
}

contract InputOrder_M_DEPOSIT_SWAP_45 is InputOrder {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEPOSIT_SWAP_45(v, r));
    }
}

contract InputOrder_M_TRANSFER_SWAP_45 is InputOrder {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TRANSFER_SWAP_45(v, r));
    }
}
