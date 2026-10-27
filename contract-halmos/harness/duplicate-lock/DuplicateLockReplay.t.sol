// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Concrete replays of this suite (forge test, concrete EVM). They show that every failing Halmos node has a
// feasible concrete witness inside the check's domain: the real PoseidonT3 and the real (or mutant)
// LeanIMT are etched at the linked addresses, states are reached from the empty pool by real calls
// (the lock-held replays alone set the status slot directly, as the Halmos checks do), and argument
// values are the ones in the Halmos counterexamples (c = 2^253, amount = 2^127, funder 2^159,
// 65-byte proof and payload of zero bytes). Each replay runs the stock code and the mutant on the
// same calls.

import {Test} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {MockERC20} from "../../src/mocks/MockERC20.sol";
import {ReentrancyGuard} from "@openzeppelin-contracts/utils/ReentrancyGuard.sol";
import {SwitchVerifier, SwitchRegistry, SwitchToken, LibProbe, Trip} from "./DuplicateLock.t.sol";
import {ShieldedPool_M_NR_D} from "./mutants/ShieldedPool_M_NR_D.sol";
import {ShieldedPool_M_NR_T} from "./mutants/ShieldedPool_M_NR_T.sol";
import {ShieldedPool_M_NR_W} from "./mutants/ShieldedPool_M_NR_W.sol";
import {ShieldedPool_M_SKIP} from "./mutants/ShieldedPool_M_SKIP.sol";
import {ShieldedPool_M_ARG} from "./mutants/ShieldedPool_M_ARG.sol";

/// Token whose first transfer or transferFrom calls one configured pool function (re-entry), then
/// records whether that inner call succeeded and its return data. Moves no balances.
contract HookToken {
    address public pool;
    bytes public inner;
    uint256 public calls;
    bool public tried;
    bool public innerOk;
    bytes public innerRet;

    function arm(address p, bytes calldata data) external {
        pool = p;
        inner = data;
    }

    function _hook() internal {
        calls += 1;
        if (calls != 1 || inner.length == 0) return;
        tried = true;
        (bool ok, bytes memory ret) = pool.call(inner);
        innerOk = ok;
        innerRet = ret;
    }

    function transferFrom(address, address, uint256) external returns (bool) {
        _hook();
        return true;
    }

    function transfer(address, uint256) external returns (bool) {
        _hook();
        return true;
    }
}

contract DuplicateLockReplayTest is Test {
    bytes32 internal constant LOCK = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;
    bytes4 internal constant LEAF_EXISTS = bytes4(keccak256("LeafAlreadyExists()"));
    bytes4 internal constant GUARD = ReentrancyGuard.ReentrancyGuardReentrantCall.selector;
    bytes32 internal constant C = bytes32(uint256(1) << 253);
    bytes32 internal constant D = bytes32(uint256(3) << 252);
    bytes32 internal constant E = bytes32(uint256(5));
    uint256 internal constant A = uint256(1) << 127;
    address internal constant F = address(uint160(1) << 159);
    address internal constant RCP = address(uint160(1) << 159);

    enum Kind {
        STOCK,
        SKIP,
        ARG,
        NR_D,
        NR_T,
        NR_W
    }

    SwitchVerifier internal verifier;
    SwitchRegistry internal registry;
    bytes internal proof;
    bytes internal note;

    function _etch(string memory artifact, address at) internal {
        bytes memory init = vm.getCode(artifact);
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(at, tmp.code);
    }

    function setUp() public {
        _etch("LeanIMT.sol:LeanIMT", address(0xA1001));
        _etch("PoseidonT3.sol:PoseidonT3", address(0xA1002));
        verifier = new SwitchVerifier();
        registry = new SwitchRegistry();
        proof = new bytes(65);
        note = new bytes(65);
    }

    function _pool(Kind k) internal returns (ShieldedPool p) {
        address v = address(verifier);
        address r = address(registry);
        if (k == Kind.STOCK) p = new ShieldedPool(v, r);
        else if (k == Kind.SKIP) p = ShieldedPool(address(new ShieldedPool_M_SKIP(v, r)));
        else if (k == Kind.ARG) p = ShieldedPool(address(new ShieldedPool_M_ARG(v, r)));
        else if (k == Kind.NR_D) p = ShieldedPool(address(new ShieldedPool_M_NR_D(v, r)));
        else if (k == Kind.NR_T) p = ShieldedPool(address(new ShieldedPool_M_NR_T(v, r)));
        else p = ShieldedPool(address(new ShieldedPool_M_NR_W(v, r)));
    }

    function _leafIdx(ShieldedPool p, bytes32 x) internal view returns (uint256) {
        return uint256(vm.load(address(p), keccak256(abi.encode(uint256(x), uint256(3)))));
    }

    function _funded(ShieldedPool p) internal returns (MockERC20 t) {
        t = new MockERC20("T", "T", 18);
        p.addSupportedToken(address(t));
        t.mint(F, 2 * A);
        vm.prank(F);
        t.approve(address(p), type(uint256).max);
    }

    function _dep(ShieldedPool p, address tok, bytes32 c) internal returns (bool ok, bytes memory ret) {
        vm.prank(F);
        (ok, ret) = address(p).call(abi.encodeCall(ShieldedPool.deposit, (proof, c, tok, A, F, note)));
    }

    function _depData(bytes32 c, address tok, address f) internal view returns (bytes memory) {
        return abi.encodeCall(ShieldedPool.deposit, (proof, c, tok, A, f, note));
    }

    function _trData(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r) internal view returns (bytes memory) {
        return abi.encodeCall(ShieldedPool.transfer, (proof, [n0, n1], [c0, c1], r, note));
    }

    function _wdData(bytes32 n, address tok, address rcp, bytes32 r) internal view returns (bytes memory) {
        return abi.encodeCall(ShieldedPool.withdraw, (proof, n, tok, A, rcp, r));
    }

    function _is(bytes memory ret, bytes4 sel) internal pure returns (bool) {
        return ret.length == 4 && bytes4(ret) == sel;
    }

    // ---- D5: duplicate deposit from a reachable state (deposit C, then deposit C again) ----

    /// Stock: the second deposit reverts with exactly LeafAlreadyExists; tree size, leaf index, pool and
    /// funder balances are unchanged by it.
    function test_D5_stock_secondDepositReverts() public {
        ShieldedPool p = _pool(Kind.STOCK);
        MockERC20 t = _funded(p);
        (bool ok,) = _dep(p, address(t), C);
        assertTrue(ok, "first deposit");
        bytes memory ret;
        (ok, ret) = _dep(p, address(t), C);
        assertFalse(ok, "second deposit must revert");
        assertTrue(_is(ret, LEAF_EXISTS), "exact LeafAlreadyExists");
        assertEq(p.getCommitmentCount(), 1);
        assertEq(_leafIdx(p, C), 1);
        assertEq(t.balanceOf(address(p)), A);
        assertEq(t.balanceOf(F), A);
    }

    /// D5-P instrument, concrete: with the probe at the link address and the real library at 0xA1003, the
    /// duplicate deposit's revert data is LeafAlreadyExists ++ insert selector ++ slot 0 ++ C.
    function test_D5_stock_probeData() public {
        _etch("LeanIMT.sol:LeanIMT", address(0xA1003));
        vm.etch(address(0xA1001), address(new LibProbe()).code);
        ShieldedPool p = _pool(Kind.STOCK);
        MockERC20 t = _funded(p);
        (bool ok,) = _dep(p, address(t), C);
        assertTrue(ok, "first deposit through the probe");
        bytes memory ret;
        (ok, ret) = _dep(p, address(t), C);
        assertFalse(ok);
        bytes memory want = abi.encodePacked(
            LEAF_EXISTS, bytes4(keccak256("insert(LeanIMTData storage,uint256)")), uint256(0), uint256(C)
        );
        assertEq(keccak256(ret), keccak256(want));
    }

    /// M_SKIP (dupCore, dupAnyGuards): the duplicate deposit succeeds, pulls A tokens again and adds no
    /// leaf: the pool holds 2A against one note.
    function test_D5_SKIP_secondDepositSucceeds() public {
        ShieldedPool p = _pool(Kind.SKIP);
        MockERC20 t = _funded(p);
        (bool ok,) = _dep(p, address(t), C);
        assertTrue(ok, "first deposit");
        (ok,) = _dep(p, address(t), C);
        assertTrue(ok, "SKIP: duplicate deposit succeeds");
        assertEq(p.getCommitmentCount(), 1);
        assertEq(t.balanceOf(address(p)), 2 * A);
        assertEq(t.balanceOf(F), 0);
    }

    /// dupReverts and dupProbe on M_SKIP, M_DUP and M_ARG (tripwire token), with the library etched plain
    /// and behind the probe. C becomes a leaf by a first deposit (STOCK, SKIP, DUP) or as a transfer output
    /// (ARG), with the token benign; the token then switches to tripwire mode. Stock: exact
    /// LeafAlreadyExists (plain) or the 72-byte probe data (probe). Each mutant: the duplicate deposit
    /// gets past the tree and reaches the token, so the revert data is exactly Trip(3).
    function test_D5_mutants_tripTokenReached() public {
        bytes memory trip = abi.encodeWithSelector(Trip.selector, uint256(3));
        bytes memory probeData =
            abi.encodePacked(LEAF_EXISTS, bytes4(keccak256("insert(LeanIMTData storage,uint256)")), uint256(0), uint256(C));
        Kind[4] memory ks = [Kind.STOCK, Kind.SKIP, Kind.STOCK, Kind.ARG];
        for (uint256 probe = 0; probe < 2; probe++) {
            for (uint256 j = 0; j < 4; j++) {
                string memory lib = j == 2 ? "LeanIMT_M_DUP.sol:LeanIMT_M_DUP" : "LeanIMT.sol:LeanIMT";
                if (probe == 0) {
                    _etch(lib, address(0xA1001));
                } else {
                    _etch(lib, address(0xA1003));
                    vm.etch(address(0xA1001), address(new LibProbe()).code);
                }
                ShieldedPool p = _pool(ks[j]);
                SwitchToken tok = new SwitchToken();
                p.addSupportedToken(address(tok));
                bool ok;
                if (ks[j] == Kind.ARG) {
                    (ok,) = address(p).call(_trData(bytes32(uint256(1)), bytes32(uint256(2)), C, D, bytes32(0)));
                } else {
                    (ok,) = _dep(p, address(tok), C);
                }
                assertTrue(ok, "C enters the tree");
                tok.setMode(2);
                bytes memory ret;
                (ok, ret) = _dep(p, address(tok), C);
                assertFalse(ok);
                if (j == 0) {
                    bytes memory want = probe == 0 ? abi.encodePacked(LEAF_EXISTS) : probeData;
                    assertEq(keccak256(ret), keccak256(want), "stock data");
                } else {
                    assertEq(keccak256(ret), keccak256(trip), "mutant reaches the token");
                }
            }
        }
    }

    /// X1acq on M_NR_W and M_NR_D, from the empty pool, observing token: stock sees status 2 at its token
    /// call and 1 after return; the mutant sees 1 at the token call (no acquisition).
    function test_X1_acq_observation() public {
        Kind[2] memory ks = [Kind.NR_W, Kind.NR_D];
        for (uint256 j = 0; j < 2; j++) {
            for (uint256 i = 0; i < 2; i++) {
                ShieldedPool p = _pool(i == 0 ? Kind.STOCK : ks[j]);
                SwitchToken tok = new SwitchToken();
                tok.setMode(1);
                p.addSupportedToken(address(tok));
                bool ok;
                if (j == 0) (ok,) = address(p).call(_wdData(bytes32(uint256(6)), address(tok), RCP, bytes32(0)));
                else (ok,) = _dep(p, address(tok), C);
                assertTrue(ok);
                assertEq(tok.calls(), 1);
                assertEq(tok.lockAtCall(), i == 0 ? 2 : 1);
                assertEq(uint256(vm.load(address(p), LOCK)), 1);
            }
        }
    }

    /// M_DUP (library without the _has check): the duplicate deposit succeeds with the real PoseidonT3:
    /// size 2, depth 1, leaves[C] overwritten to 2.
    function test_D5_DUP_secondDepositSucceeds() public {
        _etch("LeanIMT_M_DUP.sol:LeanIMT_M_DUP", address(0xA1001));
        ShieldedPool p = _pool(Kind.STOCK);
        MockERC20 t = _funded(p);
        (bool ok,) = _dep(p, address(t), C);
        assertTrue(ok, "first deposit");
        (ok,) = _dep(p, address(t), C);
        assertTrue(ok, "DUP: duplicate deposit succeeds");
        assertEq(p.getCommitmentCount(), 2);
        assertEq(_leafIdx(p, C), 2);
        assertEq(t.balanceOf(address(p)), 2 * A);
    }

    /// M_ARG: C enters the tree as a transfer output (the mutant changes only the deposit line), then a
    /// deposit of C succeeds because the library receives the payload commitment instead of C.
    /// Stock on the same calls: the deposit reverts with exactly LeafAlreadyExists.
    function test_D5_ARG_depositOfExistingLeafSucceeds() public {
        for (uint256 i = 0; i < 2; i++) {
            ShieldedPool p = _pool(i == 0 ? Kind.STOCK : Kind.ARG);
            MockERC20 t = _funded(p);
            (bool ok,) = address(p).call(_trData(bytes32(uint256(1)), bytes32(uint256(2)), C, D, bytes32(0)));
            assertTrue(ok, "transfer from the empty tree");
            assertEq(_leafIdx(p, C), 1);
            bytes memory ret;
            (ok, ret) = _dep(p, address(t), C);
            if (i == 0) {
                assertFalse(ok);
                assertTrue(_is(ret, LEAF_EXISTS), "stock: exact LeafAlreadyExists");
            } else {
                assertTrue(ok, "ARG: deposit of an existing leaf succeeds");
                assertEq(p.getCommitmentCount(), 3);
                assertEq(_leafIdx(p, C), 1);
                assertEq(_leafIdx(p, p.payloadCommitment(note)), 3);
            }
        }
    }

    // ---- X1: status slot set to ENTERED directly (the Halmos X1 domain) ----

    /// X1core withdraw, cex arguments (n = 0, r = 0 = empty-tree root, rcp = 2^159, amount 2^127).
    /// Stock: exact guard revert. M_NR_W: success, the recipient is paid and the nullifier is spent.
    function test_X1_direct_withdraw() public {
        for (uint256 i = 0; i < 2; i++) {
            ShieldedPool p = _pool(i == 0 ? Kind.STOCK : Kind.NR_W);
            MockERC20 t = _funded(p);
            t.mint(address(p), A);
            vm.store(address(p), LOCK, bytes32(uint256(2)));
            (bool ok, bytes memory ret) = address(p).call(_wdData(bytes32(0), address(t), RCP, bytes32(0)));
            if (i == 0) {
                assertFalse(ok);
                assertTrue(_is(ret, GUARD), "stock: exact guard revert");
                assertFalse(p.nullifiers(bytes32(0)));
            } else {
                assertTrue(ok, "NR_W: withdraw succeeds while the lock is held");
                assertTrue(p.nullifiers(bytes32(0)));
                assertEq(t.balanceOf(RCP), 3 * A); // F == RCP in the cex: 2A minted to F plus A paid out
            }
        }
    }

    /// X1s_lockedWithdrawBenign on M_NR_W: by STATICCALL the mutant reaches its first write, the nullifier
    /// SSTORE, and halts with empty return data. Stock: exact guard revert.
    function test_X1_static_withdrawBenign() public {
        for (uint256 i = 0; i < 2; i++) {
            ShieldedPool p = _pool(i == 0 ? Kind.STOCK : Kind.NR_W);
            MockERC20 t = _funded(p);
            t.mint(address(p), A);
            vm.store(address(p), LOCK, bytes32(uint256(2)));
            (bool ok, bytes memory ret) = address(p).staticcall(_wdData(bytes32(0), address(t), RCP, bytes32(0)));
            assertFalse(ok);
            if (i == 0) assertTrue(_is(ret, GUARD), "stock: exact guard revert");
            else assertEq(ret.length, 0, "NR_W: static write halt");
        }
    }

    /// X1core deposit, cex arguments (c = 2^253, depth 0, empty tree). Stock: guard. M_NR_D: success.
    function test_X1_direct_deposit() public {
        for (uint256 i = 0; i < 2; i++) {
            ShieldedPool p = _pool(i == 0 ? Kind.STOCK : Kind.NR_D);
            MockERC20 t = _funded(p);
            vm.store(address(p), LOCK, bytes32(uint256(2)));
            (bool ok, bytes memory ret) = _dep(p, address(t), C);
            if (i == 0) {
                assertFalse(ok);
                assertTrue(_is(ret, GUARD), "stock: exact guard revert");
            } else {
                assertTrue(ok, "NR_D: deposit succeeds while the lock is held");
                assertEq(_leafIdx(p, C), 1);
            }
        }
    }

    /// X1core transfer, cex arguments (n0 = 0, n1 = 2^253, c0 = 2^253, c1 = 3*2^252, r = 0).
    function test_X1_direct_transfer() public {
        for (uint256 i = 0; i < 2; i++) {
            ShieldedPool p = _pool(i == 0 ? Kind.STOCK : Kind.NR_T);
            vm.store(address(p), LOCK, bytes32(uint256(2)));
            (bool ok, bytes memory ret) = address(p).call(_trData(bytes32(0), C, C, D, bytes32(0)));
            if (i == 0) {
                assertFalse(ok);
                assertTrue(_is(ret, GUARD), "stock: exact guard revert");
            } else {
                assertTrue(ok, "NR_T: transfer succeeds while the lock is held");
                assertEq(p.getCommitmentCount(), 2);
                assertTrue(p.nullifiers(bytes32(0)) && p.nullifiers(C));
            }
        }
    }

    /// Main X1/X1s checks on the NR mutants (tripwire mocks), cex arguments with zero addresses and
    /// equal nullifiers: the mutant passes the missing guard and stops at a later guard, so the revert
    /// data is not the guard selector. Feasible, reason-only failures (no success claimed here).
    function test_X1_tripCex_reasonOnly() public {
        bytes4 unsupported = ShieldedPool.UnsupportedToken.selector;
        bytes4 identical = ShieldedPool.IdenticalNullifiers.selector;
        Kind[3] memory ks = [Kind.NR_W, Kind.NR_D, Kind.NR_T];
        for (uint256 j = 0; j < 3; j++) {
            for (uint256 i = 0; i < 2; i++) {
                ShieldedPool p = _pool(i == 0 ? Kind.STOCK : ks[j]);
                vm.store(address(p), LOCK, bytes32(uint256(2)));
                bytes memory data = j == 0
                    ? _wdData(bytes32(0), address(0), address(0), bytes32(0))
                    : (j == 1 ? _depData(C, address(0), address(0)) : _trData(bytes32(0), bytes32(0), C, D, bytes32(0)));
                vm.prank(address(0));
                (bool ok, bytes memory ret) = address(p).call(data);
                (bool sok, bytes memory sret) = address(p).staticcall(data);
                assertFalse(ok);
                assertFalse(sok);
                if (i == 0) {
                    assertTrue(_is(ret, GUARD) && _is(sret, GUARD), "stock: guard");
                } else {
                    bytes4 want = j == 2 ? identical : unsupported;
                    assertTrue(_is(ret, want) && _is(sret, want), "mutant: later guard");
                }
            }
        }
    }

    // ---- X1: lock held by a real outer call (token callback), no direct status write ----

    /// Outer deposit (guarded in M_NR_W) calls the hook token; the hook re-enters withdraw.
    /// Stock: the inner withdraw reverts with exactly the guard selector. M_NR_W: it succeeds.
    function test_X1_callback_depositThenWithdraw() public {
        for (uint256 i = 0; i < 2; i++) {
            ShieldedPool p = _pool(i == 0 ? Kind.STOCK : Kind.NR_W);
            HookToken h = new HookToken();
            p.addSupportedToken(address(h));
            // After the outer deposit of C into the empty tree, the root is C (one leaf).
            h.arm(address(p), _wdData(bytes32(uint256(7)), address(h), RCP, C));
            (bool ok,) = _dep(p, address(h), C);
            assertTrue(ok, "outer deposit");
            assertTrue(h.tried());
            if (i == 0) {
                assertFalse(h.innerOk());
                assertTrue(_is(h.innerRet(), GUARD), "stock: inner guard revert");
            } else {
                assertTrue(h.innerOk(), "NR_W: inner withdraw succeeds during the outer deposit");
                assertTrue(p.nullifiers(bytes32(uint256(7))));
            }
        }
    }

    /// Outer withdraw (guarded in M_NR_D and M_NR_T) calls the hook token; the hook re-enters deposit
    /// (funder = the hook token) or transfer. Stock: guard revert. Mutant: the inner call succeeds.
    function test_X1_callback_withdrawThenDepositOrTransfer() public {
        Kind[2] memory ks = [Kind.NR_D, Kind.NR_T];
        for (uint256 j = 0; j < 2; j++) {
            for (uint256 i = 0; i < 2; i++) {
                ShieldedPool p = _pool(i == 0 ? Kind.STOCK : ks[j]);
                HookToken h = new HookToken();
                p.addSupportedToken(address(h));
                bytes memory inner = j == 0
                    ? _depData(D, address(h), address(h))
                    : _trData(bytes32(uint256(8)), bytes32(uint256(9)), D, E, bytes32(0));
                h.arm(address(p), inner);
                (bool ok,) = address(p).call(_wdData(bytes32(uint256(6)), address(h), RCP, bytes32(0)));
                assertTrue(ok, "outer withdraw");
                assertTrue(h.tried());
                if (i == 0) {
                    assertFalse(h.innerOk());
                    assertTrue(_is(h.innerRet(), GUARD), "stock: inner guard revert");
                } else {
                    assertTrue(h.innerOk(), "mutant: inner call succeeds during the outer withdraw");
                    assertEq(_leafIdx(p, D), 1);
                }
            }
        }
    }
}
