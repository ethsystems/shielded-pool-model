// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/src/Test.sol";
interface SVM { function enableSymbolicStorage(address) external; }
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {LeanIMT} from "@zk-kit/packages/lean-imt/contracts/LeanIMT.sol";
import {ShieldedPool_M_LATE_MARK} from "./mutants/ShieldedPool_M_LATE_MARK.sol";
import {ShieldedPool_M_PAY_CALLER} from "./mutants/ShieldedPool_M_PAY_CALLER.sol";

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

    /// Deposit and transfer: stop at the verifier, so no tree insertion runs.
    function verifyDeposit(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        if (!_same(pi)) revert Diverged();
        revert Matched();
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata pi) external view returns (bool) {
        if (!_same(pi)) revert Diverged();
        revert Matched();
    }

    /// Withdraw: the answer is the symbolic `accept`, given only for the expected inputs.
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
/// for the watched key AT THE TIME OF THE CALL. Any other selector is counted in `others`.
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

abstract contract WithdrawCallerBase is Test {
    SVM internal constant svm = SVM(address(uint160(uint256(keccak256("svm cheat code")))));
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
        svm.enableSymbolicStorage(address(pool));
        vm.store(address(pool), bytes32(uint256(108)), bytes32(uint256(uint160(address(verifier)))));
        vm.store(address(pool), bytes32(uint256(109)), bytes32(uint256(uint160(address(registry)))));
        vm.store(address(pool), REENTRANCY_SLOT, bytes32(uint256(1)));
        svm.enableSymbolicStorage(address(registry));
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

contract WithdrawCallerTest is WithdrawCallerBase {
    error VerifierInputsDiverged();
    error VerifierBypassed();
    error NotMarkedAtPayout();
    error NotMarkedAfter();
    error TokenCallCount();
    error PayoutArgs();
    error WrongToken();

    function _wd(bytes calldata proof, bytes32 n, address token, uint256 a, address rcp, bytes32 r, bool acc)
        internal
        returns (bool ok, bytes4 sel)
    {
        verifier.setExp(
            acc, 5, [n, bytes32(uint256(uint160(token))), bytes32(a), bytes32(uint256(uint160(rcp))), r, bytes32(0)]
        );
        RecToken(TOKEN).arm(address(pool), n);
        other.arm(address(pool), n);
        vm.prank(caller);
        try pool.withdraw(proof, n, token, a, rcp, r) {
            ok = true;
        } catch {
            sel = _sel();
        }
    }

    address internal caller;

    /// Marking before payout and the payout call, every path, for the token argument `token`. Any call: the verifier never saw inputs
    /// other than [n, token, a, rcp, r] (else Diverged surfaces). A successful call: the verifier said
    /// yes (acc); exactly one retained recorded call reached the two tokens, and it went to `token`;
    /// the nullifier was already marked when that token was called and is marked after; the call
    /// was transfer(rcp, a) from the pool; neither token recorded any other call.
    function _body(bytes calldata proof, bytes32 n, address token, uint256 a, address rcp, bytes32 r, bool acc)
        internal
    {
        _fresh();
        (bool ok, bytes4 sel) = _wd(proof, n, token, a, rcp, r, acc);
        if (!ok) {
            assert(!(sel == CmpVerifier.Diverged.selector)); // VerifierInputsDiverged
            return;
        }
        assert(!(!acc)); // VerifierBypassed
        uint256 cA = _get(TOKEN, RecToken(TOKEN).calls.selector);
        uint256 cB = _get(address(other), RecToken(TOKEN).calls.selector);
        assert(!(cA + cB != 1)); // TokenCallCount
        address moved = cA == 1 ? TOKEN : address(other);
        assert(!(moved != token)); // WrongToken
        assert(!(_get(moved, RecToken(TOKEN).spentSeen.selector) != 1)); // NotMarkedAtPayout
        assert(!(_get1(address(pool), pool.nullifiers.selector, n) != 1)); // NotMarkedAfter
        assert(!(_get(TOKEN, RecToken(TOKEN).others.selector) != 0)); // TokenCallCount
        assert(!(_get(address(other), RecToken(TOKEN).others.selector) != 0)); // TokenCallCount
        assert(!(_get(moved, RecToken(TOKEN).to.selector) != uint256(uint160(rcp)))); // PayoutArgs
        assert(!(_get(moved, RecToken(TOKEN).amt.selector) != a)); // PayoutArgs
        assert(!(_get(moved, RecToken(TOKEN).from.selector) != uint256(uint160(address(pool))))); // PayoutArgs
    }

    function check_withdraw(bytes32 n, address token, uint256 a, address rcp, bytes32 r,
        bool acc, address who, bytes calldata proof) public {
        vm.assume(token != address(vm));
        vm.assume(uint160(token) > 0x11);
        caller = who;
        _body(proof, n, token, a, rcp, r, acc);
    }

    function check_witnessHigh(bytes32 n, uint256 a, address rcp, bytes32 r,
        address who, bytes calldata proof) public {
        caller = who;
        _fresh();
        (bool ok,) = _wd(proof, n, TOKEN, a, rcp, r, true);
        assert(!ok);
    }

    function check_witnessLow(bytes32 n, uint256 a, address rcp, bytes32 r,
        address who, bytes calldata proof) public {
        caller = who;
        _fresh();
        (bool ok,) = _wd(proof, n, address(other), a, rcp, r, true);
        assert(!ok);
    }
}

// Must-fail siblings: the same bodies against a pool with one change (mutants/caller/).
contract WithdrawCallerMut_LATE_MARKTest is WithdrawCallerTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_LATE_MARK(v, r));
    }
}





contract WithdrawCallerMut_PAY_CALLERTest is WithdrawCallerTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_CALLER(v, r));
    }
}




