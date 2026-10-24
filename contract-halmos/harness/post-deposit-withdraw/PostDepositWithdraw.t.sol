// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
import {Test} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";

interface SVM {
    function createBytes32(string calldata) external returns (bytes32);
    function createUint256(string calldata) external returns (uint256);
    function createAddress(string calldata) external returns (address);
    function createBool(string calldata) external returns (bool);
    function createCalldata(string calldata, bool) external returns (bytes memory);
    function enableSymbolicStorage(address) external;
    function snapshotStorage(address) external returns (uint256);
}

contract PostRegistry {
    bytes32 public attestationRoot;

    function set(bytes32 r) external {
        attestationRoot = r;
    }
}

contract PostHash {
    function hash(uint256[2] memory x) public pure returns (uint256) {
        return uint256(keccak256(abi.encode(x[0], x[1])))
            % 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    }
}

// Two-phase recorder (as in the owner-payout suite): revert through STATICCALL, retain the record in storage between calls.
contract PostVerifier is IVerifier {
    error Saw(
        uint256 kind, uint256 len, bytes32 a, bytes32 b, bytes32 c, bytes32 d, bytes32 e, bytes32 f, bytes32 proofHash
    );
    error Diverged();
    uint256 public mode;
    bool public accepts;
    bool public hit;
    uint256 public kind;
    uint256 public len;
    bytes32[6] public rec;
    bytes32 public proofHash;

    function configure(uint256 m, bool a) external {
        mode = m;
        accepts = a;
    }

    function record(bytes memory ret) external {
        if (ret.length != 292 || bytes4(ret) != Saw.selector) return;
        hit = true;
        uint256 k;
        uint256 l;
        bytes32 ph;
        assembly {
            k := mload(add(ret, 36))
            l := mload(add(ret, 68))
            ph := mload(add(ret, 292))
        }
        kind = k;
        len = l;
        proofHash = ph;
        for (uint256 i = 0; i < 6; i++) {
            bytes32 w;
            assembly { w := mload(add(add(ret, 100), mul(i, 32))) }
            rec[i] = w;
        }
    }

    function _verify(uint256 k, bytes calldata proof, bytes32[] calldata pi) internal view returns (bool) {
        if (mode == 1) {
            if (pi.length < 5) revert Saw(k, pi.length, 0, 0, 0, 0, 0, 0, keccak256(proof));
            revert Saw(
                k, pi.length, pi[0], pi[1], pi[2], pi[3], pi[4], pi.length > 5 ? pi[5] : bytes32(0), keccak256(proof)
            );
        }
        if (mode == 2) {
            if (!hit || kind != k || len != pi.length || proofHash != keccak256(proof)) revert Diverged();
            for (uint256 i = 0; i < pi.length; i++) {
                if (i >= 6 || pi[i] != rec[i]) revert Diverged();
            }
        }
        return accepts;
    }

    function verifyDeposit(bytes calldata p, bytes32[] calldata x) external view returns (bool) {
        return _verify(0, p, x);
    }

    function verifyTransfer(bytes calldata p, bytes32[] calldata x) external view returns (bool) {
        return _verify(1, p, x);
    }

    function verifyWithdraw(bytes calldata p, bytes32[] calldata x) external view returns (bool) {
        return _verify(2, p, x);
    }
}

contract PostToken {
    uint256 public count;
    uint256 public kind;
    address public sender;
    address public src;
    address public dst;
    uint256 public amount;
    address public pool;
    bytes public callback;
    bool public tried;
    bool public nestedOK;

    function hook(address p, bytes memory c) external {
        pool = p;
        callback = c;
    }

    function _call(uint256 k, address f, address t, uint256 a) internal {
        count++;
        kind = k;
        sender = msg.sender;
        src = f;
        dst = t;
        amount = a;
        if (!tried && callback.length != 0) {
            tried = true;
            (nestedOK,) = pool.call(callback);
        }
    }

    function transfer(address to, uint256 a) external returns (bool) {
        _call(2, address(0), to, a);
        return true;
    }

    function transferFrom(address from, address to, uint256 a) external returns (bool) {
        _call(0, from, to, a);
        return true;
    }

    fallback() external {
        count++;
        kind = 99;
    }
}

contract PostDepositWithdrawTest is Test {
    SVM constant svm = SVM(address(uint160(uint256(keccak256("svm cheat code")))));
    uint256 constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    address constant HIGH_TOKEN = address(uint160((uint256(0xF) << 156) + 0xB));
    ShieldedPool pool;
    PostVerifier verifier;
    PostRegistry registry;
    PostToken tokA;
    PostToken tokB;

    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    function setUp() public {
        bytes memory init = vm.getCode("LeanIMT.sol:LeanIMT");
        address lib;
        assembly { lib := create(0, add(init, 32), mload(init)) }
        require(lib != address(0));
        vm.etch(address(0xA1001), lib.code);
        vm.etch(address(0xA1002), address(new PostHash()).code);
        verifier = new PostVerifier();
        registry = new PostRegistry();
        tokA = new PostToken();
        vm.etch(HIGH_TOKEN, type(PostToken).runtimeCode);
        tokB = PostToken(HIGH_TOKEN);
    }

    function mapSlot(bytes32 k, uint256 base) internal pure returns (bytes32) {
        return keccak256(abi.encode(k, base));
    }

    function load(uint256 s) internal view returns (bytes32) {
        return vm.load(address(pool), bytes32(s));
    }

    function _fresh(bool dep) internal {
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
        svm.enableSymbolicStorage(address(pool));
        uint256 idx = svm.createUint256("ringIndex");
        vm.assume(idx < 100);
        vm.store(address(pool), bytes32(uint256(104)), bytes32(idx));
        registry.set(svm.createBytes32("attestationRoot"));
        verifier.configure(0, svm.createBool("verifierAccepts"));
        if (dep) {
            uint256 d = svm.createUint256("depth");
            vm.assume(d < 4);
            vm.store(address(pool), bytes32(uint256(1)), bytes32(d));
            vm.assume(uint256(load(0)) <= uint256(1) << d);
        }
    }

    struct Args {
        bytes proof;
        bytes payload;
        bytes32 n;
        address t;
        uint256 a;
        address who;
        bytes32 root;
        address caller;
    }

    function _data(bool dep, Args memory a) internal pure returns (bytes memory) {
        if (dep) return abi.encodeCall(ShieldedPool.deposit, (a.proof, a.n, a.t, a.a, a.who, a.payload));
        return abi.encodeCall(ShieldedPool.withdraw, (a.proof, a.n, a.t, a.a, a.who, a.root));
    }

    function _invoke(Args memory a, bytes memory data) internal returns (bool ok, bytes memory ret) {
        vm.prank(a.caller);
        return address(pool).call(data);
    }

    function _twoPhase(Args memory a, bytes memory data) internal returns (bool ok) {
        bool accepts = verifier.accepts();
        verifier.configure(1, accepts);
        uint256 snap = svm.snapshotStorage(address(pool));
        (bool first, bytes memory ret) = _invoke(a, data);
        assert(!first);
        assert(svm.snapshotStorage(address(pool)) == snap);
        verifier.record(ret);
        verifier.configure(2, accepts);
        (ok, ret) = _invoke(a, data);
        assert(ok || bytes4(ret) != PostVerifier.Diverged.selector);
    }

    struct Frame {
        bool mappingProbe;
        bytes32 slot;
        bytes32 plain;
        bytes32 key;
        uint256 base;
        bytes32 mapped;
        uint256 size;
        uint256 depth;
        uint256 idx;
        bytes32 evicted;
        bytes32[5] side;
    }

    function _before(bool dep) internal returns (Frame memory f) {
        f.mappingProbe = svm.createBool("mappingProbe");
        if (f.mappingProbe) {
            f.key = svm.createBytes32("frameKey");
            f.base = svm.createUint256("frameBase");
            f.mapped = vm.load(address(pool), mapSlot(f.key, f.base));
        } else {
            f.slot = svm.createBytes32("frameSlot");
            f.plain = vm.load(address(pool), f.slot);
        }
        if (dep) {
            f.size = uint256(load(0));
            f.depth = uint256(load(1));
            f.idx = uint256(load(104));
            f.evicted = load(4 + f.idx);
            for (uint256 i = 0; i < 5; i++) {
                f.side[i] = vm.load(address(pool), mapSlot(bytes32(i), 2));
            }
        }
    }

    function _post(bool dep, bytes32 n, Frame memory f) internal view {
        bytes32 plain = f.plain;
        bytes32 mapped = f.mapped;
        if (!dep) {
            if (f.mappingProbe && f.base == 106 && f.key == n) mapped = bytes32((uint256(mapped) & ~uint256(255)) | 1);
        } else {
            uint256 d = f.depth;
            if ((uint256(1) << d) < f.size + 1) d++;
            bytes32 node = n;
            for (uint256 level = 0; level < d; level++) {
                if ((f.size >> level) & 1 == 1) node = bytes32(uint256(keccak256(abi.encode(f.side[level], node))) % P);
                else f.side[level] = node;
            }
            for (uint256 i = 0; i < 5; i++) {
                if (d == i) f.side[i] = node;
            }
            if (!f.mappingProbe) {
                if (f.slot == bytes32(0)) plain = bytes32(f.size + 1);
                if (f.slot == bytes32(uint256(1))) plain = bytes32(d);
                if (f.slot == bytes32(4 + f.idx)) plain = node;
                if (f.slot == bytes32(uint256(104))) plain = bytes32((f.idx + 1) % 100);
            } else {
                if (f.base == 2) {
                    for (uint256 i = 0; i < 5; i++) {
                        if (f.key == bytes32(i)) mapped = f.side[i];
                    }
                }
                if (f.base == 3 && f.key == n) mapped = bytes32(f.size + 1);
                if (f.base == 105) {
                    if (f.evicted != 0 && f.key == f.evicted) mapped = bytes32(uint256(mapped) & ~uint256(255));
                    if (f.key == node) mapped = bytes32((uint256(mapped) & ~uint256(255)) | 1);
                }
            }
        }
        if (f.mappingProbe) assert(vm.load(address(pool), mapSlot(f.key, f.base)) == mapped);
        else assert(vm.load(address(pool), f.slot) == plain);
    }

    // Field ids: 0 amount, 1 supported/unspent, 2 fresh_leaf/known_root, 3 verified, 4 guarded, 5 token_calls, 6 post.
    function _check(bool dep, uint256 field, Args memory a) internal {
        _fresh(dep);
        // Token environment: two recording, no-op ERC20s. Full-width address/call words are never balances.
        vm.assume(a.t == address(tokA) || a.t == address(tokB));
        bool preBool;
        bytes32 preWord;
        Frame memory frame;
        if (field == 1) preBool = dep ? pool.supportedTokens(a.t) : pool.nullifiers(a.n);
        if (field == 2) {
            if (dep) {
                preWord = vm.load(address(pool), mapSlot(a.n, 3));
            } else {
                preBool =
                (a.root == vm.load(address(pool), mapSlot(load(1), 2))
                        || uint8(uint256(vm.load(address(pool), mapSlot(a.root, 105)))) != 0);
            }
        }
        if (field == 4) {
            bytes memory nested = svm.createCalldata("ShieldedPool", false);
            bytes4 sel = bytes4(nested);
            vm.assume(
                sel == ShieldedPool.deposit.selector || sel == ShieldedPool.transfer.selector
                    || sel == ShieldedPool.withdraw.selector
            );
            tokA.hook(address(pool), nested);
            tokB.hook(address(pool), nested);
        }
        if (field == 6) frame = _before(dep);
        bytes memory data = _data(dep, a);
        bool ok;
        if (field == 3) ok = _twoPhase(a, data);
        else (ok,) = _invoke(a, data);
        if (!ok) return;
        if (field == 0) {
            assert(a.a != 0);
        } else if (field == 1) {
            assert(dep ? preBool : !preBool);
        } else if (field == 2) {
            assert(dep ? preWord == 0 : preBool);
        } else if (field == 3) {
            assert(verifier.hit() && verifier.accepts());
            assert(address(pool.verifier()) == address(verifier));
            assert(verifier.kind() == (dep ? 0 : 2));
            assert(verifier.len() == (dep ? 6 : 5));
            assert(verifier.rec(0) == a.n);
            assert(verifier.rec(1) == bytes32(uint256(uint160(a.t))));
            assert(verifier.rec(2) == bytes32(a.a));
            assert(verifier.rec(3) == bytes32(uint256(uint160(a.who))));
            assert(verifier.rec(4) == (dep ? registry.attestationRoot() : a.root));
            if (dep) assert(verifier.rec(5) == bytes32(uint256(keccak256(a.payload)) % P));
            for (uint256 i = 0; i < (dep ? 6 : 5); i++) {
                assert(uint256(verifier.rec(i)) < P);
            }
        } else if (field == 4) {
            assert(!tokA.nestedOK());
            assert(!tokB.nestedOK());
        } else if (field == 5) {
            assert(tokA.count() + tokB.count() == 1);
            PostToken t = tokA.count() == 1 ? tokA : tokB;
            assert(address(t) == a.t);
            assert(t.kind() == (dep ? 0 : 2));
            assert(t.sender() == address(pool));
            assert(t.dst() == (dep ? address(pool) : a.who));
            assert(t.amount() == a.a);
            if (dep) assert(t.src() == a.who);
        } else if (field == 6) {
            _post(dep, a.n, frame);
        } else if (field == 7) {
            assert(false); // Non-vacuity witness: must fail on a successful call.
        }
    }

    function check_W_amount_ne_zero(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 0, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_W_unspent(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 1, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_W_known_root(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 2, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_W_verified(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 3, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_W_guarded(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 4, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_W_token_calls(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 5, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_W_post(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 6, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_W_witness(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(false, 7, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_amount_ne_zero(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 0, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_supported(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 1, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_fresh_leaf(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 2, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_verified(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 3, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_guarded(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 4, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_token_calls(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 5, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_post(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 6, Args(proof, payload, n, t, a, who, root, caller));
    }

    function check_D_witness(
        bytes memory proof,
        bytes memory payload,
        bytes32 n,
        address t,
        uint256 a,
        address who,
        bytes32 root,
        address caller
    ) public {
        _check(true, 7, Args(proof, payload, n, t, a, who, root, caller));
    }
}
