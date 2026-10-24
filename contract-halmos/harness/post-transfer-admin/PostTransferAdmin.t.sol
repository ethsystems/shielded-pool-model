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

contract PostTransferAdminTest is Test {
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

    struct Args {
        bytes proof;
        bytes payload;
        bytes32[2] n;
        bytes32[2] c;
        bytes32 root;
        address caller;
    }

    function _hook() internal {
        bytes memory nested = abi.encodeCall(ShieldedPool.withdraw, (
            bytes(""), svm.createBytes32("callbackNullifier"), address(tokA),
            svm.createUint256("callbackAmount"), svm.createAddress("callbackRecipient"),
            svm.createBytes32("callbackRoot")
        ));
        tokA.hook(address(pool), nested);
        tokB.hook(address(pool), nested);
    }

    function _invoke(Args memory a) internal returns (bool ok, bytes memory ret) {
        vm.prank(a.caller);
        return address(pool).call(abi.encodeCall(ShieldedPool.transfer, (a.proof, a.n, a.c, a.root, a.payload)));
    }

    function _twoPhase(Args memory a) internal returns (bool ok) {
        bool accepts = verifier.accepts();
        verifier.configure(1, accepts);
        uint256 snap = svm.snapshotStorage(address(pool));
        (bool first, bytes memory ret) = _invoke(a);
        assert(!first);
        assert(svm.snapshotStorage(address(pool)) == snap);
        verifier.record(ret);
        verifier.configure(2, accepts);
        (ok, ret) = _invoke(a);
        assert(ok || bytes4(ret) != PostVerifier.Diverged.selector);
    }

    function _modelInsert(Frame memory f, bytes32 leaf) internal pure returns (bytes32 node) {
        uint256 d = f.depth;
        if ((uint256(1) << d) < f.size + 1) d++;
        node = leaf;
        for (uint256 level = 0; level < d; level++) {
            if ((f.size >> level) & 1 == 1) node = bytes32(uint256(keccak256(abi.encode(f.side[level], node))) % P);
            else f.side[level] = node;
        }
        for (uint256 i = 0; i < 5; i++) {
            if (d == i) f.side[i] = node;
        }
        f.depth = d;
        f.size++;
    }

    function _transferPost(Args memory a, Frame memory f) internal view {
        uint256 size = f.size;
        _modelInsert(f, a.c[0]);
        bytes32 node = _modelInsert(f, a.c[1]);
        bytes32 expected;
        if (f.mappingProbe) {
            expected = f.mapped;
            if (f.base == 106 && (f.key == a.n[0] || f.key == a.n[1])) {
                expected = bytes32((uint256(expected) & ~uint256(255)) | 1);
            }
            if (f.base == 2) {
                for (uint256 i = 0; i < 5; i++) {
                    if (f.key == bytes32(i)) expected = f.side[i];
                }
            }
            if (f.base == 3) {
                if (f.key == a.c[0]) expected = bytes32(size + 1);
                if (f.key == a.c[1]) expected = bytes32(size + 2);
            }
            if (f.base == 105) {
                if (f.evicted != 0 && f.key == f.evicted) expected = bytes32(uint256(expected) & ~uint256(255));
                if (f.key == node) expected = bytes32((uint256(expected) & ~uint256(255)) | 1);
            }
            assert(vm.load(address(pool), mapSlot(f.key, f.base)) == expected);
        } else {
            expected = f.plain;
            if (f.slot == bytes32(0)) expected = bytes32(size + 2);
            if (f.slot == bytes32(uint256(1))) expected = bytes32(f.depth);
            if (f.slot == bytes32(4 + f.idx)) expected = node;
            if (f.slot == bytes32(uint256(104))) expected = bytes32((f.idx + 1) % 100);
            assert(vm.load(address(pool), f.slot) == expected);
        }
    }

    function _checkTransfer(uint256 field, bool witness, Args memory a) internal {
        _fresh(true);
        _hook();
        bool unspent0;
        bool unspent1;
        bool known;
        bytes32 leaf0;
        bytes32 leaf1;
        address preVerifier;
        Frame memory frame;
        if (field == 1) {
            unspent0 = !pool.nullifiers(a.n[0]);
            unspent1 = !pool.nullifiers(a.n[1]);
        }
        if (field == 2) {
            known = a.root == vm.load(address(pool), mapSlot(load(1), 2))
                || uint8(uint256(vm.load(address(pool), mapSlot(a.root, 105)))) != 0;
        }
        if (field == 3) {
            leaf0 = vm.load(address(pool), mapSlot(a.c[0], 3));
            leaf1 = vm.load(address(pool), mapSlot(a.c[1], 3));
        }
        if (field == 4) preVerifier = address(pool.verifier());
        if (field == 6) frame = _before(true);
        bool ok;
        if (field == 4) ok = _twoPhase(a);
        else (ok,) = _invoke(a);
        if (!ok) return;
        if (field == 0) assert(a.n[0] != a.n[1]);
        if (field == 1) assert(unspent0 && unspent1);
        if (field == 2) assert(known);
        if (field == 3) assert(leaf0 == 0 && leaf1 == 0 && a.c[0] != a.c[1]);
        if (field == 4) {
            assert(preVerifier == address(verifier));
            assert(verifier.hit() && verifier.accepts());
            assert(verifier.kind() == 1 && verifier.len() == 6);
            assert(verifier.rec(0) == a.n[0]);
            assert(verifier.rec(1) == a.n[1]);
            assert(verifier.rec(2) == a.c[0]);
            assert(verifier.rec(3) == a.c[1]);
            assert(verifier.rec(4) == a.root);
            assert(verifier.rec(5) == bytes32(uint256(keccak256(a.payload)) % P));
            for (uint256 i = 0; i < 6; i++) assert(uint256(verifier.rec(i)) < P);
        }
        if (field == 5) {
            assert(tokA.count() == 0 && tokB.count() == 0);
            assert(!tokA.nestedOK() && !tokB.nestedOK());
        }
        if (field == 6 && !tokA.nestedOK() && !tokB.nestedOK()) _transferPost(a, frame);
        if (witness) assert(false);
    }

    function _checkAdmin(uint256 field, bool witness, address x, address caller) internal {
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
        svm.enableSymbolicStorage(address(pool));
        vm.store(address(pool), bytes32(uint256(108)), bytes32(uint256(uint160(svm.createAddress("adminVerifier")))));
        vm.store(address(pool), bytes32(uint256(109)), bytes32(uint256(uint160(svm.createAddress("adminRegistry")))));
        vm.store(address(pool), bytes32(uint256(110)), bytes32(uint256(uint160(svm.createAddress("adminOwner")))));
        _hook();
        Frame memory f = _before(false);
        bytes memory data;
        if (field == 0) data = abi.encodeCall(ShieldedPool.addSupportedToken, (x));
        if (field == 1) data = abi.encodeCall(ShieldedPool.removeSupportedToken, (x));
        if (field == 2) data = abi.encodeCall(ShieldedPool.setAttestationRegistry, (x));
        if (field == 3) data = abi.encodeCall(ShieldedPool.transferOwnership, (x));
        vm.prank(caller);
        (bool ok,) = address(pool).call(data);
        if (!ok) return;
        if (f.mappingProbe) {
            bytes32 expected = f.mapped;
            if (field <= 1 && f.base == 107 && f.key == bytes32(uint256(uint160(x)))) {
                expected = bytes32((uint256(expected) & ~uint256(255)) | (field == 0 ? 1 : 0));
            }
            assert(vm.load(address(pool), mapSlot(f.key, f.base)) == expected);
        } else {
            bytes32 expected = f.plain;
            if ((field == 2 && f.slot == bytes32(uint256(109))) || (field == 3 && f.slot == bytes32(uint256(110)))) {
                expected = bytes32((uint256(expected) & ~uint256(type(uint160).max)) | uint256(uint160(x)));
            }
            assert(vm.load(address(pool), f.slot) == expected);
        }
        if (witness) assert(false);
    }
    function check_T_distinct(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(0, false, Args(proof, payload, n, c, root, caller));
    }
    function check_T_distinct_witness(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(0, true, Args(proof, payload, n, c, root, caller));
    }
    function check_T_unspent(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(1, false, Args(proof, payload, n, c, root, caller));
    }
    function check_T_unspent_witness(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(1, true, Args(proof, payload, n, c, root, caller));
    }
    function check_T_known_root(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(2, false, Args(proof, payload, n, c, root, caller));
    }
    function check_T_known_root_witness(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(2, true, Args(proof, payload, n, c, root, caller));
    }
    function check_T_fresh_outputs(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(3, false, Args(proof, payload, n, c, root, caller));
    }
    function check_T_fresh_outputs_witness(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(3, true, Args(proof, payload, n, c, root, caller));
    }
    function check_T_verified(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(4, false, Args(proof, payload, n, c, root, caller));
    }
    function check_T_verified_witness(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(4, true, Args(proof, payload, n, c, root, caller));
    }
    function check_T_no_effects(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(5, false, Args(proof, payload, n, c, root, caller));
    }
    function check_T_no_effects_witness(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(5, true, Args(proof, payload, n, c, root, caller));
    }
    function check_T_post(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(6, false, Args(proof, payload, n, c, root, caller));
    }
    function check_T_post_witness(bytes memory proof, bytes memory payload, bytes32[2] memory n,
        bytes32[2] memory c, bytes32 root, address caller) public {
        _checkTransfer(6, true, Args(proof, payload, n, c, root, caller));
    }
    function check_A_add(address x, address caller) public {
        _checkAdmin(0, false, x, caller);
    }
    function check_A_add_witness(address x, address caller) public {
        _checkAdmin(0, true, x, caller);
    }
    function check_A_remove(address x, address caller) public {
        _checkAdmin(1, false, x, caller);
    }
    function check_A_remove_witness(address x, address caller) public {
        _checkAdmin(1, true, x, caller);
    }
    function check_A_registry(address x, address caller) public {
        _checkAdmin(2, false, x, caller);
    }
    function check_A_registry_witness(address x, address caller) public {
        _checkAdmin(2, true, x, caller);
    }
    function check_A_owner(address x, address caller) public {
        _checkAdmin(3, false, x, caller);
    }
    function check_A_owner_witness(address x, address caller) public {
        _checkAdmin(3, true, x, caller);
    }
}
