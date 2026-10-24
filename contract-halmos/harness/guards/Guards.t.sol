// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The pre-verify guards of ShieldedPool (ethsystems/pocs a04b8b3), checked by Halmos for every
// input. One check per guard: if the guard's condition fails, the call reverts, the verifier is not
// reached, and no storage, balance or code of any account changes. Mutant controls at the end.

import {Test} from "forge-std/src/Test.sol";
import {ShieldedPool} from "../../src/ShieldedPool.sol";
import {IVerifier} from "../../src/interfaces/IVerifier.sol";
import {MockERC20} from "../../src/mocks/MockERC20.sol";
import {ShieldedPool_M_DEP_TOKEN} from "./mutants/ShieldedPool_M_DEP_TOKEN.sol";
import {ShieldedPool_M_DEP_AMOUNT_ZERO} from "./mutants/ShieldedPool_M_DEP_AMOUNT_ZERO.sol";
import {ShieldedPool_M_DEP_AMOUNT_MAX} from "./mutants/ShieldedPool_M_DEP_AMOUNT_MAX.sol";
import {ShieldedPool_M_DEP_FUNDER_ZERO} from "./mutants/ShieldedPool_M_DEP_FUNDER_ZERO.sol";
import {ShieldedPool_M_DEP_FUNDER_CALLER} from "./mutants/ShieldedPool_M_DEP_FUNDER_CALLER.sol";
import {ShieldedPool_M_DEP_CANONICAL} from "./mutants/ShieldedPool_M_DEP_CANONICAL.sol";
import {ShieldedPool_M_TR_DISTINCT} from "./mutants/ShieldedPool_M_TR_DISTINCT.sol";
import {ShieldedPool_M_TR_SPENT0} from "./mutants/ShieldedPool_M_TR_SPENT0.sol";
import {ShieldedPool_M_TR_SPENT1} from "./mutants/ShieldedPool_M_TR_SPENT1.sol";
import {ShieldedPool_M_TR_ROOT} from "./mutants/ShieldedPool_M_TR_ROOT.sol";
import {ShieldedPool_M_TR_CANONICAL} from "./mutants/ShieldedPool_M_TR_CANONICAL.sol";
import {ShieldedPool_M_WD_TOKEN} from "./mutants/ShieldedPool_M_WD_TOKEN.sol";
import {ShieldedPool_M_WD_AMOUNT_ZERO} from "./mutants/ShieldedPool_M_WD_AMOUNT_ZERO.sol";
import {ShieldedPool_M_WD_AMOUNT_MAX} from "./mutants/ShieldedPool_M_WD_AMOUNT_MAX.sol";
import {ShieldedPool_M_WD_RECIPIENT_ZERO} from "./mutants/ShieldedPool_M_WD_RECIPIENT_ZERO.sol";
import {ShieldedPool_M_WD_SPENT} from "./mutants/ShieldedPool_M_WD_SPENT.sol";
import {ShieldedPool_M_WD_ROOT} from "./mutants/ShieldedPool_M_WD_ROOT.sol";
import {ShieldedPool_M_WD_CANONICAL} from "./mutants/ShieldedPool_M_WD_CANONICAL.sol";

interface SVM {
    function createBytes32(string calldata name) external returns (bytes32);
    function createAddress(string calldata name) external returns (address);
    function createUint256(string calldata name) external returns (uint256);
    function enableSymbolicStorage(address) external;
    function snapshotStorage(address) external returns (uint256);
    function snapshotState() external returns (bytes32);
}

/// Verifier mock. ShieldedPool calls verify* through IVerifier's `view` functions, so the call is a
/// STATICCALL and the mock cannot write a storage record (or emit a log). The record travels in revert
/// data instead. TRIP mode: every verify* call reverts with VerifierReached(msg.sig), and the pool's
/// high-level call re-throws that data unchanged. ACCEPT mode: every verify* call returns true.
contract RecordingVerifier is IVerifier {
    error VerifierReached(bytes4 which);

    bool public trip;

    function setTrip(bool t) external {
        trip = t;
    }

    function _answer() internal view returns (bool) {
        if (trip) revert VerifierReached(msg.sig);
        return true;
    }

    function verifyDeposit(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _answer();
    }

    function verifyTransfer(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _answer();
    }

    function verifyWithdraw(bytes calldata, bytes32[] calldata) external view returns (bool) {
        return _answer();
    }
}

/// Attestation registry stub. Its root is set inside each check to a fresh symbolic value, so the
/// deposit public input 4 is symbolic too.
contract SymRegistry {
    bytes32 public root;

    function set(bytes32 r) external {
        root = r;
    }

    function attestationRoot() external view returns (bytes32) {
        return root;
    }

    function attestationLeaves(bytes32) external pure returns (bool) {
        return false;
    }
}

contract GuardsTest is Test {
    SVM internal constant svm = SVM(address(uint160(uint256(keccak256("svm cheat code")))));
    uint256 internal constant P = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    uint256 internal constant MAX_AMOUNT = 1 << 128;
    bytes32 internal constant REENTRANCY_SLOT = 0x9b779b17422d0df92223018b32b4d1fa46e071723d6817e2486d003becc55f00;

    ShieldedPool internal pool;
    RecordingVerifier internal verifier;
    SymRegistry internal registry;
    MockERC20 internal token;
    /// Set only by the check_core_* wrappers: they drop the revert-reason assertion and keep the
    /// rejection property (revert, verifier not reached, no state change).
    bool internal noAttr;

    function _etchLib(string memory artifact, address at) internal {
        bytes memory init = vm.getCode(artifact);
        address tmp;
        assembly {
            tmp := create(0, add(init, 0x20), mload(init))
        }
        require(tmp != address(0), "lib deploy");
        vm.etch(at, tmp.code);
    }

    function setUp() public {
        // Linked library addresses from foundry.toml. The real LeanIMT and PoseidonT3 code.
        _etchLib("LeanIMT.sol:LeanIMT", address(0xA1001));
        _etchLib("PoseidonT3.sol:PoseidonT3", address(0xA1002));
        verifier = new RecordingVerifier();
        registry = new SymRegistry();
        token = new MockERC20("T", "T", 18);
    }

    /// Mutant test contracts override this to deploy a copy with one guard removed.
    function _deploy(address v, address r) internal virtual returns (address) {
        return address(new ShieldedPool(v, r));
    }

    /// Fresh pool deployed inside the check, then symbolic storage (Halmos keeps the slots written
    /// in setUp concrete). The constructor writes verifier, attestationRegistry, owner and the
    /// reentrancy status; those stay concrete. Every other pool slot is symbolic when first read:
    /// nullifiers, supportedTokens, validRoots, the tree (size, depth, sideNodes, leaves), the root buffer.
    function _fresh() internal {
        pool = ShieldedPool(_deploy(address(verifier), address(registry)));
        svm.enableSymbolicStorage(address(pool));
        registry.set(svm.createBytes32("attRoot"));
    }

    // ---- calldata builders ----

    function _dep(bytes memory proof, bytes32 c, address t, uint256 a, address f, bytes memory note)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(ShieldedPool.deposit.selector, proof, c, t, a, f, note);
    }

    function _tr(bytes memory proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note)
        internal
        pure
        returns (bytes memory)
    {
        bytes32[2] memory ns = [n0, n1];
        bytes32[2] memory cs = [c0, c1];
        return abi.encodeWithSelector(ShieldedPool.transfer.selector, proof, ns, cs, r, note);
    }

    function _wd(bytes memory proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(ShieldedPool.withdraw.selector, proof, n, t, a, rcp, r);
    }

    // ---- the rejection property ----

    /// One call of `data` from `caller` with the verifier in the given mode: it reverts, the verifier
    /// marker is absent, and the pool storage, the token storage and the whole state (storage, balance
    /// and code of every account) are unchanged. Snapshots are taken right before and right after the call.
    function _rejectOnce(address caller, bytes memory data, bool trip) internal returns (bytes memory ret) {
        verifier.setTrip(trip);
        bytes32 g0 = svm.snapshotState();
        uint256 p0 = svm.snapshotStorage(address(pool));
        uint256 k0 = svm.snapshotStorage(address(token));
        bool ok;
        vm.prank(caller);
        (ok, ret) = address(pool).call(data);
        assert(svm.snapshotState() == g0);
        assert(svm.snapshotStorage(address(pool)) == p0);
        assert(svm.snapshotStorage(address(token)) == k0);
        assert(!ok);
        assert(bytes4(ret) != RecordingVerifier.VerifierReached.selector);
    }

    /// Rejected with the verifier in TRIP mode (so it is never reached) and in ACCEPT mode (so the
    /// rejection holds although the verifier would accept any proof), with the same revert data.
    function _mustReject(address caller, bytes memory data) internal returns (bytes4) {
        bytes memory r1 = _rejectOnce(caller, data, true);
        bytes memory r2 = _rejectOnce(caller, data, false);
        assert(keccak256(r1) == keccak256(r2));
        return bytes4(r1);
    }

    function _known(bytes32 r) internal view returns (bool) {
        return r == pool.commitmentRoot() || pool.validRoots(r);
    }

    // ---- deposit, ShieldedPool.sol:145-149 and 163 ----

    function _depEarlier(uint256 k, address t, uint256 a, address f, address caller) internal view returns (bool) {
        if (k > 1 && !pool.supportedTokens(t)) return true;
        if (k > 2 && a == 0) return true;
        if (k > 3 && a >= MAX_AMOUNT) return true;
        if (k > 4 && f == address(0)) return true;
        if (k > 5 && caller != f) return true;
        return false;
    }

    function _depNonCanon(bytes32 c, address t, uint256 a, address f, bytes memory note) internal view returns (bool) {
        return uint256(c) >= P || uint256(uint160(t)) >= P || a >= P || uint256(uint160(f)) >= P
            || uint256(registry.root()) >= P || uint256(keccak256(note)) % P >= P;
    }

    function check_deposit_unsupportedToken(
        bytes memory proof,
        bytes32 c,
        address t,
        uint256 a,
        address f,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(!pool.supportedTokens(t));
        bytes4 sel = _mustReject(caller, _dep(proof, c, t, a, f, note));
        assert(noAttr || sel == ShieldedPool.UnsupportedToken.selector);
    }

    function check_deposit_zeroAmount(bytes memory proof, bytes32 c, address t, address f, bytes memory note, address caller)
        public
    {
        _fresh();
        bytes4 sel = _mustReject(caller, _dep(proof, c, t, 0, f, note));
        assert(noAttr || _depEarlier(2, t, 0, f, caller) || sel == ShieldedPool.ZeroAmount.selector);
    }

    function check_deposit_amountTooLarge(
        bytes memory proof,
        bytes32 c,
        address t,
        uint256 a,
        address f,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(a >= MAX_AMOUNT);
        bytes4 sel = _mustReject(caller, _dep(proof, c, t, a, f, note));
        assert(noAttr || _depEarlier(3, t, a, f, caller) || sel == ShieldedPool.AmountTooLarge.selector);
    }

    function check_deposit_zeroFundingAddress(
        bytes memory proof,
        bytes32 c,
        address t,
        uint256 a,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        bytes4 sel = _mustReject(caller, _dep(proof, c, t, a, address(0), note));
        assert(noAttr || _depEarlier(4, t, a, address(0), caller) || sel == ShieldedPool.ZeroAddress.selector);
    }

    function check_deposit_senderNotFundingAddress(
        bytes memory proof,
        bytes32 c,
        address t,
        uint256 a,
        address f,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(caller != f);
        bytes4 sel = _mustReject(caller, _dep(proof, c, t, a, f, note));
        assert(noAttr || _depEarlier(5, t, a, f, caller) || sel == ShieldedPool.FundingAddressMismatch.selector);
    }

    function check_deposit_nonCanonicalInput(
        bytes memory proof,
        bytes32 c,
        address t,
        uint256 a,
        address f,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(_depNonCanon(c, t, a, f, note));
        bytes4 sel = _mustReject(caller, _dep(proof, c, t, a, f, note));
        assert(noAttr || _depEarlier(6, t, a, f, caller) || sel == ShieldedPool.PublicInputGeFieldModulus.selector);
    }

    // ---- transfer, ShieldedPool.sol:195-204 and 218 ----

    function _trEarlier(uint256 k, bytes32 n0, bytes32 n1, bytes32 r) internal view returns (bool) {
        if (k > 1 && n0 == n1) return true;
        if (k > 2 && pool.nullifiers(n0)) return true;
        if (k > 3 && pool.nullifiers(n1)) return true;
        if (k > 4 && !_known(r)) return true;
        return false;
    }

    function _trNonCanon(bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note)
        internal
        pure
        returns (bool)
    {
        return uint256(n0) >= P || uint256(n1) >= P || uint256(c0) >= P || uint256(c1) >= P || uint256(r) >= P
            || uint256(keccak256(note)) % P >= P;
    }

    function check_transfer_identicalNullifiers(
        bytes memory proof,
        bytes32 n,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        bytes4 sel = _mustReject(caller, _tr(proof, n, n, c0, c1, r, note));
        assert(noAttr || sel == ShieldedPool.IdenticalNullifiers.selector);
    }

    function check_transfer_firstNullifierSpent(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(pool.nullifiers(n0));
        bytes4 sel = _mustReject(caller, _tr(proof, n0, n1, c0, c1, r, note));
        assert(noAttr || _trEarlier(2, n0, n1, r) || sel == ShieldedPool.NullifierAlreadySpent.selector);
    }

    function check_transfer_secondNullifierSpent(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(pool.nullifiers(n1));
        bytes4 sel = _mustReject(caller, _tr(proof, n0, n1, c0, c1, r, note));
        assert(noAttr || _trEarlier(3, n0, n1, r) || sel == ShieldedPool.NullifierAlreadySpent.selector);
    }

    function check_transfer_unknownRoot(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(r != pool.commitmentRoot() && !pool.validRoots(r));
        bytes4 sel = _mustReject(caller, _tr(proof, n0, n1, c0, c1, r, note));
        assert(noAttr || _trEarlier(4, n0, n1, r) || sel == ShieldedPool.InvalidRoot.selector);
    }

    function check_transfer_nonCanonicalInput(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(_trNonCanon(n0, n1, c0, c1, r, note));
        bytes4 sel = _mustReject(caller, _tr(proof, n0, n1, c0, c1, r, note));
        assert(noAttr || _trEarlier(5, n0, n1, r) || sel == ShieldedPool.PublicInputGeFieldModulus.selector);
    }

    // ---- withdraw, ShieldedPool.sol:254-263 and 275 ----

    function _wdEarlier(uint256 k, bytes32 n, address t, uint256 a, address rcp, bytes32 r)
        internal
        view
        returns (bool)
    {
        if (k > 1 && !pool.supportedTokens(t)) return true;
        if (k > 2 && a == 0) return true;
        if (k > 3 && a >= MAX_AMOUNT) return true;
        if (k > 4 && rcp == address(0)) return true;
        if (k > 5 && pool.nullifiers(n)) return true;
        if (k > 6 && !_known(r)) return true;
        return false;
    }

    function check_withdraw_unsupportedToken(
        bytes memory proof,
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        vm.assume(!pool.supportedTokens(t));
        bytes4 sel = _mustReject(caller, _wd(proof, n, t, a, rcp, r));
        assert(noAttr || sel == ShieldedPool.UnsupportedToken.selector);
    }

    function check_withdraw_zeroAmount(bytes memory proof, bytes32 n, address t, address rcp, bytes32 r, address caller)
        public
    {
        _fresh();
        bytes4 sel = _mustReject(caller, _wd(proof, n, t, 0, rcp, r));
        assert(noAttr || _wdEarlier(2, n, t, 0, rcp, r) || sel == ShieldedPool.ZeroAmount.selector);
    }

    function check_withdraw_amountTooLarge(
        bytes memory proof,
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        vm.assume(a >= MAX_AMOUNT);
        bytes4 sel = _mustReject(caller, _wd(proof, n, t, a, rcp, r));
        assert(noAttr || _wdEarlier(3, n, t, a, rcp, r) || sel == ShieldedPool.AmountTooLarge.selector);
    }

    function check_withdraw_zeroRecipient(bytes memory proof, bytes32 n, address t, uint256 a, bytes32 r, address caller)
        public
    {
        _fresh();
        bytes4 sel = _mustReject(caller, _wd(proof, n, t, a, address(0), r));
        assert(noAttr || _wdEarlier(4, n, t, a, address(0), r) || sel == ShieldedPool.ZeroAddress.selector);
    }

    function check_withdraw_nullifierSpent(
        bytes memory proof,
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        vm.assume(pool.nullifiers(n));
        bytes4 sel = _mustReject(caller, _wd(proof, n, t, a, rcp, r));
        assert(noAttr || _wdEarlier(5, n, t, a, rcp, r) || sel == ShieldedPool.NullifierAlreadySpent.selector);
    }

    function check_withdraw_unknownRoot(
        bytes memory proof,
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        vm.assume(r != pool.commitmentRoot() && !pool.validRoots(r));
        bytes4 sel = _mustReject(caller, _wd(proof, n, t, a, rcp, r));
        assert(noAttr || _wdEarlier(6, n, t, a, rcp, r) || sel == ShieldedPool.InvalidRoot.selector);
    }

    function check_withdraw_nonCanonicalInput(
        bytes memory proof,
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r,
        address caller
    ) public {
        _fresh();
        vm.assume(
            uint256(n) >= P || uint256(uint160(t)) >= P || a >= P || uint256(uint160(rcp)) >= P || uint256(r) >= P
        );
        bytes4 sel = _mustReject(caller, _wd(proof, n, t, a, rcp, r));
        assert(noAttr || _wdEarlier(7, n, t, a, rcp, r) || sel == ShieldedPool.PublicInputGeFieldModulus.selector);
    }

    // ---- core-only variants: the rejection property without the revert-reason assertion ----

    function check_core_deposit_unsupportedToken(bytes memory proof, bytes32 c, address t, uint256 a, address f, bytes memory note, address caller) public {
        noAttr = true;
        check_deposit_unsupportedToken(proof, c, t, a, f, note, caller);
    }

    function check_core_deposit_zeroAmount(bytes memory proof, bytes32 c, address t, address f, bytes memory note, address caller) public {
        noAttr = true;
        check_deposit_zeroAmount(proof, c, t, f, note, caller);
    }

    function check_core_deposit_amountTooLarge(bytes memory proof, bytes32 c, address t, uint256 a, address f, bytes memory note, address caller) public {
        noAttr = true;
        check_deposit_amountTooLarge(proof, c, t, a, f, note, caller);
    }

    function check_core_deposit_zeroFundingAddress(bytes memory proof, bytes32 c, address t, uint256 a, bytes memory note, address caller) public {
        noAttr = true;
        check_deposit_zeroFundingAddress(proof, c, t, a, note, caller);
    }

    function check_core_deposit_senderNotFundingAddress(bytes memory proof, bytes32 c, address t, uint256 a, address f, bytes memory note, address caller) public {
        noAttr = true;
        check_deposit_senderNotFundingAddress(proof, c, t, a, f, note, caller);
    }

    function check_core_deposit_nonCanonicalInput(bytes memory proof, bytes32 c, address t, uint256 a, address f, bytes memory note, address caller) public {
        noAttr = true;
        check_deposit_nonCanonicalInput(proof, c, t, a, f, note, caller);
    }

    function check_core_transfer_identicalNullifiers(bytes memory proof, bytes32 n, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note, address caller) public {
        noAttr = true;
        check_transfer_identicalNullifiers(proof, n, c0, c1, r, note, caller);
    }

    function check_core_transfer_firstNullifierSpent(bytes memory proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note, address caller) public {
        noAttr = true;
        check_transfer_firstNullifierSpent(proof, n0, n1, c0, c1, r, note, caller);
    }

    function check_core_transfer_secondNullifierSpent(bytes memory proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note, address caller) public {
        noAttr = true;
        check_transfer_secondNullifierSpent(proof, n0, n1, c0, c1, r, note, caller);
    }

    function check_core_transfer_unknownRoot(bytes memory proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note, address caller) public {
        noAttr = true;
        check_transfer_unknownRoot(proof, n0, n1, c0, c1, r, note, caller);
    }

    function check_core_transfer_nonCanonicalInput(bytes memory proof, bytes32 n0, bytes32 n1, bytes32 c0, bytes32 c1, bytes32 r, bytes memory note, address caller) public {
        noAttr = true;
        check_transfer_nonCanonicalInput(proof, n0, n1, c0, c1, r, note, caller);
    }

    function check_core_withdraw_unsupportedToken(bytes memory proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller) public {
        noAttr = true;
        check_withdraw_unsupportedToken(proof, n, t, a, rcp, r, caller);
    }

    function check_core_withdraw_zeroAmount(bytes memory proof, bytes32 n, address t, address rcp, bytes32 r, address caller) public {
        noAttr = true;
        check_withdraw_zeroAmount(proof, n, t, rcp, r, caller);
    }

    function check_core_withdraw_amountTooLarge(bytes memory proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller) public {
        noAttr = true;
        check_withdraw_amountTooLarge(proof, n, t, a, rcp, r, caller);
    }

    function check_core_withdraw_zeroRecipient(bytes memory proof, bytes32 n, address t, uint256 a, bytes32 r, address caller) public {
        noAttr = true;
        check_withdraw_zeroRecipient(proof, n, t, a, r, caller);
    }

    function check_core_withdraw_nullifierSpent(bytes memory proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller) public {
        noAttr = true;
        check_withdraw_nullifierSpent(proof, n, t, a, rcp, r, caller);
    }

    function check_core_withdraw_unknownRoot(bytes memory proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller) public {
        noAttr = true;
        check_withdraw_unknownRoot(proof, n, t, a, rcp, r, caller);
    }

    function check_core_withdraw_nonCanonicalInput(bytes memory proof, bytes32 n, address t, uint256 a, address rcp, bytes32 r, address caller) public {
        noAttr = true;
        check_withdraw_nonCanonicalInput(proof, n, t, a, rcp, r, caller);
    }

    /// The zero-funder guard with msg.sender != 0: shows whether the caller-mismatch guard alone already rejects fundingAddress == 0.
    function check_core_deposit_zeroFundingAddress_nonzeroCaller(bytes memory proof, bytes32 c, address t, uint256 a, bytes memory note, address caller) public {
        vm.assume(caller != address(0));
        noAttr = true;
        check_deposit_zeroFundingAddress(proof, c, t, a, note, caller);
    }

    // ---- spent nullifier, marked by the contract itself: a successful withdraw, then any reuse ----

    function check_spent_withdrawThenReuseRejected(bytes32 n, uint256 a, address rcp, bytes32 r, address caller) public {
        _fresh();
        token.mint(address(pool), MAX_AMOUNT);
        vm.assume(pool.supportedTokens(address(token)));
        verifier.setTrip(false);
        (bool ok,) = address(pool).call(_wd("", n, address(token), a, rcp, r));
        vm.assume(ok);
        assert(pool.nullifiers(n));
        _reuseRejected(caller, n);
    }

    /// After n is spent: a second withdraw of n, and a transfer that spends n in input slot 0 or 1,
    /// with every other argument fresh and symbolic, are all rejected.
    function _reuseRejected(address caller, bytes32 n) internal {
        _mustReject(
            caller,
            _wd("", n, svm.createAddress("t2"), svm.createUint256("a2"), svm.createAddress("rcp2"), svm.createBytes32("r2"))
        );
        bytes32 m = svm.createBytes32("m");
        bytes32 c0 = svm.createBytes32("c0");
        bytes32 c1 = svm.createBytes32("c1");
        bytes32 r3 = svm.createBytes32("r3");
        _mustReject(caller, _tr("", n, m, c0, c1, r3, ""));
        _mustReject(caller, _tr("", m, n, c0, c1, r3, ""));
    }

    // ---- probes: the fresh-pool slots are really symbolic (each _expectFail must FAIL) ----

    function check_PROBE_nullifierCanBeSpent_expectFail(bytes32 k) public {
        _fresh();
        assert(!pool.nullifiers(k));
    }

    function check_PROBE_nullifierCanBeUnspent_expectFail(bytes32 k) public {
        _fresh();
        assert(pool.nullifiers(k));
    }

    function check_PROBE_nullifierKeysIndependent_expectFail(bytes32 k1, bytes32 k2) public {
        _fresh();
        assert(!(pool.nullifiers(k1) && !pool.nullifiers(k2)));
    }

    function check_PROBE_tokenCanBeSupported_expectFail(address t) public {
        _fresh();
        assert(!pool.supportedTokens(t));
    }

    function check_PROBE_tokenCanBeUnsupported_expectFail(address t) public {
        _fresh();
        assert(pool.supportedTokens(t));
    }

    function check_PROBE_validRootCanBeTrue_expectFail(bytes32 r) public {
        _fresh();
        assert(!pool.validRoots(r));
    }

    function check_PROBE_validRootCanBeFalse_expectFail(bytes32 r) public {
        _fresh();
        assert(pool.validRoots(r));
    }

    function check_PROBE_currentRootArbitrary_expectFail(bytes32 r) public {
        _fresh();
        assert(pool.commitmentRoot() != r);
    }

    function check_PROBE_rootIndexArbitrary_expectFail() public {
        _fresh();
        assert(pool.historicalRootIndex() < 100);
    }

    function check_PROBE_attestationRootNonCanonical_expectFail() public {
        _fresh();
        assert(uint256(registry.attestationRoot()) < P);
    }

    /// Expected PASS: the constructor-written slots stay concrete (they are not part of the claim).
    function check_PROBE_constructorSlotsConcrete() public {
        _fresh();
        assert(address(pool.verifier()) == address(verifier));
        assert(address(pool.attestationRegistry()) == address(registry));
        assert(pool.owner() == address(this));
        assert(uint256(vm.load(address(pool), REENTRANCY_SLOT)) == 1);
    }

    // ---- witnesses: with every guard passing, the verifier is reached (each must FAIL) ----

    function check_WIT_deposit_verifierReached_expectFail(
        bytes memory proof,
        bytes32 c,
        address t,
        uint256 a,
        bytes memory note,
        address caller
    ) public {
        _fresh();
        vm.assume(!_depEarlier(6, t, a, caller, caller) && !_depNonCanon(c, t, a, caller, note));
        verifier.setTrip(true);
        vm.prank(caller);
        (, bytes memory ret) = address(pool).call(_dep(proof, c, t, a, caller, note));
        assert(bytes4(ret) != RecordingVerifier.VerifierReached.selector);
    }

    function check_WIT_transfer_verifierReached_expectFail(
        bytes memory proof,
        bytes32 n0,
        bytes32 n1,
        bytes32 c0,
        bytes32 c1,
        bytes32 r,
        bytes memory note
    ) public {
        _fresh();
        vm.assume(!_trEarlier(5, n0, n1, r) && !_trNonCanon(n0, n1, c0, c1, r, note));
        verifier.setTrip(true);
        (, bytes memory ret) = address(pool).call(_tr(proof, n0, n1, c0, c1, r, note));
        assert(bytes4(ret) != RecordingVerifier.VerifierReached.selector);
    }

    function check_WIT_withdraw_verifierReached_expectFail(
        bytes memory proof,
        bytes32 n,
        address t,
        uint256 a,
        address rcp,
        bytes32 r
    ) public {
        _fresh();
        vm.assume(!_wdEarlier(7, n, t, a, rcp, r));
        vm.assume(uint256(n) < P && uint256(r) < P);
        verifier.setTrip(true);
        (, bytes memory ret) = address(pool).call(_wd(proof, n, t, a, rcp, r));
        assert(bytes4(ret) != RecordingVerifier.VerifierReached.selector);
    }

    /// Positive control for the state snapshot: a successful withdraw (ACCEPT mode) changes the state.
    function check_WIT_withdraw_stateChanges_expectFail(bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _fresh();
        token.mint(address(pool), MAX_AMOUNT);
        vm.assume(pool.supportedTokens(address(token)));
        verifier.setTrip(false);
        bytes32 g0 = svm.snapshotState();
        (bool ok,) = address(pool).call(_wd("", n, address(token), a, rcp, r));
        bytes32 g1 = svm.snapshotState();
        vm.assume(ok);
        assert(g1 == g0);
    }

    /// Positive control for the pool-storage snapshot. Every slot the withdraw reads is read first, so a
    /// lazily created symbolic slot cannot change the digest; only the nullifier write can.
    function check_WIT_withdraw_poolStorageChanges_expectFail(bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _fresh();
        token.mint(address(pool), MAX_AMOUNT);
        vm.assume(pool.supportedTokens(address(token)));
        vm.assume(!pool.nullifiers(n) && _known(r));
        verifier.setTrip(false);
        uint256 p0 = svm.snapshotStorage(address(pool));
        (bool ok,) = address(pool).call(_wd("", n, address(token), a, rcp, r));
        uint256 p1 = svm.snapshotStorage(address(pool));
        vm.assume(ok);
        assert(p1 == p0);
    }

    /// Positive control for the token snapshot: a successful withdraw moves tokens.
    function check_WIT_withdraw_tokenMoves_expectFail(bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _fresh();
        token.mint(address(pool), MAX_AMOUNT);
        vm.assume(pool.supportedTokens(address(token)));
        verifier.setTrip(false);
        uint256 k0 = svm.snapshotStorage(address(token));
        (bool ok,) = address(pool).call(_wd("", n, address(token), a, rcp, r));
        uint256 k1 = svm.snapshotStorage(address(token));
        vm.assume(ok);
        assert(k1 == k0);
    }
}

// ---- mutant controls: each deploys a copy of ShieldedPool with one guard removed ----

contract GuardsMut_DEP_TOKENTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEP_TOKEN(v, r));
    }
}

contract GuardsMut_DEP_AMOUNT_ZEROTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEP_AMOUNT_ZERO(v, r));
    }
}

contract GuardsMut_DEP_AMOUNT_MAXTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEP_AMOUNT_MAX(v, r));
    }
}

contract GuardsMut_DEP_FUNDER_ZEROTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEP_FUNDER_ZERO(v, r));
    }
}

contract GuardsMut_DEP_FUNDER_CALLERTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEP_FUNDER_CALLER(v, r));
    }
}

contract GuardsMut_DEP_CANONICALTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_DEP_CANONICAL(v, r));
    }
}

contract GuardsMut_TR_DISTINCTTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TR_DISTINCT(v, r));
    }
}

contract GuardsMut_TR_SPENT0Test is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TR_SPENT0(v, r));
    }
}

contract GuardsMut_TR_SPENT1Test is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TR_SPENT1(v, r));
    }
}

contract GuardsMut_TR_ROOTTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TR_ROOT(v, r));
    }
}

contract GuardsMut_TR_CANONICALTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_TR_CANONICAL(v, r));
    }
}

contract GuardsMut_WD_TOKENTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WD_TOKEN(v, r));
    }
}

contract GuardsMut_WD_AMOUNT_ZEROTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WD_AMOUNT_ZERO(v, r));
    }
}

contract GuardsMut_WD_AMOUNT_MAXTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WD_AMOUNT_MAX(v, r));
    }
}

contract GuardsMut_WD_RECIPIENT_ZEROTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WD_RECIPIENT_ZERO(v, r));
    }
}

contract GuardsMut_WD_SPENTTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WD_SPENT(v, r));
    }
}

contract GuardsMut_WD_ROOTTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WD_ROOT(v, r));
    }
}

contract GuardsMut_WD_CANONICALTest is GuardsTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_WD_CANONICAL(v, r));
    }
}
