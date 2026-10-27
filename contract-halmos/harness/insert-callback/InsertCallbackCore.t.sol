// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Extra X1 core checks. The X1 checks in InsertCallback.t.sol also assert the inner revert selector, so a
// mutant can fail them only because the inner call reverted for another reason. These core checks
// assert only that the inner call did not succeed. On the nonReentrant mutants they must FAIL, which
// shows that without the guard the inner call can succeed.

import {InsertCallbackTest} from "./InsertCallback.t.sol";
import {ShieldedPool_M_NR_D} from "./mutants/ShieldedPool_M_NR_D.sol";
import {ShieldedPool_M_NR_T} from "./mutants/ShieldedPool_M_NR_T.sol";
import {ShieldedPool_M_NR_W} from "./mutants/ShieldedPool_M_NR_W.sol";

abstract contract InsertCallbackCore is InsertCallbackTest {
    function _coreDep(uint256 inner, bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) internal {
        _fresh();
        _depPass(c, a, f);
        _setInner(inner);
        _dep(proof, c, a, f, note);
        vm.assume(token.innerTried());
        assert(!token.innerOk());
    }

    function _coreWd(uint256 inner, bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) internal {
        _fresh();
        _wdPass(n, a, rcp, r);
        _setInner(inner);
        _wd(proof, n, a, rcp, r);
        vm.assume(token.innerTried());
        assert(!token.innerOk());
    }

    function check_X1core_depositReentersDeposit(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _coreDep(DEP, proof, c, a, f, note);
    }

    function check_X1core_depositReentersTransfer(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _coreDep(TR, proof, c, a, f, note);
    }

    function check_X1core_depositReentersWithdraw(bytes memory proof, bytes32 c, uint256 a, address f, bytes memory note) public {
        _coreDep(WD, proof, c, a, f, note);
    }

    function check_X1core_withdrawReentersDeposit(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _coreWd(DEP, proof, n, a, rcp, r);
    }

    function check_X1core_withdrawReentersTransfer(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _coreWd(TR, proof, n, a, rcp, r);
    }

    function check_X1core_withdrawReentersWithdraw(bytes memory proof, bytes32 n, uint256 a, address rcp, bytes32 r) public {
        _coreWd(WD, proof, n, a, rcp, r);
    }
}

contract InsertCallbackCoreTest is InsertCallbackCore {}

contract InsertCallbackCoreMut_NR_DTest is InsertCallbackCore {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_D(v, r));
    }
}

contract InsertCallbackCoreMut_NR_TTest is InsertCallbackCore {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_T(v, r));
    }
}

contract InsertCallbackCoreMut_NR_WTest is InsertCallbackCore {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_NR_W(v, r));
    }
}
