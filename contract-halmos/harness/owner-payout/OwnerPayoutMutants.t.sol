// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// One OwnerPayoutTest per mutant (mutants/owner-payout/). Each must FAIL the checks named in runs.tsv.
import {OwnerPayoutTest} from "./OwnerPayout.t.sol";
import {ShieldedPool_M_PAY_SENDER} from "./mutants/ShieldedPool_M_PAY_SENDER.sol";
import {ShieldedPool_M_PAY_AMT1} from "./mutants/ShieldedPool_M_PAY_AMT1.sol";
import {ShieldedPool_M_PAY_TOK} from "./mutants/ShieldedPool_M_PAY_TOK.sol";
import {ShieldedPool_M_PAY_TWICE} from "./mutants/ShieldedPool_M_PAY_TWICE.sol";
import {ShieldedPool_M_PAY_RCP_HI} from "./mutants/ShieldedPool_M_PAY_RCP_HI.sol";
import {ShieldedPool_M_PI_TOK} from "./mutants/ShieldedPool_M_PI_TOK.sol";
import {ShieldedPool_M_PI_AMT} from "./mutants/ShieldedPool_M_PI_AMT.sol";
import {ShieldedPool_M_PI_RCP} from "./mutants/ShieldedPool_M_PI_RCP.sol";
import {ShieldedPool_M_PI_NUL_HI} from "./mutants/ShieldedPool_M_PI_NUL_HI.sol";
import {ShieldedPool_M_PI_TOK_HI} from "./mutants/ShieldedPool_M_PI_TOK_HI.sol";
import {ShieldedPool_M_PI_RCP_HI} from "./mutants/ShieldedPool_M_PI_RCP_HI.sol";
import {ShieldedPool_M_PI_ROOT_HI} from "./mutants/ShieldedPool_M_PI_ROOT_HI.sol";
import {ShieldedPool_M_OO_ADD} from "./mutants/ShieldedPool_M_OO_ADD.sol";
import {ShieldedPool_M_OO_REM} from "./mutants/ShieldedPool_M_OO_REM.sol";
import {ShieldedPool_M_OO_SETV} from "./mutants/ShieldedPool_M_OO_SETV.sol";
import {ShieldedPool_M_OO_SETR} from "./mutants/ShieldedPool_M_OO_SETR.sol";
import {ShieldedPool_M_OO_OWN} from "./mutants/ShieldedPool_M_OO_OWN.sol";
import {ShieldedPool_M_EFF_ADD} from "./mutants/ShieldedPool_M_EFF_ADD.sol";
import {ShieldedPool_M_EFF_REM} from "./mutants/ShieldedPool_M_EFF_REM.sol";
import {ShieldedPool_M_EFF_SETV} from "./mutants/ShieldedPool_M_EFF_SETV.sol";
import {ShieldedPool_M_EFF_SETR} from "./mutants/ShieldedPool_M_EFF_SETR.sol";
import {ShieldedPool_M_EFF_OWN} from "./mutants/ShieldedPool_M_EFF_OWN.sol";

contract OwnerPayoutMut_PAY_SENDERTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_SENDER(v, r));
    }
}

contract OwnerPayoutMut_PAY_AMT1Test is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_AMT1(v, r));
    }
}

contract OwnerPayoutMut_PAY_TOKTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_TOK(v, r));
    }
}

contract OwnerPayoutMut_PAY_TWICETest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_TWICE(v, r));
    }
}

contract OwnerPayoutMut_PAY_RCP_HITest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PAY_RCP_HI(v, r));
    }
}

contract OwnerPayoutMut_PI_TOKTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PI_TOK(v, r));
    }
}

contract OwnerPayoutMut_PI_AMTTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PI_AMT(v, r));
    }
}

contract OwnerPayoutMut_PI_RCPTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PI_RCP(v, r));
    }
}

contract OwnerPayoutMut_PI_NUL_HITest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PI_NUL_HI(v, r));
    }
}

contract OwnerPayoutMut_PI_TOK_HITest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PI_TOK_HI(v, r));
    }
}

contract OwnerPayoutMut_PI_RCP_HITest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PI_RCP_HI(v, r));
    }
}

contract OwnerPayoutMut_PI_ROOT_HITest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_PI_ROOT_HI(v, r));
    }
}

contract OwnerPayoutMut_OO_ADDTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_OO_ADD(v, r));
    }
}

contract OwnerPayoutMut_OO_REMTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_OO_REM(v, r));
    }
}

contract OwnerPayoutMut_OO_SETVTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_OO_SETV(v, r));
    }
}

contract OwnerPayoutMut_OO_SETRTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_OO_SETR(v, r));
    }
}

contract OwnerPayoutMut_OO_OWNTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_OO_OWN(v, r));
    }
}

contract OwnerPayoutMut_EFF_ADDTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_EFF_ADD(v, r));
    }
}

contract OwnerPayoutMut_EFF_REMTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_EFF_REM(v, r));
    }
}

contract OwnerPayoutMut_EFF_SETVTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_EFF_SETV(v, r));
    }
}

contract OwnerPayoutMut_EFF_SETRTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_EFF_SETR(v, r));
    }
}

contract OwnerPayoutMut_EFF_OWNTest is OwnerPayoutTest {
    function _deploy(address v, address r) internal override returns (address) {
        return address(new ShieldedPool_M_EFF_OWN(v, r));
    }
}
