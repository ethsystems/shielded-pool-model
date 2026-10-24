// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// One PostDepositWithdrawTest per mutant (mutants/post-deposit-withdraw/). Each must FAIL the check named in runs.tsv.
import {PostDepositWithdrawTest} from "./PostDepositWithdraw.t.sol";
import {M_W_amount_ne_zero} from "./mutants/M_W_amount_ne_zero.sol";
contract PostDepositWithdrawMut_W_amount_ne_zero is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_W_amount_ne_zero(v,r));}}
import {M_W_unspent} from "./mutants/M_W_unspent.sol";
contract PostDepositWithdrawMut_W_unspent is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_W_unspent(v,r));}}
import {M_W_known_root} from "./mutants/M_W_known_root.sol";
contract PostDepositWithdrawMut_W_known_root is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_W_known_root(v,r));}}
import {M_W_verified} from "./mutants/M_W_verified.sol";
contract PostDepositWithdrawMut_W_verified is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_W_verified(v,r));}}
import {M_W_guarded} from "./mutants/M_W_guarded.sol";
contract PostDepositWithdrawMut_W_guarded is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_W_guarded(v,r));}}
import {M_W_token_calls} from "./mutants/M_W_token_calls.sol";
contract PostDepositWithdrawMut_W_token_calls is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_W_token_calls(v,r));}}
import {M_W_post} from "./mutants/M_W_post.sol";
contract PostDepositWithdrawMut_W_post is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_W_post(v,r));}}
import {M_D_amount_ne_zero} from "./mutants/M_D_amount_ne_zero.sol";
contract PostDepositWithdrawMut_D_amount_ne_zero is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_D_amount_ne_zero(v,r));}}
import {M_D_supported} from "./mutants/M_D_supported.sol";
contract PostDepositWithdrawMut_D_supported is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_D_supported(v,r));}}
import {M_D_fresh_leaf} from "./mutants/M_D_fresh_leaf.sol";
contract PostDepositWithdrawMut_D_fresh_leaf is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_D_fresh_leaf(v,r));}}
import {M_D_verified} from "./mutants/M_D_verified.sol";
contract PostDepositWithdrawMut_D_verified is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_D_verified(v,r));}}
import {M_D_guarded} from "./mutants/M_D_guarded.sol";
contract PostDepositWithdrawMut_D_guarded is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_D_guarded(v,r));}}
import {M_D_token_calls} from "./mutants/M_D_token_calls.sol";
contract PostDepositWithdrawMut_D_token_calls is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_D_token_calls(v,r));}}
import {M_D_post} from "./mutants/M_D_post.sol";
contract PostDepositWithdrawMut_D_post is PostDepositWithdrawTest {function _deploy(address v,address r) internal override returns(address){return address(new M_D_post(v,r));}}
