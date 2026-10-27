// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// One PostTransferAdminTest per mutant (mutants/post-transfer-admin/). Each must FAIL the check named in runs.tsv.
import {PostTransferAdminTest} from "./PostTransferAdmin.t.sol";
import {M_T_distinct} from "./mutants/M_T_distinct.sol";
contract PostTransferAdminMut_T_distinct is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_distinct(v,r));}}
import {M_T_unspent} from "./mutants/M_T_unspent.sol";
contract PostTransferAdminMut_T_unspent is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_unspent(v,r));}}
import {M_T_known_root} from "./mutants/M_T_known_root.sol";
contract PostTransferAdminMut_T_known_root is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_known_root(v,r));}}
import {M_T_fresh_outputs} from "./mutants/M_T_fresh_outputs.sol";
contract PostTransferAdminMut_T_fresh_outputs is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_fresh_outputs(v,r));}}
import {M_T_verified} from "./mutants/M_T_verified.sol";
contract PostTransferAdminMut_T_verified is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_verified(v,r));}}
import {M_T_no_effects} from "./mutants/M_T_no_effects.sol";
contract PostTransferAdminMut_T_no_effects is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_no_effects(v,r));}}
import {M_T_post} from "./mutants/M_T_post.sol";
contract PostTransferAdminMut_T_post is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_post(v,r));}}
import {M_A_add} from "./mutants/M_A_add.sol";
contract PostTransferAdminMut_A_add is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_A_add(v,r));}}
import {M_A_remove} from "./mutants/M_A_remove.sol";
contract PostTransferAdminMut_A_remove is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_A_remove(v,r));}}
import {M_A_registry} from "./mutants/M_A_registry.sol";
contract PostTransferAdminMut_A_registry is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_A_registry(v,r));}}
import {M_A_owner} from "./mutants/M_A_owner.sol";
contract PostTransferAdminMut_A_owner is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_A_owner(v,r));}}
import {M_T_verified_root} from "./mutants/M_T_verified_root.sol";
contract PostTransferAdminMut_T_verified_root is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_verified_root(v,r));}}
import {M_T_verified_canonical} from "./mutants/M_T_verified_canonical.sol";
contract PostTransferAdminMut_T_verified_canonical is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_verified_canonical(v,r));}}
import {M_T_post_mapping} from "./mutants/M_T_post_mapping.sol";
contract PostTransferAdminMut_T_post_mapping is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_post_mapping(v,r));}}
import {M_T_post_order} from "./mutants/M_T_post_order.sol";
contract PostTransferAdminMut_T_post_order is PostTransferAdminTest {function _deploy(address v,address r) internal override returns(address){return address(new M_T_post_order(v,r));}}
