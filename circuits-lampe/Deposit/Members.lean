import Poseidon.Hash
import Deposit.MainHashes
namespace Deposit.Members
open Lampe
theorem main : «deposit-0.0.0::main» ∈ «deposit-0.0.0».env.functions := by
  have h : «deposit-0.0.0::main» ∈ «deposit-0.0.0».Main.env.functions := by
    change «deposit-0.0.0::main» ∈ [«deposit-0.0.0::MAX_ATTESTATION_TREE_DEPTH», «deposit-0.0.0::poseidon4», «deposit-0.0.0::poseidon2», «deposit-0.0.0::verify_merkle_proof», «deposit-0.0.0::main», «deposit-0.0.0::test_deposit_valid», «deposit-0.0.0::test_deposit_with_expiry», «deposit-0.0.0::test_deposit_invalid_commitment», «deposit-0.0.0::test_deposit_invalid_merkle_proof», «deposit-0.0.0::test_deposit_amount_above_u128», «deposit-0.0.0::test_deposit_wrong_spending_key»]
    exact List.mem_cons_of_mem «deposit-0.0.0::MAX_ATTESTATION_TREE_DEPTH» (List.mem_cons_of_mem «deposit-0.0.0::poseidon4» (List.mem_cons_of_mem «deposit-0.0.0::poseidon2» (List.mem_cons_of_mem «deposit-0.0.0::verify_merkle_proof» (List.mem_cons_self))))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms main
theorem range : «std-1.0.0-beta.21::field::assert_max_bit_size» ∈ «deposit-0.0.0».env.functions := by
  have h : «std-1.0.0-beta.21::field::assert_max_bit_size» ∈ «std-1.0.0-beta.21».Field.Mod.env.functions := by
    change «std-1.0.0-beta.21::field::assert_max_bit_size» ∈ [«std-1.0.0-beta.21::field::assert_max_bit_size», «std-1.0.0-beta.21::field::to_le_bits», «std-1.0.0-beta.21::field::to_be_bits», «std-1.0.0-beta.21::field::to_le_bytes», «std-1.0.0-beta.21::field::to_be_bytes», «std-1.0.0-beta.21::field::to_le_radix», «std-1.0.0-beta.21::field::to_be_radix», «std-1.0.0-beta.21::field::pow_32», «std-1.0.0-beta.21::field::sgn0», «std-1.0.0-beta.21::field::lt», «std-1.0.0-beta.21::field::from_le_bytes», «std-1.0.0-beta.21::field::from_be_bytes», «std-1.0.0-beta.21::field::__field_less_than», «std-1.0.0-beta.21::field::field_less_than», «std-1.0.0-beta.21::field::bytes32_to_field», «std-1.0.0-beta.21::field::lt_fallback», «std-1.0.0-beta.21::field::tests::test_to_be_bits», «std-1.0.0-beta.21::field::tests::test_to_le_bits», «std-1.0.0-beta.21::field::tests::test_to_be_bytes», «std-1.0.0-beta.21::field::tests::test_to_le_bytes», «std-1.0.0-beta.21::field::tests::test_to_be_radix», «std-1.0.0-beta.21::field::tests::test_to_le_radix», «std-1.0.0-beta.21::field::tests::test_to_le_radix_1», «std-1.0.0-beta.21::field::tests::test_to_le_radix_brillig_1», «std-1.0.0-beta.21::field::tests::test_to_le_radix_3», «std-1.0.0-beta.21::field::tests::test_to_le_radix_brillig_3», «std-1.0.0-beta.21::field::tests::test_to_le_radix_512», «std-1.0.0-beta.21::field::tests::not_enough_limbs_brillig», «std-1.0.0-beta.21::field::tests::not_enough_limbs», «std-1.0.0-beta.21::field::tests::test_field_less_than», «std-1.0.0-beta.21::field::tests::test_large_field_values_unconstrained», «std-1.0.0-beta.21::field::tests::test_large_field_values», «std-1.0.0-beta.21::field::tests::test_decomposition_edge_cases», «std-1.0.0-beta.21::field::tests::test_pow_32», «std-1.0.0-beta.21::field::tests::test_sgn0», «std-1.0.0-beta.21::field::tests::test_bit_decomposition_overflow», «std-1.0.0-beta.21::field::tests::test_byte_decomposition_overflow», «std-1.0.0-beta.21::field::tests::test_to_from_be_bytes_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::test_to_from_le_bytes_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::from_le_bits», «std-1.0.0-beta.21::field::tests::from_be_bits», «std-1.0.0-beta.21::field::tests::test_to_from_be_bits_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::test_to_from_le_bits_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::max_bit_size_too_large»]
    exact List.mem_cons_self
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms range
theorem verify : «deposit-0.0.0::verify_merkle_proof» ∈ «deposit-0.0.0».env.functions := by
  have h : «deposit-0.0.0::verify_merkle_proof» ∈ «deposit-0.0.0».Main.env.functions := by
    change «deposit-0.0.0::verify_merkle_proof» ∈ [«deposit-0.0.0::MAX_ATTESTATION_TREE_DEPTH», «deposit-0.0.0::poseidon4», «deposit-0.0.0::poseidon2», «deposit-0.0.0::verify_merkle_proof», «deposit-0.0.0::main», «deposit-0.0.0::test_deposit_valid», «deposit-0.0.0::test_deposit_with_expiry», «deposit-0.0.0::test_deposit_invalid_commitment», «deposit-0.0.0::test_deposit_invalid_merkle_proof», «deposit-0.0.0::test_deposit_amount_above_u128», «deposit-0.0.0::test_deposit_wrong_spending_key»]
    exact List.mem_cons_of_mem «deposit-0.0.0::MAX_ATTESTATION_TREE_DEPTH» (List.mem_cons_of_mem «deposit-0.0.0::poseidon4» (List.mem_cons_of_mem «deposit-0.0.0::poseidon2» (List.mem_cons_self)))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms verify
theorem root : «binary_merkle_root-0.0.0::binary_merkle_root» ∈ «deposit-0.0.0».env.functions := by
  have h : «binary_merkle_root-0.0.0::binary_merkle_root» ∈ «binary_merkle_root-0.0.0».Lib.env.functions := by
    change «binary_merkle_root-0.0.0::binary_merkle_root» ∈ [«binary_merkle_root-0.0.0::binary_merkle_root»]
    exact List.mem_cons_self
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms root
theorem hash1 : «poseidon-0.0.0::poseidon::bn254::hash_1» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::hash_1» ∈ «poseidon-0.0.0».Poseidon.Bn254.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::hash_1» ∈ [«poseidon-0.0.0::poseidon::bn254::sponge», «poseidon-0.0.0::poseidon::bn254::hash_internal», «poseidon-0.0.0::poseidon::bn254::hash_1», «poseidon-0.0.0::poseidon::bn254::hash_2», «poseidon-0.0.0::poseidon::bn254::hash_3», «poseidon-0.0.0::poseidon::bn254::hash_4», «poseidon-0.0.0::poseidon::bn254::hash_5», «poseidon-0.0.0::poseidon::bn254::hash_6», «poseidon-0.0.0::poseidon::bn254::hash_7», «poseidon-0.0.0::poseidon::bn254::hash_8», «poseidon-0.0.0::poseidon::bn254::hash_9», «poseidon-0.0.0::poseidon::bn254::hash_10», «poseidon-0.0.0::poseidon::bn254::hash_11», «poseidon-0.0.0::poseidon::bn254::hash_12», «poseidon-0.0.0::poseidon::bn254::hash_13», «poseidon-0.0.0::poseidon::bn254::hash_14», «poseidon-0.0.0::poseidon::bn254::hash_15», «poseidon-0.0.0::poseidon::bn254::hash_16»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::sponge» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::hash_internal» (List.mem_cons_self))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms hash1
theorem hash4 : «poseidon-0.0.0::poseidon::bn254::hash_4» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::hash_4» ∈ «poseidon-0.0.0».Poseidon.Bn254.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::hash_4» ∈ [«poseidon-0.0.0::poseidon::bn254::sponge», «poseidon-0.0.0::poseidon::bn254::hash_internal», «poseidon-0.0.0::poseidon::bn254::hash_1», «poseidon-0.0.0::poseidon::bn254::hash_2», «poseidon-0.0.0::poseidon::bn254::hash_3», «poseidon-0.0.0::poseidon::bn254::hash_4», «poseidon-0.0.0::poseidon::bn254::hash_5», «poseidon-0.0.0::poseidon::bn254::hash_6», «poseidon-0.0.0::poseidon::bn254::hash_7», «poseidon-0.0.0::poseidon::bn254::hash_8», «poseidon-0.0.0::poseidon::bn254::hash_9», «poseidon-0.0.0::poseidon::bn254::hash_10», «poseidon-0.0.0::poseidon::bn254::hash_11», «poseidon-0.0.0::poseidon::bn254::hash_12», «poseidon-0.0.0::poseidon::bn254::hash_13», «poseidon-0.0.0::poseidon::bn254::hash_14», «poseidon-0.0.0::poseidon::bn254::hash_15», «poseidon-0.0.0::poseidon::bn254::hash_16»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::sponge» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::hash_internal» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::hash_1» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::hash_2» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::hash_3» (List.mem_cons_self)))))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms hash4
theorem poseidon4 : «deposit-0.0.0::poseidon4» ∈ «deposit-0.0.0».env.functions := by
  have h : «deposit-0.0.0::poseidon4» ∈ «deposit-0.0.0».Main.env.functions := by
    change «deposit-0.0.0::poseidon4» ∈ [«deposit-0.0.0::MAX_ATTESTATION_TREE_DEPTH», «deposit-0.0.0::poseidon4», «deposit-0.0.0::poseidon2», «deposit-0.0.0::verify_merkle_proof», «deposit-0.0.0::main», «deposit-0.0.0::test_deposit_valid», «deposit-0.0.0::test_deposit_with_expiry», «deposit-0.0.0::test_deposit_invalid_commitment», «deposit-0.0.0::test_deposit_invalid_merkle_proof», «deposit-0.0.0::test_deposit_amount_above_u128», «deposit-0.0.0::test_deposit_wrong_spending_key»]
    exact List.mem_cons_of_mem «deposit-0.0.0::MAX_ATTESTATION_TREE_DEPTH» (List.mem_cons_self)
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms poseidon4
theorem internal : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ «poseidon-0.0.0».Poseidon.Bn254.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::hash_internal» ∈ [«poseidon-0.0.0::poseidon::bn254::sponge», «poseidon-0.0.0::poseidon::bn254::hash_internal», «poseidon-0.0.0::poseidon::bn254::hash_1», «poseidon-0.0.0::poseidon::bn254::hash_2», «poseidon-0.0.0::poseidon::bn254::hash_3», «poseidon-0.0.0::poseidon::bn254::hash_4», «poseidon-0.0.0::poseidon::bn254::hash_5», «poseidon-0.0.0::poseidon::bn254::hash_6», «poseidon-0.0.0::poseidon::bn254::hash_7», «poseidon-0.0.0::poseidon::bn254::hash_8», «poseidon-0.0.0::poseidon::bn254::hash_9», «poseidon-0.0.0::poseidon::bn254::hash_10», «poseidon-0.0.0::poseidon::bn254::hash_11», «poseidon-0.0.0::poseidon::bn254::hash_12», «poseidon-0.0.0::poseidon::bn254::hash_13», «poseidon-0.0.0::poseidon::bn254::hash_14», «poseidon-0.0.0::poseidon::bn254::hash_15», «poseidon-0.0.0::poseidon::bn254::hash_16»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::sponge» (List.mem_cons_self)
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms internal
theorem wrapper2 : «poseidon-0.0.0::poseidon::bn254::perm::x5_2» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::perm::x5_2» ∈ «poseidon-0.0.0».Poseidon.Bn254.Perm.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::perm::x5_2» ∈ [«poseidon-0.0.0::poseidon::bn254::perm::x5_2», «poseidon-0.0.0::poseidon::bn254::perm::x5_3», «poseidon-0.0.0::poseidon::bn254::perm::x5_4», «poseidon-0.0.0::poseidon::bn254::perm::x5_5», «poseidon-0.0.0::poseidon::bn254::perm::x5_6», «poseidon-0.0.0::poseidon::bn254::perm::x5_7», «poseidon-0.0.0::poseidon::bn254::perm::x5_8», «poseidon-0.0.0::poseidon::bn254::perm::x5_9», «poseidon-0.0.0::poseidon::bn254::perm::x5_10», «poseidon-0.0.0::poseidon::bn254::perm::x5_11», «poseidon-0.0.0::poseidon::bn254::perm::x5_12», «poseidon-0.0.0::poseidon::bn254::perm::x5_13», «poseidon-0.0.0::poseidon::bn254::perm::x5_14», «poseidon-0.0.0::poseidon::bn254::perm::x5_15», «poseidon-0.0.0::poseidon::bn254::perm::x5_16», «poseidon-0.0.0::poseidon::bn254::perm::x5_17»]
    exact List.mem_cons_self
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms wrapper2
theorem wrapper5 : «poseidon-0.0.0::poseidon::bn254::perm::x5_5» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::perm::x5_5» ∈ «poseidon-0.0.0».Poseidon.Bn254.Perm.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::perm::x5_5» ∈ [«poseidon-0.0.0::poseidon::bn254::perm::x5_2», «poseidon-0.0.0::poseidon::bn254::perm::x5_3», «poseidon-0.0.0::poseidon::bn254::perm::x5_4», «poseidon-0.0.0::poseidon::bn254::perm::x5_5», «poseidon-0.0.0::poseidon::bn254::perm::x5_6», «poseidon-0.0.0::poseidon::bn254::perm::x5_7», «poseidon-0.0.0::poseidon::bn254::perm::x5_8», «poseidon-0.0.0::poseidon::bn254::perm::x5_9», «poseidon-0.0.0::poseidon::bn254::perm::x5_10», «poseidon-0.0.0::poseidon::bn254::perm::x5_11», «poseidon-0.0.0::poseidon::bn254::perm::x5_12», «poseidon-0.0.0::poseidon::bn254::perm::x5_13», «poseidon-0.0.0::poseidon::bn254::perm::x5_14», «poseidon-0.0.0::poseidon::bn254::perm::x5_15», «poseidon-0.0.0::poseidon::bn254::perm::x5_16», «poseidon-0.0.0::poseidon::bn254::perm::x5_17»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::perm::x5_2» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::perm::x5_3» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::perm::x5_4» (List.mem_cons_self)))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms wrapper5
theorem config2 : «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config» ∈ «poseidon-0.0.0».Poseidon.Bn254.Consts.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config» ∈ [«poseidon-0.0.0::poseidon::bn254::consts::alpha», «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_4_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_6_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_7_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_8_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_9_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_10_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_11_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_12_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_13_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_14_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_15_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_16_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_17_config»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::consts::alpha» (List.mem_cons_self)
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms config2
theorem config5 : «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config» ∈ «poseidon-0.0.0».Poseidon.Bn254.Consts.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config» ∈ [«poseidon-0.0.0::poseidon::bn254::consts::alpha», «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_4_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_6_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_7_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_8_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_9_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_10_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_11_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_12_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_13_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_14_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_15_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_16_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_17_config»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::consts::alpha» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::bn254::consts::x5_4_config» (List.mem_cons_self))))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms config5
theorem config : «poseidon-0.0.0::poseidon::config» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::config» ∈ «poseidon-0.0.0».Poseidon.Mod.env.functions := by
    change «poseidon-0.0.0::poseidon::config» ∈ [«poseidon-0.0.0::poseidon::config», «poseidon-0.0.0::poseidon::permute», «poseidon-0.0.0::poseidon::apply_matrix», «poseidon-0.0.0::poseidon::absorb», «poseidon-0.0.0::poseidon::sigma»]
    exact List.mem_cons_self
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms config
theorem alpha : «poseidon-0.0.0::poseidon::bn254::consts::alpha» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::bn254::consts::alpha» ∈ «poseidon-0.0.0».Poseidon.Bn254.Consts.env.functions := by
    change «poseidon-0.0.0::poseidon::bn254::consts::alpha» ∈ [«poseidon-0.0.0::poseidon::bn254::consts::alpha», «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_4_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_6_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_7_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_8_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_9_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_10_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_11_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_12_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_13_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_14_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_15_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_16_config», «poseidon-0.0.0::poseidon::bn254::consts::x5_17_config»]
    exact List.mem_cons_self
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms alpha
theorem pow : «std-1.0.0-beta.21::field::pow_32» ∈ «deposit-0.0.0».env.functions := by
  have h : «std-1.0.0-beta.21::field::pow_32» ∈ «std-1.0.0-beta.21».Field.Mod.env.functions := by
    change «std-1.0.0-beta.21::field::pow_32» ∈ [«std-1.0.0-beta.21::field::assert_max_bit_size», «std-1.0.0-beta.21::field::to_le_bits», «std-1.0.0-beta.21::field::to_be_bits», «std-1.0.0-beta.21::field::to_le_bytes», «std-1.0.0-beta.21::field::to_be_bytes», «std-1.0.0-beta.21::field::to_le_radix», «std-1.0.0-beta.21::field::to_be_radix», «std-1.0.0-beta.21::field::pow_32», «std-1.0.0-beta.21::field::sgn0», «std-1.0.0-beta.21::field::lt», «std-1.0.0-beta.21::field::from_le_bytes», «std-1.0.0-beta.21::field::from_be_bytes», «std-1.0.0-beta.21::field::__field_less_than», «std-1.0.0-beta.21::field::field_less_than», «std-1.0.0-beta.21::field::bytes32_to_field», «std-1.0.0-beta.21::field::lt_fallback», «std-1.0.0-beta.21::field::tests::test_to_be_bits», «std-1.0.0-beta.21::field::tests::test_to_le_bits», «std-1.0.0-beta.21::field::tests::test_to_be_bytes», «std-1.0.0-beta.21::field::tests::test_to_le_bytes», «std-1.0.0-beta.21::field::tests::test_to_be_radix», «std-1.0.0-beta.21::field::tests::test_to_le_radix», «std-1.0.0-beta.21::field::tests::test_to_le_radix_1», «std-1.0.0-beta.21::field::tests::test_to_le_radix_brillig_1», «std-1.0.0-beta.21::field::tests::test_to_le_radix_3», «std-1.0.0-beta.21::field::tests::test_to_le_radix_brillig_3», «std-1.0.0-beta.21::field::tests::test_to_le_radix_512», «std-1.0.0-beta.21::field::tests::not_enough_limbs_brillig», «std-1.0.0-beta.21::field::tests::not_enough_limbs», «std-1.0.0-beta.21::field::tests::test_field_less_than», «std-1.0.0-beta.21::field::tests::test_large_field_values_unconstrained», «std-1.0.0-beta.21::field::tests::test_large_field_values», «std-1.0.0-beta.21::field::tests::test_decomposition_edge_cases», «std-1.0.0-beta.21::field::tests::test_pow_32», «std-1.0.0-beta.21::field::tests::test_sgn0», «std-1.0.0-beta.21::field::tests::test_bit_decomposition_overflow», «std-1.0.0-beta.21::field::tests::test_byte_decomposition_overflow», «std-1.0.0-beta.21::field::tests::test_to_from_be_bytes_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::test_to_from_le_bytes_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::from_le_bits», «std-1.0.0-beta.21::field::tests::from_be_bits», «std-1.0.0-beta.21::field::tests::test_to_from_be_bits_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::test_to_from_le_bits_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::max_bit_size_too_large»]
    exact List.mem_cons_of_mem «std-1.0.0-beta.21::field::assert_max_bit_size» (List.mem_cons_of_mem «std-1.0.0-beta.21::field::to_le_bits» (List.mem_cons_of_mem «std-1.0.0-beta.21::field::to_be_bits» (List.mem_cons_of_mem «std-1.0.0-beta.21::field::to_le_bytes» (List.mem_cons_of_mem «std-1.0.0-beta.21::field::to_be_bytes» (List.mem_cons_of_mem «std-1.0.0-beta.21::field::to_le_radix» (List.mem_cons_of_mem «std-1.0.0-beta.21::field::to_be_radix» (List.mem_cons_self)))))))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms pow
theorem bits : «std-1.0.0-beta.21::field::to_le_bits» ∈ «deposit-0.0.0».env.functions := by
  have h : «std-1.0.0-beta.21::field::to_le_bits» ∈ «std-1.0.0-beta.21».Field.Mod.env.functions := by
    change «std-1.0.0-beta.21::field::to_le_bits» ∈ [«std-1.0.0-beta.21::field::assert_max_bit_size», «std-1.0.0-beta.21::field::to_le_bits», «std-1.0.0-beta.21::field::to_be_bits», «std-1.0.0-beta.21::field::to_le_bytes», «std-1.0.0-beta.21::field::to_be_bytes», «std-1.0.0-beta.21::field::to_le_radix», «std-1.0.0-beta.21::field::to_be_radix», «std-1.0.0-beta.21::field::pow_32», «std-1.0.0-beta.21::field::sgn0», «std-1.0.0-beta.21::field::lt», «std-1.0.0-beta.21::field::from_le_bytes», «std-1.0.0-beta.21::field::from_be_bytes», «std-1.0.0-beta.21::field::__field_less_than», «std-1.0.0-beta.21::field::field_less_than», «std-1.0.0-beta.21::field::bytes32_to_field», «std-1.0.0-beta.21::field::lt_fallback», «std-1.0.0-beta.21::field::tests::test_to_be_bits», «std-1.0.0-beta.21::field::tests::test_to_le_bits», «std-1.0.0-beta.21::field::tests::test_to_be_bytes», «std-1.0.0-beta.21::field::tests::test_to_le_bytes», «std-1.0.0-beta.21::field::tests::test_to_be_radix», «std-1.0.0-beta.21::field::tests::test_to_le_radix», «std-1.0.0-beta.21::field::tests::test_to_le_radix_1», «std-1.0.0-beta.21::field::tests::test_to_le_radix_brillig_1», «std-1.0.0-beta.21::field::tests::test_to_le_radix_3», «std-1.0.0-beta.21::field::tests::test_to_le_radix_brillig_3», «std-1.0.0-beta.21::field::tests::test_to_le_radix_512», «std-1.0.0-beta.21::field::tests::not_enough_limbs_brillig», «std-1.0.0-beta.21::field::tests::not_enough_limbs», «std-1.0.0-beta.21::field::tests::test_field_less_than», «std-1.0.0-beta.21::field::tests::test_large_field_values_unconstrained», «std-1.0.0-beta.21::field::tests::test_large_field_values», «std-1.0.0-beta.21::field::tests::test_decomposition_edge_cases», «std-1.0.0-beta.21::field::tests::test_pow_32», «std-1.0.0-beta.21::field::tests::test_sgn0», «std-1.0.0-beta.21::field::tests::test_bit_decomposition_overflow», «std-1.0.0-beta.21::field::tests::test_byte_decomposition_overflow», «std-1.0.0-beta.21::field::tests::test_to_from_be_bytes_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::test_to_from_le_bytes_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::from_le_bits», «std-1.0.0-beta.21::field::tests::from_be_bits», «std-1.0.0-beta.21::field::tests::test_to_from_be_bits_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::test_to_from_le_bits_bn254_edge_cases», «std-1.0.0-beta.21::field::tests::max_bit_size_too_large»]
    exact List.mem_cons_of_mem «std-1.0.0-beta.21::field::assert_max_bit_size» (List.mem_cons_self)
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms bits
theorem sigma : «poseidon-0.0.0::poseidon::sigma» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::sigma» ∈ «poseidon-0.0.0».Poseidon.Mod.env.functions := by
    change «poseidon-0.0.0::poseidon::sigma» ∈ [«poseidon-0.0.0::poseidon::config», «poseidon-0.0.0::poseidon::permute», «poseidon-0.0.0::poseidon::apply_matrix», «poseidon-0.0.0::poseidon::absorb», «poseidon-0.0.0::poseidon::sigma»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::config» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::permute» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::apply_matrix» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::absorb» (List.mem_cons_self))))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms sigma
theorem matrix : «poseidon-0.0.0::poseidon::apply_matrix» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::apply_matrix» ∈ «poseidon-0.0.0».Poseidon.Mod.env.functions := by
    change «poseidon-0.0.0::poseidon::apply_matrix» ∈ [«poseidon-0.0.0::poseidon::config», «poseidon-0.0.0::poseidon::permute», «poseidon-0.0.0::poseidon::apply_matrix», «poseidon-0.0.0::poseidon::absorb», «poseidon-0.0.0::poseidon::sigma»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::config» (List.mem_cons_of_mem «poseidon-0.0.0::poseidon::permute» (List.mem_cons_self))
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms matrix
theorem permute : «poseidon-0.0.0::poseidon::permute» ∈ «deposit-0.0.0».env.functions := by
  have h : «poseidon-0.0.0::poseidon::permute» ∈ «poseidon-0.0.0».Poseidon.Mod.env.functions := by
    change «poseidon-0.0.0::poseidon::permute» ∈ [«poseidon-0.0.0::poseidon::config», «poseidon-0.0.0::poseidon::permute», «poseidon-0.0.0::poseidon::apply_matrix», «poseidon-0.0.0::poseidon::absorb», «poseidon-0.0.0::poseidon::sigma»]
    exact List.mem_cons_of_mem «poseidon-0.0.0::poseidon::config» (List.mem_cons_self)
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env,
    «std-1.0.0-beta.21».env, Env.functions_append, List.mem_append]
  tauto
#print axioms permute
end Deposit.Members
