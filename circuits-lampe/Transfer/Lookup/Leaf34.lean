import «std-1.0.0-beta.21».Extracted.Meta.Expr
import «transfer-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
import «binary_merkle_root-0.0.0».Extracted.Lib
import «poseidon-0.0.0».Extracted.Poseidon.Bn254
import «poseidon-0.0.0».Extracted.Poseidon.Bn254.Consts
import «poseidon-0.0.0».Extracted.Poseidon.Bn254.Perm
import «poseidon-0.0.0».Extracted.Poseidon.Mod
open Lampe
namespace Transfer.Lookup
theorem config_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::config».name) = [] := by rfl
theorem permute_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::permute».name) = [] := by rfl
theorem sigma_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::sigma».name) = [] := by rfl
theorem apply_matrix_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::apply_matrix».name) = [] := by rfl
theorem hash_1_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_1».name) = [] := by rfl
theorem hash_2_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_2».name) = [] := by rfl
theorem hash_4_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_4».name) = [] := by rfl
theorem hash_internal_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_internal».name) = [] := by rfl
theorem x5_2_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::perm::x5_2».name) = [] := by rfl
theorem x5_3_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::perm::x5_3».name) = [] := by rfl
theorem x5_5_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::perm::x5_5».name) = [] := by rfl
theorem x5_2_config_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config».name) = [] := by rfl
theorem x5_3_config_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config».name) = [] := by rfl
theorem x5_5_config_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config».name) = [] := by rfl
theorem alpha_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::alpha».name) = [] := by rfl
theorem pow_32_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «std-1.0.0-beta.21::field::pow_32».name) = [] := by rfl
theorem to_le_bits_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «std-1.0.0-beta.21::field::to_le_bits».name) = [] := by rfl
theorem bmr_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «binary_merkle_root-0.0.0::binary_merkle_root».name) = [] := by rfl
theorem main_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «transfer-0.0.0::main».name) = [] := by rfl
theorem vmp_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «transfer-0.0.0::verify_merkle_proof».name) = [] := by rfl
theorem poseidon1_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «transfer-0.0.0::poseidon1».name) = [] := by rfl
theorem poseidon2_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «transfer-0.0.0::poseidon2».name) = [] := by rfl
theorem poseidon4_filter_34 : «std-1.0.0-beta.21».Meta.Expr.env.functions.filter (fun d => d.name == «transfer-0.0.0::poseidon4».name) = [] := by rfl
end Transfer.Lookup
