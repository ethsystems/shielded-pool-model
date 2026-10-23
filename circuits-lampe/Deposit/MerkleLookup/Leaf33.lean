import «std-1.0.0-beta.21».Extracted.Meta.Ctstring
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
import «binary_merkle_root-0.0.0».Extracted.Lib
import «poseidon-0.0.0».Extracted.Poseidon.Bn254
import «poseidon-0.0.0».Extracted.Poseidon.Bn254.Consts
import «poseidon-0.0.0».Extracted.Poseidon.Bn254.Perm
open Lampe
namespace Deposit.MerkleLookup
theorem hash_2_filter_33 : «std-1.0.0-beta.21».Meta.Ctstring.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_2».name) = [] := by rfl
theorem x5_3_filter_33 : «std-1.0.0-beta.21».Meta.Ctstring.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::perm::x5_3».name) = [] := by rfl
theorem x5_3_config_filter_33 : «std-1.0.0-beta.21».Meta.Ctstring.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config».name) = [] := by rfl
theorem bmr_filter_33 : «std-1.0.0-beta.21».Meta.Ctstring.env.functions.filter (fun d => d.name == «binary_merkle_root-0.0.0::binary_merkle_root».name) = [] := by rfl
end Deposit.MerkleLookup
