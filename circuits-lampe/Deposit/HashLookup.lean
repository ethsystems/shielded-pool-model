import Deposit.HashLookup.Leaf0
import Deposit.HashLookup.Leaf1
import Deposit.HashLookup.Leaf2
import Deposit.HashLookup.Leaf3
import Deposit.HashLookup.Leaf4
import Deposit.HashLookup.Leaf5
import Deposit.HashLookup.Leaf6
import Deposit.HashLookup.Leaf7
import Deposit.HashLookup.Leaf8
import Deposit.HashLookup.Leaf9
import Deposit.HashLookup.Leaf10
import Deposit.HashLookup.Leaf11
import Deposit.HashLookup.Leaf12
import Deposit.HashLookup.Leaf13
import Deposit.HashLookup.Leaf14
import Deposit.HashLookup.Leaf15
import Deposit.HashLookup.Leaf16
import Deposit.HashLookup.Leaf17
import Deposit.HashLookup.Leaf18
import Deposit.HashLookup.Leaf19
import Deposit.HashLookup.Leaf20
import Deposit.HashLookup.Leaf21
import Deposit.HashLookup.Leaf22
import Deposit.HashLookup.Leaf23
import Deposit.HashLookup.Leaf24
import Deposit.HashLookup.Leaf25
import Deposit.HashLookup.Leaf26
import Deposit.HashLookup.Leaf27
import Deposit.HashLookup.Leaf28
import Deposit.HashLookup.Leaf29
import Deposit.HashLookup.Leaf30
import Deposit.HashLookup.Leaf31
import Deposit.HashLookup.Leaf32
import Deposit.HashLookup.Leaf33
import Deposit.HashLookup.Leaf34
import Deposit.HashLookup.Leaf35
import Deposit.HashLookup.Leaf36
import Deposit.HashLookup.Leaf37
import Deposit.HashLookup.Leaf38
import Deposit.HashLookup.Leaf39
import Deposit.HashLookup.Leaf40
import Deposit.HashLookup.Leaf41
import Deposit.HashLookup.Leaf42
import Deposit.HashLookup.Leaf43
import Deposit.HashLookup.Leaf44
import Deposit.HashLookup.Leaf45
import Deposit.HashLookup.Leaf46
import Deposit.HashLookup.Leaf47
import Deposit.HashLookup.Leaf48
import Deposit.HashLookup.Leaf49
import Deposit.HashLookup.Leaf50
import Deposit.HashLookup.Leaf51
import Deposit.HashLookup.Leaf52
import Deposit.HashLookup.Leaf53
import Deposit.HashLookup.Leaf54
import Deposit.HashLookup.Leaf55
import Deposit.HashLookup.Leaf56
import Deposit.HashLookup.Leaf57
import Deposit.HashLookup.Leaf58
import «deposit-0.0.0».Extracted
import Deposit.Range
open Lampe
namespace Deposit.HashLookup
theorem hash_1_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_1».name) = [«poseidon-0.0.0::poseidon::bn254::hash_1»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, hash_1_filter_0, hash_1_filter_1, hash_1_filter_2, hash_1_filter_3, hash_1_filter_4, hash_1_filter_5, hash_1_filter_6, hash_1_filter_7, hash_1_filter_8, hash_1_filter_9, hash_1_filter_10, hash_1_filter_11, hash_1_filter_12, hash_1_filter_13, hash_1_filter_14, hash_1_filter_15, hash_1_filter_16, hash_1_filter_17, hash_1_filter_18, hash_1_filter_19, hash_1_filter_20, hash_1_filter_21, hash_1_filter_22, hash_1_filter_23, hash_1_filter_24, hash_1_filter_25, hash_1_filter_26, hash_1_filter_27, hash_1_filter_28, hash_1_filter_29, hash_1_filter_30, hash_1_filter_31, hash_1_filter_32, hash_1_filter_33, hash_1_filter_34, hash_1_filter_35, hash_1_filter_36, hash_1_filter_37, hash_1_filter_38, hash_1_filter_39, hash_1_filter_40, hash_1_filter_41, hash_1_filter_42, hash_1_filter_43, hash_1_filter_44, hash_1_filter_45, hash_1_filter_46, hash_1_filter_47, hash_1_filter_48, hash_1_filter_49, hash_1_filter_50, hash_1_filter_51, hash_1_filter_52, hash_1_filter_53, hash_1_filter_54, hash_1_filter_55, hash_1_filter_56, hash_1_filter_57, hash_1_filter_58, List.nil_append, List.append_nil]
theorem hash_1_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::hash_1» :=
  Deposit.Range.unique_of_filter (n := 1) hash_1_filter
#print axioms hash_1_filter
#print axioms hash_1_unique
theorem hash_4_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_4».name) = [«poseidon-0.0.0::poseidon::bn254::hash_4»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, hash_4_filter_0, hash_4_filter_1, hash_4_filter_2, hash_4_filter_3, hash_4_filter_4, hash_4_filter_5, hash_4_filter_6, hash_4_filter_7, hash_4_filter_8, hash_4_filter_9, hash_4_filter_10, hash_4_filter_11, hash_4_filter_12, hash_4_filter_13, hash_4_filter_14, hash_4_filter_15, hash_4_filter_16, hash_4_filter_17, hash_4_filter_18, hash_4_filter_19, hash_4_filter_20, hash_4_filter_21, hash_4_filter_22, hash_4_filter_23, hash_4_filter_24, hash_4_filter_25, hash_4_filter_26, hash_4_filter_27, hash_4_filter_28, hash_4_filter_29, hash_4_filter_30, hash_4_filter_31, hash_4_filter_32, hash_4_filter_33, hash_4_filter_34, hash_4_filter_35, hash_4_filter_36, hash_4_filter_37, hash_4_filter_38, hash_4_filter_39, hash_4_filter_40, hash_4_filter_41, hash_4_filter_42, hash_4_filter_43, hash_4_filter_44, hash_4_filter_45, hash_4_filter_46, hash_4_filter_47, hash_4_filter_48, hash_4_filter_49, hash_4_filter_50, hash_4_filter_51, hash_4_filter_52, hash_4_filter_53, hash_4_filter_54, hash_4_filter_55, hash_4_filter_56, hash_4_filter_57, hash_4_filter_58, List.nil_append, List.append_nil]
theorem hash_4_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::hash_4» :=
  Deposit.Range.unique_of_filter (n := 1) hash_4_filter
#print axioms hash_4_filter
#print axioms hash_4_unique
theorem hash_internal_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_internal».name) = [«poseidon-0.0.0::poseidon::bn254::hash_internal»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, hash_internal_filter_0, hash_internal_filter_1, hash_internal_filter_2, hash_internal_filter_3, hash_internal_filter_4, hash_internal_filter_5, hash_internal_filter_6, hash_internal_filter_7, hash_internal_filter_8, hash_internal_filter_9, hash_internal_filter_10, hash_internal_filter_11, hash_internal_filter_12, hash_internal_filter_13, hash_internal_filter_14, hash_internal_filter_15, hash_internal_filter_16, hash_internal_filter_17, hash_internal_filter_18, hash_internal_filter_19, hash_internal_filter_20, hash_internal_filter_21, hash_internal_filter_22, hash_internal_filter_23, hash_internal_filter_24, hash_internal_filter_25, hash_internal_filter_26, hash_internal_filter_27, hash_internal_filter_28, hash_internal_filter_29, hash_internal_filter_30, hash_internal_filter_31, hash_internal_filter_32, hash_internal_filter_33, hash_internal_filter_34, hash_internal_filter_35, hash_internal_filter_36, hash_internal_filter_37, hash_internal_filter_38, hash_internal_filter_39, hash_internal_filter_40, hash_internal_filter_41, hash_internal_filter_42, hash_internal_filter_43, hash_internal_filter_44, hash_internal_filter_45, hash_internal_filter_46, hash_internal_filter_47, hash_internal_filter_48, hash_internal_filter_49, hash_internal_filter_50, hash_internal_filter_51, hash_internal_filter_52, hash_internal_filter_53, hash_internal_filter_54, hash_internal_filter_55, hash_internal_filter_56, hash_internal_filter_57, hash_internal_filter_58, List.nil_append, List.append_nil]
theorem hash_internal_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::hash_internal» :=
  Deposit.Range.unique_of_filter (n := 1) hash_internal_filter
#print axioms hash_internal_filter
#print axioms hash_internal_unique
theorem x5_2_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::perm::x5_2».name) = [«poseidon-0.0.0::poseidon::bn254::perm::x5_2»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, x5_2_filter_0, x5_2_filter_1, x5_2_filter_2, x5_2_filter_3, x5_2_filter_4, x5_2_filter_5, x5_2_filter_6, x5_2_filter_7, x5_2_filter_8, x5_2_filter_9, x5_2_filter_10, x5_2_filter_11, x5_2_filter_12, x5_2_filter_13, x5_2_filter_14, x5_2_filter_15, x5_2_filter_16, x5_2_filter_17, x5_2_filter_18, x5_2_filter_19, x5_2_filter_20, x5_2_filter_21, x5_2_filter_22, x5_2_filter_23, x5_2_filter_24, x5_2_filter_25, x5_2_filter_26, x5_2_filter_27, x5_2_filter_28, x5_2_filter_29, x5_2_filter_30, x5_2_filter_31, x5_2_filter_32, x5_2_filter_33, x5_2_filter_34, x5_2_filter_35, x5_2_filter_36, x5_2_filter_37, x5_2_filter_38, x5_2_filter_39, x5_2_filter_40, x5_2_filter_41, x5_2_filter_42, x5_2_filter_43, x5_2_filter_44, x5_2_filter_45, x5_2_filter_46, x5_2_filter_47, x5_2_filter_48, x5_2_filter_49, x5_2_filter_50, x5_2_filter_51, x5_2_filter_52, x5_2_filter_53, x5_2_filter_54, x5_2_filter_55, x5_2_filter_56, x5_2_filter_57, x5_2_filter_58, List.nil_append, List.append_nil]
theorem x5_2_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::perm::x5_2» :=
  Deposit.Range.unique_of_filter (n := 1) x5_2_filter
#print axioms x5_2_filter
#print axioms x5_2_unique
theorem x5_5_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::perm::x5_5».name) = [«poseidon-0.0.0::poseidon::bn254::perm::x5_5»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, x5_5_filter_0, x5_5_filter_1, x5_5_filter_2, x5_5_filter_3, x5_5_filter_4, x5_5_filter_5, x5_5_filter_6, x5_5_filter_7, x5_5_filter_8, x5_5_filter_9, x5_5_filter_10, x5_5_filter_11, x5_5_filter_12, x5_5_filter_13, x5_5_filter_14, x5_5_filter_15, x5_5_filter_16, x5_5_filter_17, x5_5_filter_18, x5_5_filter_19, x5_5_filter_20, x5_5_filter_21, x5_5_filter_22, x5_5_filter_23, x5_5_filter_24, x5_5_filter_25, x5_5_filter_26, x5_5_filter_27, x5_5_filter_28, x5_5_filter_29, x5_5_filter_30, x5_5_filter_31, x5_5_filter_32, x5_5_filter_33, x5_5_filter_34, x5_5_filter_35, x5_5_filter_36, x5_5_filter_37, x5_5_filter_38, x5_5_filter_39, x5_5_filter_40, x5_5_filter_41, x5_5_filter_42, x5_5_filter_43, x5_5_filter_44, x5_5_filter_45, x5_5_filter_46, x5_5_filter_47, x5_5_filter_48, x5_5_filter_49, x5_5_filter_50, x5_5_filter_51, x5_5_filter_52, x5_5_filter_53, x5_5_filter_54, x5_5_filter_55, x5_5_filter_56, x5_5_filter_57, x5_5_filter_58, List.nil_append, List.append_nil]
theorem x5_5_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::perm::x5_5» :=
  Deposit.Range.unique_of_filter (n := 1) x5_5_filter
#print axioms x5_5_filter
#print axioms x5_5_unique
theorem x5_2_config_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config».name) = [«poseidon-0.0.0::poseidon::bn254::consts::x5_2_config»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, x5_2_config_filter_0, x5_2_config_filter_1, x5_2_config_filter_2, x5_2_config_filter_3, x5_2_config_filter_4, x5_2_config_filter_5, x5_2_config_filter_6, x5_2_config_filter_7, x5_2_config_filter_8, x5_2_config_filter_9, x5_2_config_filter_10, x5_2_config_filter_11, x5_2_config_filter_12, x5_2_config_filter_13, x5_2_config_filter_14, x5_2_config_filter_15, x5_2_config_filter_16, x5_2_config_filter_17, x5_2_config_filter_18, x5_2_config_filter_19, x5_2_config_filter_20, x5_2_config_filter_21, x5_2_config_filter_22, x5_2_config_filter_23, x5_2_config_filter_24, x5_2_config_filter_25, x5_2_config_filter_26, x5_2_config_filter_27, x5_2_config_filter_28, x5_2_config_filter_29, x5_2_config_filter_30, x5_2_config_filter_31, x5_2_config_filter_32, x5_2_config_filter_33, x5_2_config_filter_34, x5_2_config_filter_35, x5_2_config_filter_36, x5_2_config_filter_37, x5_2_config_filter_38, x5_2_config_filter_39, x5_2_config_filter_40, x5_2_config_filter_41, x5_2_config_filter_42, x5_2_config_filter_43, x5_2_config_filter_44, x5_2_config_filter_45, x5_2_config_filter_46, x5_2_config_filter_47, x5_2_config_filter_48, x5_2_config_filter_49, x5_2_config_filter_50, x5_2_config_filter_51, x5_2_config_filter_52, x5_2_config_filter_53, x5_2_config_filter_54, x5_2_config_filter_55, x5_2_config_filter_56, x5_2_config_filter_57, x5_2_config_filter_58, List.nil_append, List.append_nil]
theorem x5_2_config_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::consts::x5_2_config» :=
  Deposit.Range.unique_of_filter (n := 1) x5_2_config_filter
#print axioms x5_2_config_filter
#print axioms x5_2_config_unique
theorem x5_5_config_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config».name) = [«poseidon-0.0.0::poseidon::bn254::consts::x5_5_config»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, x5_5_config_filter_0, x5_5_config_filter_1, x5_5_config_filter_2, x5_5_config_filter_3, x5_5_config_filter_4, x5_5_config_filter_5, x5_5_config_filter_6, x5_5_config_filter_7, x5_5_config_filter_8, x5_5_config_filter_9, x5_5_config_filter_10, x5_5_config_filter_11, x5_5_config_filter_12, x5_5_config_filter_13, x5_5_config_filter_14, x5_5_config_filter_15, x5_5_config_filter_16, x5_5_config_filter_17, x5_5_config_filter_18, x5_5_config_filter_19, x5_5_config_filter_20, x5_5_config_filter_21, x5_5_config_filter_22, x5_5_config_filter_23, x5_5_config_filter_24, x5_5_config_filter_25, x5_5_config_filter_26, x5_5_config_filter_27, x5_5_config_filter_28, x5_5_config_filter_29, x5_5_config_filter_30, x5_5_config_filter_31, x5_5_config_filter_32, x5_5_config_filter_33, x5_5_config_filter_34, x5_5_config_filter_35, x5_5_config_filter_36, x5_5_config_filter_37, x5_5_config_filter_38, x5_5_config_filter_39, x5_5_config_filter_40, x5_5_config_filter_41, x5_5_config_filter_42, x5_5_config_filter_43, x5_5_config_filter_44, x5_5_config_filter_45, x5_5_config_filter_46, x5_5_config_filter_47, x5_5_config_filter_48, x5_5_config_filter_49, x5_5_config_filter_50, x5_5_config_filter_51, x5_5_config_filter_52, x5_5_config_filter_53, x5_5_config_filter_54, x5_5_config_filter_55, x5_5_config_filter_56, x5_5_config_filter_57, x5_5_config_filter_58, List.nil_append, List.append_nil]
theorem x5_5_config_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::consts::x5_5_config» :=
  Deposit.Range.unique_of_filter (n := 1) x5_5_config_filter
#print axioms x5_5_config_filter
#print axioms x5_5_config_unique
theorem alpha_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::alpha».name) = [«poseidon-0.0.0::poseidon::bn254::consts::alpha»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, alpha_filter_0, alpha_filter_1, alpha_filter_2, alpha_filter_3, alpha_filter_4, alpha_filter_5, alpha_filter_6, alpha_filter_7, alpha_filter_8, alpha_filter_9, alpha_filter_10, alpha_filter_11, alpha_filter_12, alpha_filter_13, alpha_filter_14, alpha_filter_15, alpha_filter_16, alpha_filter_17, alpha_filter_18, alpha_filter_19, alpha_filter_20, alpha_filter_21, alpha_filter_22, alpha_filter_23, alpha_filter_24, alpha_filter_25, alpha_filter_26, alpha_filter_27, alpha_filter_28, alpha_filter_29, alpha_filter_30, alpha_filter_31, alpha_filter_32, alpha_filter_33, alpha_filter_34, alpha_filter_35, alpha_filter_36, alpha_filter_37, alpha_filter_38, alpha_filter_39, alpha_filter_40, alpha_filter_41, alpha_filter_42, alpha_filter_43, alpha_filter_44, alpha_filter_45, alpha_filter_46, alpha_filter_47, alpha_filter_48, alpha_filter_49, alpha_filter_50, alpha_filter_51, alpha_filter_52, alpha_filter_53, alpha_filter_54, alpha_filter_55, alpha_filter_56, alpha_filter_57, alpha_filter_58, List.nil_append, List.append_nil]
theorem alpha_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::consts::alpha» :=
  Deposit.Range.unique_of_filter (n := 1) alpha_filter
#print axioms alpha_filter
#print axioms alpha_unique
theorem permute_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::permute».name) = [«poseidon-0.0.0::poseidon::permute»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, permute_filter_0, permute_filter_1, permute_filter_2, permute_filter_3, permute_filter_4, permute_filter_5, permute_filter_6, permute_filter_7, permute_filter_8, permute_filter_9, permute_filter_10, permute_filter_11, permute_filter_12, permute_filter_13, permute_filter_14, permute_filter_15, permute_filter_16, permute_filter_17, permute_filter_18, permute_filter_19, permute_filter_20, permute_filter_21, permute_filter_22, permute_filter_23, permute_filter_24, permute_filter_25, permute_filter_26, permute_filter_27, permute_filter_28, permute_filter_29, permute_filter_30, permute_filter_31, permute_filter_32, permute_filter_33, permute_filter_34, permute_filter_35, permute_filter_36, permute_filter_37, permute_filter_38, permute_filter_39, permute_filter_40, permute_filter_41, permute_filter_42, permute_filter_43, permute_filter_44, permute_filter_45, permute_filter_46, permute_filter_47, permute_filter_48, permute_filter_49, permute_filter_50, permute_filter_51, permute_filter_52, permute_filter_53, permute_filter_54, permute_filter_55, permute_filter_56, permute_filter_57, permute_filter_58, List.nil_append, List.append_nil]
theorem permute_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::permute» :=
  Deposit.Range.unique_of_filter (n := 1) permute_filter
#print axioms permute_filter
#print axioms permute_unique
theorem sigma_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::sigma».name) = [«poseidon-0.0.0::poseidon::sigma»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, sigma_filter_0, sigma_filter_1, sigma_filter_2, sigma_filter_3, sigma_filter_4, sigma_filter_5, sigma_filter_6, sigma_filter_7, sigma_filter_8, sigma_filter_9, sigma_filter_10, sigma_filter_11, sigma_filter_12, sigma_filter_13, sigma_filter_14, sigma_filter_15, sigma_filter_16, sigma_filter_17, sigma_filter_18, sigma_filter_19, sigma_filter_20, sigma_filter_21, sigma_filter_22, sigma_filter_23, sigma_filter_24, sigma_filter_25, sigma_filter_26, sigma_filter_27, sigma_filter_28, sigma_filter_29, sigma_filter_30, sigma_filter_31, sigma_filter_32, sigma_filter_33, sigma_filter_34, sigma_filter_35, sigma_filter_36, sigma_filter_37, sigma_filter_38, sigma_filter_39, sigma_filter_40, sigma_filter_41, sigma_filter_42, sigma_filter_43, sigma_filter_44, sigma_filter_45, sigma_filter_46, sigma_filter_47, sigma_filter_48, sigma_filter_49, sigma_filter_50, sigma_filter_51, sigma_filter_52, sigma_filter_53, sigma_filter_54, sigma_filter_55, sigma_filter_56, sigma_filter_57, sigma_filter_58, List.nil_append, List.append_nil]
theorem sigma_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::sigma» :=
  Deposit.Range.unique_of_filter (n := 1) sigma_filter
#print axioms sigma_filter
#print axioms sigma_unique
theorem apply_matrix_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::apply_matrix».name) = [«poseidon-0.0.0::poseidon::apply_matrix»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, apply_matrix_filter_0, apply_matrix_filter_1, apply_matrix_filter_2, apply_matrix_filter_3, apply_matrix_filter_4, apply_matrix_filter_5, apply_matrix_filter_6, apply_matrix_filter_7, apply_matrix_filter_8, apply_matrix_filter_9, apply_matrix_filter_10, apply_matrix_filter_11, apply_matrix_filter_12, apply_matrix_filter_13, apply_matrix_filter_14, apply_matrix_filter_15, apply_matrix_filter_16, apply_matrix_filter_17, apply_matrix_filter_18, apply_matrix_filter_19, apply_matrix_filter_20, apply_matrix_filter_21, apply_matrix_filter_22, apply_matrix_filter_23, apply_matrix_filter_24, apply_matrix_filter_25, apply_matrix_filter_26, apply_matrix_filter_27, apply_matrix_filter_28, apply_matrix_filter_29, apply_matrix_filter_30, apply_matrix_filter_31, apply_matrix_filter_32, apply_matrix_filter_33, apply_matrix_filter_34, apply_matrix_filter_35, apply_matrix_filter_36, apply_matrix_filter_37, apply_matrix_filter_38, apply_matrix_filter_39, apply_matrix_filter_40, apply_matrix_filter_41, apply_matrix_filter_42, apply_matrix_filter_43, apply_matrix_filter_44, apply_matrix_filter_45, apply_matrix_filter_46, apply_matrix_filter_47, apply_matrix_filter_48, apply_matrix_filter_49, apply_matrix_filter_50, apply_matrix_filter_51, apply_matrix_filter_52, apply_matrix_filter_53, apply_matrix_filter_54, apply_matrix_filter_55, apply_matrix_filter_56, apply_matrix_filter_57, apply_matrix_filter_58, List.nil_append, List.append_nil]
theorem apply_matrix_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::apply_matrix» :=
  Deposit.Range.unique_of_filter (n := 1) apply_matrix_filter
#print axioms apply_matrix_filter
#print axioms apply_matrix_unique
theorem pow_32_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «std-1.0.0-beta.21::field::pow_32».name) = List.replicate 3 «std-1.0.0-beta.21::field::pow_32» := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, pow_32_filter_0, pow_32_filter_1, pow_32_filter_2, pow_32_filter_3, pow_32_filter_4, pow_32_filter_5, pow_32_filter_6, pow_32_filter_7, pow_32_filter_8, pow_32_filter_9, pow_32_filter_10, pow_32_filter_11, pow_32_filter_12, pow_32_filter_13, pow_32_filter_14, pow_32_filter_15, pow_32_filter_16, pow_32_filter_17, pow_32_filter_18, pow_32_filter_19, pow_32_filter_20, pow_32_filter_21, pow_32_filter_22, pow_32_filter_23, pow_32_filter_24, pow_32_filter_25, pow_32_filter_26, pow_32_filter_27, pow_32_filter_28, pow_32_filter_29, pow_32_filter_30, pow_32_filter_31, pow_32_filter_32, pow_32_filter_33, pow_32_filter_34, pow_32_filter_35, pow_32_filter_36, pow_32_filter_37, pow_32_filter_38, pow_32_filter_39, pow_32_filter_40, pow_32_filter_41, pow_32_filter_42, pow_32_filter_43, pow_32_filter_44, pow_32_filter_45, pow_32_filter_46, pow_32_filter_47, pow_32_filter_48, pow_32_filter_49, pow_32_filter_50, pow_32_filter_51, pow_32_filter_52, pow_32_filter_53, pow_32_filter_54, pow_32_filter_55, pow_32_filter_56, pow_32_filter_57, pow_32_filter_58, List.nil_append, List.append_nil]
  rfl
theorem pow_32_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «std-1.0.0-beta.21::field::pow_32» :=
  Deposit.Range.unique_of_filter (n := 3) pow_32_filter
#print axioms pow_32_filter
#print axioms pow_32_unique
theorem to_le_bits_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «std-1.0.0-beta.21::field::to_le_bits».name) = List.replicate 3 «std-1.0.0-beta.21::field::to_le_bits» := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, to_le_bits_filter_0, to_le_bits_filter_1, to_le_bits_filter_2, to_le_bits_filter_3, to_le_bits_filter_4, to_le_bits_filter_5, to_le_bits_filter_6, to_le_bits_filter_7, to_le_bits_filter_8, to_le_bits_filter_9, to_le_bits_filter_10, to_le_bits_filter_11, to_le_bits_filter_12, to_le_bits_filter_13, to_le_bits_filter_14, to_le_bits_filter_15, to_le_bits_filter_16, to_le_bits_filter_17, to_le_bits_filter_18, to_le_bits_filter_19, to_le_bits_filter_20, to_le_bits_filter_21, to_le_bits_filter_22, to_le_bits_filter_23, to_le_bits_filter_24, to_le_bits_filter_25, to_le_bits_filter_26, to_le_bits_filter_27, to_le_bits_filter_28, to_le_bits_filter_29, to_le_bits_filter_30, to_le_bits_filter_31, to_le_bits_filter_32, to_le_bits_filter_33, to_le_bits_filter_34, to_le_bits_filter_35, to_le_bits_filter_36, to_le_bits_filter_37, to_le_bits_filter_38, to_le_bits_filter_39, to_le_bits_filter_40, to_le_bits_filter_41, to_le_bits_filter_42, to_le_bits_filter_43, to_le_bits_filter_44, to_le_bits_filter_45, to_le_bits_filter_46, to_le_bits_filter_47, to_le_bits_filter_48, to_le_bits_filter_49, to_le_bits_filter_50, to_le_bits_filter_51, to_le_bits_filter_52, to_le_bits_filter_53, to_le_bits_filter_54, to_le_bits_filter_55, to_le_bits_filter_56, to_le_bits_filter_57, to_le_bits_filter_58, List.nil_append, List.append_nil]
  rfl
theorem to_le_bits_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «std-1.0.0-beta.21::field::to_le_bits» :=
  Deposit.Range.unique_of_filter (n := 3) to_le_bits_filter
#print axioms to_le_bits_filter
#print axioms to_le_bits_unique
theorem poseidon4_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «deposit-0.0.0::poseidon4».name) = [«deposit-0.0.0::poseidon4»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, poseidon4_filter_0, poseidon4_filter_1, poseidon4_filter_2, poseidon4_filter_3, poseidon4_filter_4, poseidon4_filter_5, poseidon4_filter_6, poseidon4_filter_7, poseidon4_filter_8, poseidon4_filter_9, poseidon4_filter_10, poseidon4_filter_11, poseidon4_filter_12, poseidon4_filter_13, poseidon4_filter_14, poseidon4_filter_15, poseidon4_filter_16, poseidon4_filter_17, poseidon4_filter_18, poseidon4_filter_19, poseidon4_filter_20, poseidon4_filter_21, poseidon4_filter_22, poseidon4_filter_23, poseidon4_filter_24, poseidon4_filter_25, poseidon4_filter_26, poseidon4_filter_27, poseidon4_filter_28, poseidon4_filter_29, poseidon4_filter_30, poseidon4_filter_31, poseidon4_filter_32, poseidon4_filter_33, poseidon4_filter_34, poseidon4_filter_35, poseidon4_filter_36, poseidon4_filter_37, poseidon4_filter_38, poseidon4_filter_39, poseidon4_filter_40, poseidon4_filter_41, poseidon4_filter_42, poseidon4_filter_43, poseidon4_filter_44, poseidon4_filter_45, poseidon4_filter_46, poseidon4_filter_47, poseidon4_filter_48, poseidon4_filter_49, poseidon4_filter_50, poseidon4_filter_51, poseidon4_filter_52, poseidon4_filter_53, poseidon4_filter_54, poseidon4_filter_55, poseidon4_filter_56, poseidon4_filter_57, poseidon4_filter_58, List.nil_append, List.append_nil]
theorem poseidon4_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «deposit-0.0.0::poseidon4» :=
  Deposit.Range.unique_of_filter (n := 1) poseidon4_filter
#print axioms poseidon4_filter
#print axioms poseidon4_unique
end Deposit.HashLookup
