import Deposit.MerkleLookup.Leaf0
import Deposit.MerkleLookup.Leaf1
import Deposit.MerkleLookup.Leaf2
import Deposit.MerkleLookup.Leaf3
import Deposit.MerkleLookup.Leaf4
import Deposit.MerkleLookup.Leaf5
import Deposit.MerkleLookup.Leaf6
import Deposit.MerkleLookup.Leaf7
import Deposit.MerkleLookup.Leaf8
import Deposit.MerkleLookup.Leaf9
import Deposit.MerkleLookup.Leaf10
import Deposit.MerkleLookup.Leaf11
import Deposit.MerkleLookup.Leaf12
import Deposit.MerkleLookup.Leaf13
import Deposit.MerkleLookup.Leaf14
import Deposit.MerkleLookup.Leaf15
import Deposit.MerkleLookup.Leaf16
import Deposit.MerkleLookup.Leaf17
import Deposit.MerkleLookup.Leaf18
import Deposit.MerkleLookup.Leaf19
import Deposit.MerkleLookup.Leaf20
import Deposit.MerkleLookup.Leaf21
import Deposit.MerkleLookup.Leaf22
import Deposit.MerkleLookup.Leaf23
import Deposit.MerkleLookup.Leaf24
import Deposit.MerkleLookup.Leaf25
import Deposit.MerkleLookup.Leaf26
import Deposit.MerkleLookup.Leaf27
import Deposit.MerkleLookup.Leaf28
import Deposit.MerkleLookup.Leaf29
import Deposit.MerkleLookup.Leaf30
import Deposit.MerkleLookup.Leaf31
import Deposit.MerkleLookup.Leaf32
import Deposit.MerkleLookup.Leaf33
import Deposit.MerkleLookup.Leaf34
import Deposit.MerkleLookup.Leaf35
import Deposit.MerkleLookup.Leaf36
import Deposit.MerkleLookup.Leaf37
import Deposit.MerkleLookup.Leaf38
import Deposit.MerkleLookup.Leaf39
import Deposit.MerkleLookup.Leaf40
import Deposit.MerkleLookup.Leaf41
import Deposit.MerkleLookup.Leaf42
import Deposit.MerkleLookup.Leaf43
import Deposit.MerkleLookup.Leaf44
import Deposit.MerkleLookup.Leaf45
import Deposit.MerkleLookup.Leaf46
import Deposit.MerkleLookup.Leaf47
import Deposit.MerkleLookup.Leaf48
import Deposit.MerkleLookup.Leaf49
import Deposit.MerkleLookup.Leaf50
import Deposit.MerkleLookup.Leaf51
import Deposit.MerkleLookup.Leaf52
import Deposit.MerkleLookup.Leaf53
import Deposit.MerkleLookup.Leaf54
import Deposit.MerkleLookup.Leaf55
import Deposit.MerkleLookup.Leaf56
import Deposit.MerkleLookup.Leaf57
import Deposit.MerkleLookup.Leaf58
import «deposit-0.0.0».Extracted
import Deposit.Range
open Lampe
namespace Deposit.MerkleLookup
theorem hash_2_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::hash_2».name) = [«poseidon-0.0.0::poseidon::bn254::hash_2»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, hash_2_filter_0, hash_2_filter_1, hash_2_filter_2, hash_2_filter_3, hash_2_filter_4, hash_2_filter_5, hash_2_filter_6, hash_2_filter_7, hash_2_filter_8, hash_2_filter_9, hash_2_filter_10, hash_2_filter_11, hash_2_filter_12, hash_2_filter_13, hash_2_filter_14, hash_2_filter_15, hash_2_filter_16, hash_2_filter_17, hash_2_filter_18, hash_2_filter_19, hash_2_filter_20, hash_2_filter_21, hash_2_filter_22, hash_2_filter_23, hash_2_filter_24, hash_2_filter_25, hash_2_filter_26, hash_2_filter_27, hash_2_filter_28, hash_2_filter_29, hash_2_filter_30, hash_2_filter_31, hash_2_filter_32, hash_2_filter_33, hash_2_filter_34, hash_2_filter_35, hash_2_filter_36, hash_2_filter_37, hash_2_filter_38, hash_2_filter_39, hash_2_filter_40, hash_2_filter_41, hash_2_filter_42, hash_2_filter_43, hash_2_filter_44, hash_2_filter_45, hash_2_filter_46, hash_2_filter_47, hash_2_filter_48, hash_2_filter_49, hash_2_filter_50, hash_2_filter_51, hash_2_filter_52, hash_2_filter_53, hash_2_filter_54, hash_2_filter_55, hash_2_filter_56, hash_2_filter_57, hash_2_filter_58, List.nil_append, List.append_nil]
theorem hash_2_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::hash_2» :=
  Deposit.Range.unique_of_filter (n := 1) hash_2_filter
#print axioms hash_2_filter
#print axioms hash_2_unique
theorem x5_3_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::perm::x5_3».name) = [«poseidon-0.0.0::poseidon::bn254::perm::x5_3»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, x5_3_filter_0, x5_3_filter_1, x5_3_filter_2, x5_3_filter_3, x5_3_filter_4, x5_3_filter_5, x5_3_filter_6, x5_3_filter_7, x5_3_filter_8, x5_3_filter_9, x5_3_filter_10, x5_3_filter_11, x5_3_filter_12, x5_3_filter_13, x5_3_filter_14, x5_3_filter_15, x5_3_filter_16, x5_3_filter_17, x5_3_filter_18, x5_3_filter_19, x5_3_filter_20, x5_3_filter_21, x5_3_filter_22, x5_3_filter_23, x5_3_filter_24, x5_3_filter_25, x5_3_filter_26, x5_3_filter_27, x5_3_filter_28, x5_3_filter_29, x5_3_filter_30, x5_3_filter_31, x5_3_filter_32, x5_3_filter_33, x5_3_filter_34, x5_3_filter_35, x5_3_filter_36, x5_3_filter_37, x5_3_filter_38, x5_3_filter_39, x5_3_filter_40, x5_3_filter_41, x5_3_filter_42, x5_3_filter_43, x5_3_filter_44, x5_3_filter_45, x5_3_filter_46, x5_3_filter_47, x5_3_filter_48, x5_3_filter_49, x5_3_filter_50, x5_3_filter_51, x5_3_filter_52, x5_3_filter_53, x5_3_filter_54, x5_3_filter_55, x5_3_filter_56, x5_3_filter_57, x5_3_filter_58, List.nil_append, List.append_nil]
theorem x5_3_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::perm::x5_3» :=
  Deposit.Range.unique_of_filter (n := 1) x5_3_filter
#print axioms x5_3_filter
#print axioms x5_3_unique
theorem x5_3_config_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config».name) = [«poseidon-0.0.0::poseidon::bn254::consts::x5_3_config»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, x5_3_config_filter_0, x5_3_config_filter_1, x5_3_config_filter_2, x5_3_config_filter_3, x5_3_config_filter_4, x5_3_config_filter_5, x5_3_config_filter_6, x5_3_config_filter_7, x5_3_config_filter_8, x5_3_config_filter_9, x5_3_config_filter_10, x5_3_config_filter_11, x5_3_config_filter_12, x5_3_config_filter_13, x5_3_config_filter_14, x5_3_config_filter_15, x5_3_config_filter_16, x5_3_config_filter_17, x5_3_config_filter_18, x5_3_config_filter_19, x5_3_config_filter_20, x5_3_config_filter_21, x5_3_config_filter_22, x5_3_config_filter_23, x5_3_config_filter_24, x5_3_config_filter_25, x5_3_config_filter_26, x5_3_config_filter_27, x5_3_config_filter_28, x5_3_config_filter_29, x5_3_config_filter_30, x5_3_config_filter_31, x5_3_config_filter_32, x5_3_config_filter_33, x5_3_config_filter_34, x5_3_config_filter_35, x5_3_config_filter_36, x5_3_config_filter_37, x5_3_config_filter_38, x5_3_config_filter_39, x5_3_config_filter_40, x5_3_config_filter_41, x5_3_config_filter_42, x5_3_config_filter_43, x5_3_config_filter_44, x5_3_config_filter_45, x5_3_config_filter_46, x5_3_config_filter_47, x5_3_config_filter_48, x5_3_config_filter_49, x5_3_config_filter_50, x5_3_config_filter_51, x5_3_config_filter_52, x5_3_config_filter_53, x5_3_config_filter_54, x5_3_config_filter_55, x5_3_config_filter_56, x5_3_config_filter_57, x5_3_config_filter_58, List.nil_append, List.append_nil]
theorem x5_3_config_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «poseidon-0.0.0::poseidon::bn254::consts::x5_3_config» :=
  Deposit.Range.unique_of_filter (n := 1) x5_3_config_filter
#print axioms x5_3_config_filter
#print axioms x5_3_config_unique
theorem bmr_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «binary_merkle_root-0.0.0::binary_merkle_root».name) = [«binary_merkle_root-0.0.0::binary_merkle_root»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, bmr_filter_0, bmr_filter_1, bmr_filter_2, bmr_filter_3, bmr_filter_4, bmr_filter_5, bmr_filter_6, bmr_filter_7, bmr_filter_8, bmr_filter_9, bmr_filter_10, bmr_filter_11, bmr_filter_12, bmr_filter_13, bmr_filter_14, bmr_filter_15, bmr_filter_16, bmr_filter_17, bmr_filter_18, bmr_filter_19, bmr_filter_20, bmr_filter_21, bmr_filter_22, bmr_filter_23, bmr_filter_24, bmr_filter_25, bmr_filter_26, bmr_filter_27, bmr_filter_28, bmr_filter_29, bmr_filter_30, bmr_filter_31, bmr_filter_32, bmr_filter_33, bmr_filter_34, bmr_filter_35, bmr_filter_36, bmr_filter_37, bmr_filter_38, bmr_filter_39, bmr_filter_40, bmr_filter_41, bmr_filter_42, bmr_filter_43, bmr_filter_44, bmr_filter_45, bmr_filter_46, bmr_filter_47, bmr_filter_48, bmr_filter_49, bmr_filter_50, bmr_filter_51, bmr_filter_52, bmr_filter_53, bmr_filter_54, bmr_filter_55, bmr_filter_56, bmr_filter_57, bmr_filter_58, List.nil_append, List.append_nil]
theorem bmr_unique : Deposit.Range.UniqueDecl «deposit-0.0.0».env «binary_merkle_root-0.0.0::binary_merkle_root» :=
  Deposit.Range.unique_of_filter (n := 1) bmr_filter
#print axioms bmr_filter
#print axioms bmr_unique
end Deposit.MerkleLookup
