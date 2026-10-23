import Deposit.MainLookup.Leaf0
import Deposit.MainLookup.Leaf1
import Deposit.MainLookup.Leaf2
import Deposit.MainLookup.Leaf3
import Deposit.MainLookup.Leaf4
import Deposit.MainLookup.Leaf5
import Deposit.MainLookup.Leaf6
import Deposit.MainLookup.Leaf7
import Deposit.MainLookup.Leaf8
import Deposit.MainLookup.Leaf9
import Deposit.MainLookup.Leaf10
import Deposit.MainLookup.Leaf11
import Deposit.MainLookup.Leaf12
import Deposit.MainLookup.Leaf13
import Deposit.MainLookup.Leaf14
import Deposit.MainLookup.Leaf15
import Deposit.MainLookup.Leaf16
import Deposit.MainLookup.Leaf17
import Deposit.MainLookup.Leaf18
import Deposit.MainLookup.Leaf19
import Deposit.MainLookup.Leaf20
import Deposit.MainLookup.Leaf21
import Deposit.MainLookup.Leaf22
import Deposit.MainLookup.Leaf23
import Deposit.MainLookup.Leaf24
import Deposit.MainLookup.Leaf25
import Deposit.MainLookup.Leaf26
import Deposit.MainLookup.Leaf27
import Deposit.MainLookup.Leaf28
import Deposit.MainLookup.Leaf29
import Deposit.MainLookup.Leaf30
import Deposit.MainLookup.Leaf31
import Deposit.MainLookup.Leaf32
import Deposit.MainLookup.Leaf33
import Deposit.MainLookup.Leaf34
import Deposit.MainLookup.Leaf35
import Deposit.MainLookup.Leaf36
import Deposit.MainLookup.Leaf37
import Deposit.MainLookup.Leaf38
import Deposit.MainLookup.Leaf39
import Deposit.MainLookup.Leaf40
import Deposit.MainLookup.Leaf41
import Deposit.MainLookup.Leaf42
import Deposit.MainLookup.Leaf43
import Deposit.MainLookup.Leaf44
import Deposit.MainLookup.Leaf45
import Deposit.MainLookup.Leaf46
import Deposit.MainLookup.Leaf47
import Deposit.MainLookup.Leaf48
import Deposit.MainLookup.Leaf49
import Deposit.MainLookup.Leaf50
import Deposit.MainLookup.Leaf51
import Deposit.MainLookup.Leaf52
import Deposit.MainLookup.Leaf53
import Deposit.MainLookup.Leaf54
import Deposit.MainLookup.Leaf55
import Deposit.MainLookup.Leaf56
import Deposit.MainLookup.Leaf57
import Deposit.MainLookup.Leaf58
import «deposit-0.0.0».Extracted
open Lampe
namespace Deposit.MainLookup
theorem range_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «std-1.0.0-beta.21::field::assert_max_bit_size».name) = List.replicate 3 «std-1.0.0-beta.21::field::assert_max_bit_size» := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, range_filter_0, range_filter_1, range_filter_2, range_filter_3, range_filter_4, range_filter_5, range_filter_6, range_filter_7, range_filter_8, range_filter_9, range_filter_10, range_filter_11, range_filter_12, range_filter_13, range_filter_14, range_filter_15, range_filter_16, range_filter_17, range_filter_18, range_filter_19, range_filter_20, range_filter_21, range_filter_22, range_filter_23, range_filter_24, range_filter_25, range_filter_26, range_filter_27, range_filter_28, range_filter_29, range_filter_30, range_filter_31, range_filter_32, range_filter_33, range_filter_34, range_filter_35, range_filter_36, range_filter_37, range_filter_38, range_filter_39, range_filter_40, range_filter_41, range_filter_42, range_filter_43, range_filter_44, range_filter_45, range_filter_46, range_filter_47, range_filter_48, range_filter_49, range_filter_50, range_filter_51, range_filter_52, range_filter_53, range_filter_54, range_filter_55, range_filter_56, range_filter_57, range_filter_58, List.nil_append, List.append_nil]
  rfl
#print axioms range_filter
theorem main_filter : «deposit-0.0.0».env.functions.filter (fun d => d.name == «deposit-0.0.0::main».name) = [«deposit-0.0.0::main»] := by
  simp only [«deposit-0.0.0».env, «binary_merkle_root-0.0.0».env, «poseidon-0.0.0».env, «std-1.0.0-beta.21».env, Env.functions_append, List.filter_append, main_filter_0, main_filter_1, main_filter_2, main_filter_3, main_filter_4, main_filter_5, main_filter_6, main_filter_7, main_filter_8, main_filter_9, main_filter_10, main_filter_11, main_filter_12, main_filter_13, main_filter_14, main_filter_15, main_filter_16, main_filter_17, main_filter_18, main_filter_19, main_filter_20, main_filter_21, main_filter_22, main_filter_23, main_filter_24, main_filter_25, main_filter_26, main_filter_27, main_filter_28, main_filter_29, main_filter_30, main_filter_31, main_filter_32, main_filter_33, main_filter_34, main_filter_35, main_filter_36, main_filter_37, main_filter_38, main_filter_39, main_filter_40, main_filter_41, main_filter_42, main_filter_43, main_filter_44, main_filter_45, main_filter_46, main_filter_47, main_filter_48, main_filter_49, main_filter_50, main_filter_51, main_filter_52, main_filter_53, main_filter_54, main_filter_55, main_filter_56, main_filter_57, main_filter_58, List.nil_append, List.append_nil]
#print axioms main_filter
end Deposit.MainLookup
