import «poseidon-0.0.0».Extracted.Poseidon.Bn254.Consts
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
open Lampe
namespace Deposit.MainLookup
theorem range_filter_5 : «poseidon-0.0.0».Poseidon.Bn254.Consts.env.functions.filter (fun d => d.name == «std-1.0.0-beta.21::field::assert_max_bit_size».name) = [] := by rfl
theorem main_filter_5 : «poseidon-0.0.0».Poseidon.Bn254.Consts.env.functions.filter (fun d => d.name == «deposit-0.0.0::main».name) = [] := by rfl
end Deposit.MainLookup
