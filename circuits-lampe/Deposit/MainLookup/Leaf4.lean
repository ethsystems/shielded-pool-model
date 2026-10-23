import «poseidon-0.0.0».Extracted.OracleTests
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
open Lampe
namespace Deposit.MainLookup
theorem range_filter_4 : «poseidon-0.0.0».OracleTests.env.functions.filter (fun d => d.name == «std-1.0.0-beta.21::field::assert_max_bit_size».name) = [] := by rfl
theorem main_filter_4 : «poseidon-0.0.0».OracleTests.env.functions.filter (fun d => d.name == «deposit-0.0.0::main».name) = [] := by rfl
end Deposit.MainLookup
