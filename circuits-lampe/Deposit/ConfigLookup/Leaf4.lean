import «poseidon-0.0.0».Extracted.OracleTests
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
import «poseidon-0.0.0».Extracted.Poseidon.Mod
open Lampe
namespace Deposit.ConfigLookup
theorem config_filter_4 : «poseidon-0.0.0».OracleTests.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::config».name) = [] := by rfl
end Deposit.ConfigLookup
