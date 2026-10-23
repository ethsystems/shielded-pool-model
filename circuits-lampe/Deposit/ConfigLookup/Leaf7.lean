import «poseidon-0.0.0».Extracted.Poseidon.Bn254
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
import «poseidon-0.0.0».Extracted.Poseidon.Mod
open Lampe
namespace Deposit.ConfigLookup
theorem config_filter_7 : «poseidon-0.0.0».Poseidon.Bn254.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::config».name) = [] := by rfl
end Deposit.ConfigLookup
