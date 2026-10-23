import «std-1.0.0-beta.21».Extracted.Field.Mod
import «deposit-0.0.0».Extracted.Main
import Lampe
import «poseidon-0.0.0».Extracted.Poseidon.Mod
open Lampe
namespace Deposit.ConfigLookup
theorem config_filter_27 : «std-1.0.0-beta.21».Field.Mod.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::config».name) = [] := by rfl
end Deposit.ConfigLookup
