import «poseidon-0.0.0».Extracted.Poseidon.Mod
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
open Lampe
namespace Deposit.ConfigLookup
theorem config_filter_8 : «poseidon-0.0.0».Poseidon.Mod.env.functions.filter (fun d => d.name == «poseidon-0.0.0::poseidon::config».name) = [«poseidon-0.0.0::poseidon::config»] := by rfl
end Deposit.ConfigLookup
