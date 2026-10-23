import «poseidon-0.0.0».Extracted.Poseidon.Bn254.Perm
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
open Lampe
namespace Deposit.VerifyLookup
theorem verify_filter_6 : «poseidon-0.0.0».Poseidon.Bn254.Perm.env.functions.filter (fun d => d.name == «deposit-0.0.0::verify_merkle_proof».name) = [] := by rfl
end Deposit.VerifyLookup
