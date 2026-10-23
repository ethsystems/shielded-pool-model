import «poseidon-0.0.0».Extracted.OracleTests
import «deposit-0.0.0».Extracted.Main
import «std-1.0.0-beta.21».Extracted.Field.Mod
import Lampe
open Lampe
namespace Deposit.VerifyLookup
theorem verify_filter_4 : «poseidon-0.0.0».OracleTests.env.functions.filter (fun d => d.name == «deposit-0.0.0::verify_merkle_proof».name) = [] := by rfl
end Deposit.VerifyLookup
