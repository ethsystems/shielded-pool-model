import Deposit.Main
import Deposit.Rules

/-!
Non-vacuity: the accepting execution `Deposit.Main.main_accepting_execution` satisfies the premises of
`Deposit.Rules.accepting_main_commitment`, so its conclusion holds at that witness
(amount 0, timestamps 0, Merkle depth 0; hashes through the extracted Poseidon code).
-/

namespace Deposit.Witness
open Lampe

/-- The conclusion of `Deposit.Rules.accepting_main_commitment` (rules 3 and 2). -/
def CommitmentRule {p : Prime} (commitment token amount spending_key salt : Fp p) : Prop :=
    ∃ st₁, Omni p «deposit-0.0.0».env st₁
      («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
        h![(⟨[spending_key], rfl⟩ : List.Vector (Fp p) 1)])
      (fun r => ∃ st₂ owner, r = some (st₂, owner) ∧
        Omni p «deposit-0.0.0».env st₂
          («deposit-0.0.0::poseidon4».call h![] h![token, amount, owner, salt])
          (fun r => ∃ st₃, r = some (st₃, commitment)))

/-- The witness of `Deposit.Main.main_accepting_execution` is an accepting execution: its postcondition rejects failure. -/
theorem witness_accepts (st : State Deposit.Main.p) :
    Omni Deposit.Main.p Deposit.Main.Γ st (Deposit.MainPermutations.mainCall Deposit.Main.f2 Deposit.Main.f5)
      (fun r => ∃ st', r = some (st', ())) ∧
    ¬ (fun r : Option (State Deposit.Main.p × Unit) => ∃ st', r = some (st', ())) none :=
  ⟨Deposit.Main.main_accepting_execution st, by rintro ⟨_, h⟩; cases h⟩

/-- Rules 3 and 2 hold at that witness. -/
theorem commitment_nonvacuous (st : State Deposit.Main.p) :
    CommitmentRule (p := Deposit.Main.p)
      (Deposit.MainPermutations.hash4 Deposit.Main.f5 0 0 (Deposit.MainPermutations.owner Deposit.Main.f2) 0) 0 0 0 0 := by
  obtain ⟨h, hn⟩ := witness_accepts st
  exact Deposit.Rules.accepting_main_commitment _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hn

#print axioms witness_accepts
#print axioms commitment_nonvacuous
end Deposit.Witness
