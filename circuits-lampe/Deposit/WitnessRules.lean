import Deposit.Witness
import Deposit.Attestation

/-! Non-vacuity for the joint rules 2 to 4 at the witness of `Deposit.Main.main_accepting_execution`. -/

namespace Deposit.Witness
open Lampe

/-- The conclusion of `Deposit.Rules.accepting_main_rules`, as a predicate on the main inputs. -/
def MainRules {p : Prime}
    (commitment token amount attestation_root spending_key salt attester : Fp p)
    (issued_at expires_at : U 64) (proof_length : U 32)
    (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20) : Prop :=
    ∃ st₁, Omni p «deposit-0.0.0».env st₁
      («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
        h![(⟨[spending_key], rfl⟩ : List.Vector (Fp p) 1)])
      (fun r => ∃ st₂ owner, r = some (st₂, owner) ∧
        Omni p «deposit-0.0.0».env st₂
          («deposit-0.0.0::poseidon4».call h![] h![token, amount, owner, salt])
          (fun r => ∃ st₃, r = some (st₃, commitment) ∧
            ∃ (c₁ c₂ : Builtin.CastTp (.u 64) .field),
              Omni p «deposit-0.0.0».env st₃
                («deposit-0.0.0::poseidon4».call h![]
                  h![owner, attester, @Builtin.CastTp.cast _ _ c₁ p issued_at,
                    @Builtin.CastTp.cast _ _ c₂ p expires_at])
                (fun r => ∃ st₄ leaf, r = some (st₄, leaf) ∧ proof_length ≤ 20 ∧
                  Omni p «deposit-0.0.0».env st₄
                    («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
                      h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
                        leaf, proof_length, indices, path])
                    (fun r => ∃ st₅, r = some (st₅, attestation_root)))))

/-- Rules 2 to 4 hold at that witness. -/
theorem rules_nonvacuous (st : State Deposit.Main.p) :
    MainRules (p := Deposit.Main.p)
      (Deposit.MainPermutations.hash4 Deposit.Main.f5 0 0 (Deposit.MainPermutations.owner Deposit.Main.f2) 0) 0 0
      (Deposit.MainPermutations.hash4 Deposit.Main.f5 (Deposit.MainPermutations.owner Deposit.Main.f2) 0 0 0) 0 0 0
      0 0 0 (List.Vector.replicate 20 0) (List.Vector.replicate 20 false) := by
  obtain ⟨h, hn⟩ := witness_accepts st
  exact Deposit.Rules.accepting_main_rules _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hn

#print axioms rules_nonvacuous
end Deposit.Witness
