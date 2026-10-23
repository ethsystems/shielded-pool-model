import Deposit.RangeWitness

/-!
Rule 3 (commitment binding) and rule 2 (owner key) for every accepting execution of
the complete extracted deposit `main`. The hashes stay the extracted Lampe declarations.
-/

namespace Deposit.Rules
open Lampe

variable {p : Prime}
variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

/-- Rule 3, commitment binding, with rule 2 as its outer layer: in every accepting execution the
public `commitment` is the value the extracted `poseidon4(token, amount, owner, salt)` returns on
every outcome, where `owner` is an outcome of the extracted `hash_1([spending_key])`. -/
theorem accepting_main_commitment {st Q}
    (accepts : Omni p «deposit-0.0.0».env st
      («deposit-0.0.0::main».call h![]
        h![commitment, token, amount, funding_address, attestation_root, payload_hash,
          spending_key, salt, attester, issued_at, expires_at, proof_length, path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    ∃ st₁, Omni p «deposit-0.0.0».env st₁
      («poseidon-0.0.0::poseidon::bn254::hash_1».call h![]
        h![(⟨[spending_key], rfl⟩ : List.Vector (Fp p) 1)])
      (fun r => ∃ st₂ owner, r = some (st₂, owner) ∧
        Omni p «deposit-0.0.0».env st₂
          («deposit-0.0.0::poseidon4».call h![] h![token, amount, owner, salt])
          (fun r => ∃ st₃, r = some (st₃, commitment))) := by
  have h0 := step_call Deposit.Range.main_unique accepts
  have h1 := step_fn h0
  obtain ⟨st₁, _, h2⟩ := (range_wit amount).run (step_seq h1 rejects_failure)
    (fun h => by simp at h)
  obtain ⟨st₁', _, hst, h3⟩ := h2
  cases hst
  refine ⟨st₁, ?_⟩
  have h4 := step_mkArray1 (step_fn h3) rejects_failure
  refine Omni.consequence (step_seq h4 rejects_failure) ?_
  rintro r ⟨st₂, owner, rfl, h5⟩
  refine ⟨st₂, owner, rfl, ?_⟩
  refine Omni.consequence (step_seq (step_fn h5) rejects_failure) ?_
  rintro r ⟨st₃, cc, rfl, h6⟩
  obtain ⟨hc, _⟩ := step_assert (step_fEq h6 rejects_failure) rejects_failure
  simp only [decide_eq_true_eq] at hc
  subst hc
  exact ⟨st₃, rfl⟩

#print axioms accepting_main_commitment
end Deposit.Rules
