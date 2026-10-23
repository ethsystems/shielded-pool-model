import Withdraw.Rules

namespace Controls.Withdraw
open Lampe Determinism Withdraw.HashGood Deposit.Rules Withdraw.Rules

variable (nullifier token amount recipient commitment_root spending_key salt : Fp p)
variable (proof_length : U 32) (path : List.Vector (Fp p) 32) (indices : List.Vector Bool 32)

theorem withdraw_rel_nullifier_is_root {st Q}
    (accepts : Omni p Γw st
      («withdraw-0.0.0::main».call h![]
        h![nullifier, token, amount, recipient, commitment_root, spending_key, salt, proof_length,
          path, indices]) Q)
    (rejects_failure : ¬ Q none) :
    Omni p Γw st («withdraw-0.0.0::poseidon1».call h![] h![spending_key])
      (fun r => ∃ st₂ owner, r = some (st₂, owner) ∧
        ∃ st₃, Omni p Γw st₃ («withdraw-0.0.0::poseidon4».call h![] h![token, amount, owner, salt])
          (fun r => ∃ st₄ commitment, r = some (st₄, commitment) ∧ proof_length ≤ 32 ∧
            (∃ st₅, Omni p Γw st₅
              («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
                h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
                  commitment, proof_length, indices, path])
              (fun r => ∃ st₆, r = some (st₆, commitment_root))) ∧
            Omni p Γw st₄ («withdraw-0.0.0::verify_merkle_proof».call h![(32 : U 32)]
                h![commitment, commitment_root, proof_length, indices, path])
              (fun r => ∃ st₇ u, r = some (st₇, u) ∧
                Omni p Γw st₇ («withdraw-0.0.0::poseidon2».call h![] h![commitment, spending_key])
                  (fun r => ∃ st₈, r = some (st₈, commitment_root))))) := by
  have h0 := step_call Withdraw.Lookup.main_unique accepts
  have h1 := step_fn h0
  refine Omni.consequence (step_seq h1 rejects_failure) ?_
  rintro r ⟨st₂, owner, rfl, h2⟩
  refine ⟨st₂, owner, rfl, ?_⟩
  obtain ⟨st₃, _, h3⟩ := (range_wit_w amount).run (step_seq (step_fn h2) rejects_failure)
    (fun h => by simp at h)
  obtain ⟨st₃', _, hst, h4⟩ := h3
  cases hst
  refine ⟨st₃, ?_⟩
  refine Omni.consequence (step_seq (step_fn h4) rejects_failure) ?_
  rintro r ⟨st₄, cm, rfl, h5⟩
  refine ⟨st₄, cm, rfl, ?_⟩
  obtain ⟨Qv, hv, hvn, hk⟩ := letIn_inv (step_fn h5) rejects_failure
  obtain ⟨hle, hroot⟩ := vmp_rel cm commitment_root proof_length indices path hv hvn
  refine ⟨hle, hroot, ?_⟩
  refine Omni.consequence hv ?_
  intro r hr
  cases r with
  | none => exact absurd hr hvn
  | some sv =>
    obtain ⟨st₇, u⟩ := sv
    refine ⟨st₇, u, rfl, ?_⟩
    have h6 := hk u st₇ hr
    refine Omni.consequence (step_seq (step_fn h6) rejects_failure) ?_
    rintro r ⟨st₈, nf, rfl, h7⟩
    obtain ⟨hc, _⟩ := step_assert (step_fEq h7 rejects_failure) rejects_failure
    simp only [decide_eq_true_eq] at hc
    subst hc
    exact ⟨st₈, rfl⟩

#print axioms withdraw_rel_nullifier_is_root
end Controls.Withdraw
