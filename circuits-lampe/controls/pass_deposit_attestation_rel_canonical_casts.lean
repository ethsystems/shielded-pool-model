import Deposit.Attestation

namespace Controls.DepositRules
open Lampe Deposit.Rules

variable {p : Prime}
variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

theorem pass_deposit_attestation_rel_canonical_casts {st Q}
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
          (fun r => ∃ st₃, r = some (st₃, commitment) ∧
            ∃ (c₁ c₂ : Builtin.CastTp (.u 64) .field),
              Omni p «deposit-0.0.0».env st₃
                («deposit-0.0.0::poseidon4».call h![]
                  h![owner, attester, ((issued_at.toNat : ℕ) : Fp p),
                    ((expires_at.toNat : ℕ) : Fp p)])
                (fun r => ∃ st₄ leaf, r = some (st₄, leaf) ∧ proof_length ≤ 20 ∧
                  Omni p «deposit-0.0.0».env st₄
                    («binary_merkle_root-0.0.0::binary_merkle_root».call h![(20 : U 32)]
                      h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
                        leaf, proof_length, indices, path])
                    (fun r => ∃ st₅, r = some (st₅, attestation_root))))) := by
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
  obtain ⟨hc, h7⟩ := step_assert (step_fEq h6 rejects_failure) rejects_failure
  simp only [decide_eq_true_eq] at hc
  subst hc
  refine ⟨st₃, rfl, ?_⟩
  obtain ⟨c₁, h8⟩ := step_cast (step_fn h7)
  obtain ⟨c₂, h9⟩ := step_cast h8
  refine ⟨c₁, c₂, ?_⟩
  refine Omni.consequence (step_seq h9 rejects_failure) ?_
  rintro r ⟨st₄, leaf, rfl, h10⟩
  refine ⟨st₄, leaf, rfl, ?_⟩
  obtain ⟨Qv, hv, hvn, _⟩ := letIn_inv (step_fn h10) rejects_failure
  have hv0 := step_call (decl := «deposit-0.0.0::verify_merkle_proof») (generics := h![(20 : U 32)])
    verify_unique hv
  dsimp only [«deposit-0.0.0::verify_merkle_proof»] at hv0
  have hv1 := step_constU hv0
  obtain ⟨hle, hv2⟩ := step_assert (step_uLeq hv1 hvn) hvn
  simp only [decide_eq_true_eq] at hle
  refine ⟨hle, ?_⟩
  refine Omni.consequence (step_seq (step_fn (step_fn hv2)) hvn) ?_
  rintro r ⟨st₅, root', rfl, hv3⟩
  obtain ⟨hr, _⟩ := step_assert (step_fEq hv3 hvn) hvn
  simp only [decide_eq_true_eq] at hr
  subst hr
  exact ⟨st₅, rfl⟩

#print axioms pass_deposit_attestation_rel_canonical_casts
end Controls.DepositRules
