import Deposit.Rules
import Deposit.VerifyLookup

/-!
Rule 4 (attestation membership) jointly with rules 2 and 3, for every accepting
execution of the complete extracted deposit `main`.
-/

namespace Deposit.Rules
open Lampe

theorem verify_unique :
    Deposit.Range.UniqueDecl «deposit-0.0.0».env «deposit-0.0.0::verify_merkle_proof» :=
  Deposit.Range.unique_of_filter (n := 1) Deposit.VerifyLookup.verify_filter


variable {p : Prime}
variable (commitment token amount funding_address attestation_root payload_hash spending_key salt attester : Fp p)
variable (issued_at expires_at : U 64) (proof_length : U 32)
variable (path : List.Vector (Fp p) 20) (indices : List.Vector Bool 20)

/-- Rules 2, 3 and 4 jointly. The owner key is an outcome of the extracted `hash_1` on
`[spending_key]`; the same value feeds the commitment hash and the attestation leaf hash. -/
theorem accepting_main_rules {st Q}
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
                  h![owner, attester, @Builtin.CastTp.cast _ _ c₁ p issued_at,
                    @Builtin.CastTp.cast _ _ c₂ p expires_at])
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

/-- Rules 2 and 4: with `leaf` the extracted `poseidon4(owner, attester, issued_at as Field,
expires_at as Field)` and `owner` the extracted `hash_1([spending_key])`, the extracted
`binary_merkle_root(hash_2, leaf, proof_length, indices, path)` returns `attestation_root`, and
`proof_length ≤ 20`. The two casts are those of the derivation (see `cast_unconstrained`). -/
theorem accepting_main_attestation {st Q}
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
          (fun r => ∃ st₃ c, r = some (st₃, c) ∧
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
                    (fun r => ∃ st₅, r = some (st₅, attestation_root))))) := by
  obtain ⟨st₁, h⟩ := accepting_main_rules commitment token amount funding_address attestation_root
    payload_hash spending_key salt attester issued_at expires_at proof_length path indices
    accepts rejects_failure
  refine ⟨st₁, Omni.consequence h ?_⟩
  rintro r ⟨st₂, owner, rfl, h2⟩
  refine ⟨st₂, owner, rfl, Omni.consequence h2 ?_⟩
  rintro r ⟨st₃, rfl, hrest⟩
  exact ⟨st₃, commitment, rfl, hrest⟩

#print axioms verify_unique
#print axioms accepting_main_rules
#print axioms accepting_main_attestation
end Deposit.Rules
