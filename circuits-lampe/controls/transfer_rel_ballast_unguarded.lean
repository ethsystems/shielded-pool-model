import Transfer.Relational

namespace Controls.Transfer
open Lampe Deposit.Rules Determinism Transfer.HashGood Transfer.CastSteps Transfer.Forward Transfer.Rules Transfer.Relational

variable (nullifier_0 nullifier_1 commitment_out_0 commitment_out_1 commitment_root payload_hash
  spending_key token_in_0 salt_in_0 token_in_1 salt_in_1 token_out_0 owner_out_0 salt_out_0
  token_out_1 owner_out_1 salt_out_1 : Fp p)
variable (amount_in_0 amount_in_1 amount_out_0 amount_out_1 : U 128) (proof_length_0 proof_length_1 : U 32)
variable (path_0 path_1 : List.Vector (Fp p) 32) (indices_0 indices_1 : List.Vector Bool 32)

theorem transfer_rel_ballast_unguarded {st Q}
    (accepts : Omni p Γt st
      («transfer-0.0.0::main».call h![]
        h![nullifier_0, nullifier_1, commitment_out_0, commitment_out_1, commitment_root,
          payload_hash, spending_key, token_in_0, amount_in_0, salt_in_0, token_in_1, amount_in_1,
          salt_in_1, token_out_0, amount_out_0, owner_out_0, salt_out_0, token_out_1, amount_out_1,
          owner_out_1, salt_out_1, proof_length_0, path_0, indices_0, proof_length_1, path_1,
          indices_1]) Q)
    (rejects_failure : ¬ Q none) :
    Omni p Γt st («transfer-0.0.0::poseidon1».call h![] h![spending_key])
      (fun r => ∃ s₁ owner, r = some (s₁, owner) ∧
        Omni p Γt s₁ («transfer-0.0.0::poseidon4».call h![]
            h![token_in_0, ((amount_in_0.toNat : ℕ) : Fp p), owner, salt_in_0])
          (fun r => ∃ s₂ c₀, r = some (s₂, c₀) ∧
            (proof_length_0 ≤ 32 ∧ ∃ s, Omni p Γt s
              («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
                h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
                  c₀, proof_length_0, indices_0, path_0])
              (fun r => ∃ s', r = some (s', commitment_root))) ∧
            ∃ s₃, Omni p Γt s₃ («transfer-0.0.0::poseidon2».call h![] h![c₀, spending_key])
              (fun r => ∃ s₄, r = some (s₄, nullifier_0) ∧
                Omni p Γt s₄ («transfer-0.0.0::poseidon4».call h![]
                    h![token_in_1, ((amount_in_1.toNat : ℕ) : Fp p), owner, salt_in_1])
                  (fun r => ∃ s₅ c₁, r = some (s₅, c₁) ∧
                    (proof_length_1 ≤ 32 ∧ ∃ s, Omni p Γt s
                      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
                        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
                          c₁, proof_length_1, indices_1, path_1])
                      (fun r => ∃ s', r = some (s', commitment_root))) ∧
                    ∃ s₆, Omni p Γt s₆ («transfer-0.0.0::poseidon2».call h![] h![c₁, spending_key])
                      (fun r => ∃ s₇, r = some (s₇, nullifier_1) ∧
                        Omni p Γt s₇ («transfer-0.0.0::poseidon4».call h![]
                            h![token_out_0, ((amount_out_0.toNat : ℕ) : Fp p), owner_out_0, salt_out_0])
                          (fun r => ∃ s₈, r = some (s₈, commitment_out_0) ∧
                            Omni p Γt s₈ («transfer-0.0.0::poseidon4».call h![]
                                h![token_out_1, ((amount_out_1.toNat : ℕ) : Fp p), owner_out_1, salt_out_1])
                              (fun r => ∃ s₉, r = some (s₉, commitment_out_1)))))))) := by
  have rf := rejects_failure
  have h0 := step_call Transfer.Lookup.main_unique accepts
  refine Omni.consequence (step_seq (step_fn h0) rf) ?_
  rintro r ⟨s₁, owner, rfl, h1⟩
  refine ⟨s₁, owner, rfl, ?_⟩
  refine Omni.consequence (step_seq (step_cast_u128 (step_fn h1)) rf) ?_
  rintro r ⟨s₂, c₀, rfl, h2⟩
  obtain ⟨hT3a, s₃, h3⟩ := vmp_step (step_fn h2) rf
  refine ⟨s₂, c₀, rfl, hT3a, s₃, ?_⟩
  refine Omni.consequence (step_seq (step_fn h3) rf) ?_
  rintro r ⟨s₄, nf₀, rfl, h4⟩
  obtain ⟨hn0, h5⟩ := step_assert (step_fEq h4 rf) rf
  simp only [decide_eq_true_eq] at hn0
  subst nf₀
  refine ⟨s₄, rfl, ?_⟩
  have h6 := step_uEq (step_litU h5) rf
  refine Omni.consequence (step_seq (step_cast_u128 (step_fn h6)) rf) ?_
  rintro r ⟨s₅, c₁, rfl, h7⟩
  have h8 := step_bNot h7 rf
  obtain ⟨Qi, hi, hin, hk⟩ := letIn_inv h8 rf
  have hz0 : BitVec.ofInt 128 0 = (0 : U 128) := by decide
  rw [hz0] at hi
  have hT3b : amount_in_1 ≠ 0 → proof_length_1 ≤ 32 ∧ ∃ s, Omni p Γt s
      («binary_merkle_root-0.0.0::binary_merkle_root».call h![(32 : U 32)]
        h![FuncRef.decl «poseidon-0.0.0::poseidon::bn254::hash_2».name [] h![],
          c₁, proof_length_1, indices_1, path_1])
      (fun r => ∃ s', r = some (s', commitment_root)) := by
    intro hne
    have hc : (!decide (amount_in_1 = 0)) = true := by rw [decide_eq_false hne]; rfl
    rw [hc] at hi
    exact (vmp_step (step_fn (ite_true_inv hi)) hin).1
  have hout : ∃ st', Qi (some (st', ())) := by
    by_cases hz : amount_in_1 = 0
    · have hc : (!decide (amount_in_1 = 0)) = false := by simp [hz]
      rw [hc] at hi
      cases ite_false_inv hi with | skip hq => exact ⟨_, hq⟩
    · have hc : (!decide (amount_in_1 = 0)) = true := by rw [decide_eq_false hz]; rfl
      rw [hc] at hi
      obtain ⟨-, st', hs⟩ := vmp_step (step_fn (ite_true_inv hi)) hin
      cases hs with | skip hq => exact ⟨_, hq⟩
  obtain ⟨s₆, hq6⟩ := hout
  have h9 := hk () s₆ hq6
  refine ⟨s₅, c₁, rfl, hT3b, s₆, ?_⟩
  refine Omni.consequence (step_seq (step_fn h9) rf) ?_
  rintro r ⟨s₇, nf₁, rfl, h10⟩
  obtain ⟨hn1, h11⟩ := step_assert (step_fEq h10 rf) rf
  simp only [decide_eq_true_eq] at hn1
  subst nf₁
  refine ⟨s₇, rfl, ?_⟩
  refine Omni.consequence (step_seq (step_cast_u128 (step_fn h11)) rf) ?_
  rintro r ⟨s₈, co₀, rfl, h12⟩
  obtain ⟨hc0, h13⟩ := step_assert (step_fEq h12 rf) rf
  simp only [decide_eq_true_eq] at hc0
  subst co₀
  refine ⟨s₈, rfl, ?_⟩
  refine Omni.consequence (step_seq (step_cast_u128 (step_fn h13)) rf) ?_
  rintro r ⟨s₉, co₁, rfl, h14⟩
  obtain ⟨hc1, -⟩ := step_assert (step_fEq h14 rf) rf
  simp only [decide_eq_true_eq] at hc1
  subst co₁
  exact ⟨s₉, rfl⟩

#print axioms transfer_rel_ballast_unguarded
end Controls.Transfer
