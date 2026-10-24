import WithdrawGame.Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame.Transport
open GameCorrespondence
variable {P : PrimSpec} {ι : Type}

/-- Failure of the common prefix, including its commitment and nullifier collisions. -/
def PrefixRejected (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι) : Prop :=
  RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = none

/-- Either candidate nullifier equals an earlier spent nullifier in an accepted prefix. -/
def CandidateCollision (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι) : Prop :=
  ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
    ((c.withdrawal keys false).nf ∈ st.nullifiers ∨ (c.withdrawal keys true).nf ∈ st.nullifiers)

/-- All remaining illegal choices. This includes unequal token/amount, duplicate candidate
commitments, non-minted notes, stale roots, ownership and amount/balance failures. -/
def OtherIllegal (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι) : Prop :=
  ¬ Legal sup keys c ∧ ¬ PrefixRejected sup keys c ∧ ¬ CandidateCollision sup keys c

theorem prefix_rejected_illegal (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (h : PrefixRejected sup keys c) : ¬ Legal sup keys c := by
  rintro ⟨_, _, _, st, hs, _⟩
  rw [h] at hs
  contradiction

theorem candidate_collision_illegal (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (h : CandidateCollision sup keys c) : ¬ Legal sup keys c := by
  obtain ⟨st, hs, hc⟩ := h
  rintro ⟨_, _, _, st', hs', _, _, hl, hr⟩
  have he : st = st' := Option.some.inj (hs.symm.trans hs')
  subst st'
  exact hc.elim hl.2.2.2.1 hr.2.2.2.1

theorem rejection_partition (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) : ¬ Legal sup keys c ↔
      PrefixRejected sup keys c ∨ CandidateCollision sup keys c ∨ OtherIllegal sup keys c := by
  classical
  constructor
  · intro h
    by_cases hp : PrefixRejected sup keys c
    · exact Or.inl hp
    by_cases hc : CandidateCollision sup keys c
    · exact Or.inr (Or.inl hc)
    exact Or.inr (Or.inr ⟨h, hp, hc⟩)
  · rintro (h | h | h)
    · exact prefix_rejected_illegal sup keys c h
    · exact candidate_collision_illegal sup keys c h
    · exact h.1

noncomputable def drawEventProbability [SampleableType (ι → P.SpendKey)]
    (adv : Adversary P ι) (p : (ι → P.SpendKey) → Challenge P ι → Prop) : ℝ :=
  (Pr[fun a => p a.1 a.2.1 | draws adv]).toReal

theorem rejection_probability_partition [SampleableType (ι → P.SpendKey)]
    (sup : P.Token → Prop) (adv : Adversary P ι) :
    rejectionProbability sup adv =
      drawEventProbability adv (PrefixRejected sup) +
      drawEventProbability adv (CandidateCollision sup) +
      drawEventProbability adv (OtherIllegal sup) := by
  classical
  have he : rejectionProbability sup adv =
      (Pr[fun a => ¬ Legal sup a.1 a.2.1 | draws adv]).toReal := by
    simp only [rejectionProbability, draws, probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
      probEvent_pure, probOutput_pure, rejected_eq_not_legal]
    congr 1
    apply tsum_congr
    intro b
    congr 1
    apply tsum_congr
    intro keys
    congr 1
    apply tsum_congr
    intro a
    simp
  rw [he]
  have hp : Pr[fun a => ¬ Legal sup a.1 a.2.1 | draws adv] =
      Pr[fun a => PrefixRejected sup a.1 a.2.1 | draws adv] +
      Pr[fun a => CandidateCollision sup a.1 a.2.1 | draws adv] +
      Pr[fun a => OtherIllegal sup a.1 a.2.1 | draws adv] := by
    simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
    apply tsum_congr
    intro a
    by_cases h₁ : PrefixRejected sup a.1 a.2.1
    · have h₂ : ¬ CandidateCollision sup a.1 a.2.1 := by
        rintro ⟨st, hs, _⟩
        rw [h₁] at hs
        contradiction
      simp [h₁, h₂, OtherIllegal, prefix_rejected_illegal sup a.1 a.2.1 h₁]
    by_cases h₂ : CandidateCollision sup a.1 a.2.1
    · simp [h₁, h₂, OtherIllegal, candidate_collision_illegal sup a.1 a.2.1 h₂]
    · simp [h₁, h₂, OtherIllegal]
  rw [hp, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  rfl

/-- `advantage_le_accounts` with every rejection term exposed. Only CandidateCollision is the
terminal candidate-versus-earlier-spend collision term. Prefix and other illegality remain explicit. -/
theorem advantage_le_explicit [Fintype ι] [Finite P.Commitment]
    [Finite P.Nullifier] [Nonempty P.Nullifier] [SampleableType P.Nullifier]
    [SampleableType (ι → P.SpendKey)] [SampleableType (Table P ι)]
    (sup : P.Token → Prop) (adv : Adversary P ι) (ε : ℝ)
    (hPRF : MultiKeyPublicKeyPRF (P := P) (ι := ι) (Fintype.card ι * ε)) :
    advantage sup adv ≤ Fintype.card ι * ε +
      (drawEventProbability adv (PrefixRejected sup) +
       drawEventProbability adv (CandidateCollision sup) +
       drawEventProbability adv (OtherIllegal sup)) / 2 := by
  simpa only [rejection_probability_partition] using advantage_le_accounts sup adv ε hPRF

end LeanShieldedPool.WithdrawGame.Transport
