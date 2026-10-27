import WithdrawGame.ROM.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM
noncomputable local instance (priority := 100000) reductionDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance 200000] chargedDecidable
variable {P : PrimSpec} {ι : Type}
variable [Fintype ι] [Fintype P.SpendKey] [Finite P.PubKey] [Finite P.Commitment]
  [Finite P.Nullifier] [Nonempty P.SpendKey] [Nonempty P.PubKey] [Nonempty P.Nullifier]
  [SampleableType P.SpendKey] [SampleableType P.Nullifier]
  [SampleableType (ι → P.SpendKey)] [SampleableType (ι → P.PubKey)]
  [SampleableType (Transport.Table P ι)] [SampleableType (P.SpendKey → P.PubKey)]
  [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]

noncomputable def realAt (adv : Adversary P ι) (keys : ι → P.SpendKey) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  Transport.test (baseAdversary adv hp hn) (hp ∘ keys) (hn ∘ keyCoord keys)

noncomputable def programmedAt (adv : Adversary P ι) (keys : ι → P.SpendKey) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  let pk ← $ᵗ (ι → P.PubKey)
  let f ← $ᵗ (Transport.Table P ι)
  Transport.test (baseAdversary adv (program keys hp pk) (program (keyCoord keys) hn f)) pk f

noncomputable def programmed (adv : Adversary P ι) : ProbComp Bool := do
  let keys ← $ᵗ (ι → P.SpendKey)
  programmedAt adv keys

theorem programmedAt_eq_realAt (adv : Adversary P ι) (keys : ι → P.SpendKey)
    (hk : Function.Injective keys) : 𝒮[programmedAt adv keys] = 𝒮[realAt adv keys] := by
  unfold programmedAt realAt
  calc
    _ = 𝒮[do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let pk ← $ᵗ (ι → P.PubKey)
      let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
      Transport.test (baseAdversary adv (program keys hp pk) hn) pk (hn ∘ keyCoord keys)] := by
        apply evalSPMF_bind_congr_left
        intro hp
        rw [evalSPMF_bind_comm]
        apply evalSPMF_bind_congr_left
        intro pk
        exact program_bind_restrict (R := P.Nullifier) (keyCoord_injective hk)
          (fun hn f => Transport.test (baseAdversary adv (program keys hp pk) hn) pk f)
    _ = _ := program_bind_restrict hk (fun hp pk => do
      let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
      Transport.test (baseAdversary adv hp hn) pk (hn ∘ keyCoord keys))

theorem real_eq_keys_first (adv : Adversary P ι) :
    𝒮[realUnguarded adv] = 𝒮[($ᵗ (ι → P.SpendKey)) >>= realAt adv] := by
  unfold realUnguarded realAt
  rw [evalSPMF_bind_comm ($ᵗ (ι → P.SpendKey))]
  apply evalSPMF_bind_congr_left
  intro hp
  rw [evalSPMF_bind_comm ($ᵗ (ι → P.SpendKey))]
  rfl

theorem real_programmed_distance (adv : Adversary P ι) :
    (realUnguarded adv).boolDistAdvantage (programmed adv) ≤
      (Pr[fun keys : ι → P.SpendKey => ¬Function.Injective keys | $ᵗ (ι → P.SpendKey)]).toReal := by
  have h := tvDist_bind_left_event_le ($ᵗ (ι → P.SpendKey)) (realAt adv) (programmedAt adv)
    (fun keys => ¬Function.Injective keys)
    (fun keys hk => (programmedAt_eq_realAt adv keys (not_not.mp hk)).symm)
  have hb := (abs_probOutput_toReal_sub_le_tvDist
    (($ᵗ (ι → P.SpendKey)) >>= realAt adv) (programmed adv)).trans h
  unfold ProbComp.boolDistAdvantage at *
  rw [probOutput_congr (x := true) rfl (real_eq_keys_first adv)]
  exact hb

structure Tables (P : PrimSpec) (ι : Type) where
  hp : P.SpendKey → P.PubKey
  hn : (P.SpendKey × P.Commitment) → P.Nullifier
  pk : ι → P.PubKey
  f : Transport.Table P ι

noncomputable def sampleTables : ProbComp (Tables P ι) := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  let pk ← $ᵗ (ι → P.PubKey)
  let f ← $ᵗ (Transport.Table P ι)
  pure ⟨hp,hn,pk,f⟩

noncomputable def ordered (adv : Adversary P ι) (prog : Bool) : ProbComp Bool := do
  let a ← sampleTables (P := P) (ι := ι)
  let b ← $ᵗ Bool
  let keys ← $ᵗ (ι → P.SpendKey)
  if prog then
    runAttack (program keys a.hp a.pk) (program (keyCoord keys) a.hn a.f)
      (whole adv a.pk a.f b)
  else runAttack a.hp a.hn (whole adv a.pk a.f b)

theorem programmed_eq_ordered (adv : Adversary P ι) :
    𝒮[programmed adv] = 𝒮[ordered adv true] := by
  unfold programmed ordered
  simp only [if_true]
  calc
    _ = 𝒮[do
      let keys ← $ᵗ (ι → P.SpendKey)
      let a ← sampleTables (P := P) (ι := ι)
      let b ← $ᵗ Bool
      runAttack (program keys a.hp a.pk) (program (keyCoord keys) a.hn a.f)
        (whole adv a.pk a.f b)] := by
      apply evalSPMF_bind_congr_left
      intro keys
      simp only [programmedAt, sampleTables, bind_assoc, pure_bind]
      apply evalSPMF_bind_congr_left; intro hp
      apply evalSPMF_bind_congr_left; intro hn
      apply evalSPMF_bind_congr_left; intro pk
      apply evalSPMF_bind_congr_left; intro f
      exact test_eq_whole adv _ _ pk f
    _ = _ := by
      rw [evalSPMF_bind_comm ($ᵗ (ι → P.SpendKey))]
      apply evalSPMF_bind_congr_left
      intro a
      exact evalSPMF_bind_comm _ _ _

theorem ideal_eq_ordered (adv : Adversary P ι) :
    𝒮[ideal adv] = 𝒮[ordered adv false] := by
  unfold ideal ordered
  simp only [sampleTables, bind_assoc, pure_bind, Bool.false_eq_true, if_false]
  apply evalSPMF_bind_congr_left; intro hp
  apply evalSPMF_bind_congr_left; intro hn
  apply evalSPMF_bind_congr_left; intro pk
  apply evalSPMF_bind_congr_left; intro f
  rw [test_eq_whole]
  apply evalSPMF_bind_congr_left; intro b
  exact (evalSPMF_bind_const_neverFails _ (by simp) _).symm

theorem programmed_ideal_distance (adv : Adversary P ι) (qc qg : Nat)
    (hq : QueryBound adv qc qg) :
    (programmed adv).boolDistAdvantage (ideal adv) ≤
      (Fintype.card ι : ℝ) * (qc + qg) / Fintype.card P.SpendKey := by
  have h : (ordered adv false).boolDistAdvantage (ordered adv true) ≤
      (Fintype.card ι : ℝ) * (qc + qg) / Fintype.card P.SpendKey := by
    unfold ordered
    simp only [Bool.false_eq_true, if_false, if_true]
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro a _
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro b _
    simpa only [Nat.cast_add] using programming_bound a.hp a.hn a.pk a.f
      (whole adv a.pk a.f b) (qc+qg) (whole_bound adv qc qg hq a.pk a.f b)
  unfold ProbComp.boolDistAdvantage at *
  rw [probOutput_congr (x := true) rfl (programmed_eq_ordered adv),
    probOutput_congr (x := true) rfl (ideal_eq_ordered adv), abs_sub_comm]
  exact h

theorem oracleSwitch_of_queryBound (adv : Adversary P ι) (qc qg : Nat)
    (hq : QueryBound adv qc qg) : OracleSwitch adv qc qg := by
  have hc := ENNReal.toReal_mono (by finiteness)
    (keymap_collision_bound (I := ι) (K := P.SpendKey))
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.cast_mul, ENNReal.toReal_mul] at hc
  have hn (n : Nat) : (n : ℝ) * ((n - 1 : Nat) : ℝ) = (n : ℝ) * (n - 1) := by
    cases n with
    | zero => norm_num
    | succ n => simp [Nat.cast_add]
  rw [hn] at hc
  have ht := ProbComp.boolDistAdvantage_triangle (realUnguarded adv) (programmed adv) (ideal adv)
  have hr := real_programmed_distance adv
  have hp := programmed_ideal_distance adv qc qg hq
  unfold OracleSwitch
  linarith

/-- Withdrawal privacy in the eager ROM, with no switching premise. -/
theorem advantage_le_queryBound (sup : P.Token → Prop) (adv : Adversary P ι)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    advantage sup adv ≤
      (Fintype.card ι : ℝ) * (qc + qg) / Fintype.card P.SpendKey +
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card P.SpendKey +
      rejectionProbability sup adv / 2 :=
  advantage_le_of_oracle_switch sup adv qc qg (oracleSwitch_of_queryBound adv qc qg hq)

end LeanShieldedPool.WithdrawGame.ROM
