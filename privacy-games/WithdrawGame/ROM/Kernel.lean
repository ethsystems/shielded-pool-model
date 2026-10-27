import WithdrawGame.ROM.Reduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM.Kernel
noncomputable local instance (priority := 100000) kernelDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance 200000] chargedDecidable
variable {P : PrimSpec} {ι : Type}
variable [Fintype ι] [Fintype P.SpendKey] [Finite P.PubKey] [Finite P.Commitment]
  [Finite P.Nullifier] [Nonempty P.SpendKey] [Nonempty P.PubKey] [Nonempty P.Nullifier]
  [SampleableType P.SpendKey] [SampleableType P.Nullifier]
  [SampleableType (ι → P.SpendKey)] [SampleableType (ι → P.PubKey)]
  [SampleableType (Transport.Table P ι)] [SampleableType (P.SpendKey → P.PubKey)]
  [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]

noncomputable def realAt (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) (keys : ι → P.SpendKey) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  runAttack hp hn (test (hp ∘ keys) (hn ∘ keyCoord keys))

noncomputable def programmedAt (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) (keys : ι → P.SpendKey) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  let pk ← $ᵗ (ι → P.PubKey)
  let f ← $ᵗ (Transport.Table P ι)
  runAttack (program keys hp pk) (program (keyCoord keys) hn f) (test pk f)

noncomputable def programmed (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) : ProbComp Bool := do
  let keys ← $ᵗ (ι → P.SpendKey)
  programmedAt test keys

theorem programmedAt_eq_realAt (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) (keys : ι → P.SpendKey)
    (hk : Function.Injective keys) : 𝒮[programmedAt test keys] = 𝒮[realAt test keys] := by
  unfold programmedAt realAt
  calc
    _ = 𝒮[do
      let hp ← $ᵗ (P.SpendKey → P.PubKey)
      let pk ← $ᵗ (ι → P.PubKey)
      let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
      runAttack (program keys hp pk) hn (test pk (hn ∘ keyCoord keys))] := by
        apply evalSPMF_bind_congr_left
        intro hp
        rw [evalSPMF_bind_comm]
        apply evalSPMF_bind_congr_left
        intro pk
        exact program_bind_restrict (R := P.Nullifier) (keyCoord_injective hk)
          (fun hn f => runAttack (program keys hp pk) hn (test pk f))
    _ = _ := program_bind_restrict hk (fun hp pk => do
      let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
      runAttack hp hn (test pk (hn ∘ keyCoord keys)))


noncomputable def real (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) : ProbComp Bool :=
  ($ᵗ (ι → P.SpendKey)) >>= realAt test

noncomputable def ideal (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) : ProbComp Bool := do
  let a ← sampleTables (P := P) (ι := ι)
  runAttack a.hp a.hn (test a.pk a.f)

noncomputable def ordered (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool)
    (prog : Bool) : ProbComp Bool := do
  let a ← sampleTables (P := P) (ι := ι)
  let keys ← $ᵗ (ι → P.SpendKey)
  if prog then runAttack (program keys a.hp a.pk) (program (keyCoord keys) a.hn a.f) (test a.pk a.f)
  else runAttack a.hp a.hn (test a.pk a.f)

theorem programmed_eq_ordered (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) :
    𝒮[programmed test] = 𝒮[ordered test true] := by
  unfold programmed ordered
  simp only [if_true]
  have he := evalSPMF_bind_comm ($ᵗ (ι → P.SpendKey)) (sampleTables (P := P) (ι := ι))
    (fun keys a => runAttack (program keys a.hp a.pk) (program (keyCoord keys) a.hn a.f) (test a.pk a.f))
  simpa only [programmedAt, sampleTables, bind_assoc, pure_bind] using he

theorem ideal_eq_ordered (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool) :
    𝒮[ideal test] = 𝒮[ordered test false] := by
  unfold ideal ordered
  simp only [Bool.false_eq_true, if_false]
  apply evalSPMF_bind_congr_left; intro a
  exact (evalSPMF_bind_const_neverFails _ (by simp) _).symm

theorem switch_bound (test : (ι → P.PubKey) → Transport.Table P ι → OracleComp (attackSpec P) Bool)
    (q : Nat) (hq : ∀ pk f, (test pk f).IsQueryBoundP (charged P) q) :
    (real test).boolDistAdvantage (ideal test) ≤
      (Fintype.card ι : ℝ) * q / Fintype.card P.SpendKey +
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card P.SpendKey := by
  have hc := ENNReal.toReal_mono (by finiteness)
    (keymap_collision_bound (I := ι) (K := P.SpendKey))
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.cast_mul, ENNReal.toReal_mul] at hc
  have hn (n : Nat) : (n : ℝ) * ((n - 1 : Nat) : ℝ) = (n : ℝ) * (n - 1) := by
    cases n with
    | zero => norm_num
    | succ n => simp [Nat.cast_add]
  rw [hn] at hc
  have hr : (real test).boolDistAdvantage (programmed test) ≤
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card P.SpendKey := by
    have h := tvDist_bind_left_event_le ($ᵗ (ι → P.SpendKey)) (realAt test) (programmedAt test)
      (fun keys => ¬Function.Injective keys)
      (fun keys hk => (programmedAt_eq_realAt test keys (not_not.mp hk)).symm)
    exact (abs_probOutput_toReal_sub_le_tvDist (real test) (programmed test)).trans (h.trans hc)
  have hi : (programmed test).boolDistAdvantage (ideal test) ≤
      (Fintype.card ι : ℝ) * q / Fintype.card P.SpendKey := by
    have h : (ordered test false).boolDistAdvantage (ordered test true) ≤
        (Fintype.card ι : ℝ) * q / Fintype.card P.SpendKey := by
      unfold ordered
      simp only [Bool.false_eq_true, if_false, if_true]
      apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
      intro a _
      exact programming_bound a.hp a.hn a.pk a.f (test a.pk a.f) q (hq a.pk a.f)
    unfold ProbComp.boolDistAdvantage at *
    rw [probOutput_congr (x := true) rfl (programmed_eq_ordered test),
      probOutput_congr (x := true) rfl (ideal_eq_ordered test), abs_sub_comm]
    exact h
  exact (ProbComp.boolDistAdvantage_triangle (real test) (programmed test) (ideal test)).trans (by linarith)

end LeanShieldedPool.WithdrawGame.ROM.Kernel
