import CommitROM.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM
variable {M S C I : Type} {aux : OracleSpec I}
variable [Finite M] [Fintype S] [Finite C] [Nonempty C]
  [SampleableType S] [SampleableType (M × S → C)] [SampleableType (M → C)]

noncomputable def real (other : QueryImpl aux Id)
    (test : (M → C) → OracleComp (attackSpec M S C aux) Bool) : ProbComp Bool := do
  let s ← $ᵗ S
  let h ← $ᵗ (M × S → C)
  run other h (test (h ∘ saltCoord s))

noncomputable def ideal (other : QueryImpl aux Id)
    (test : (M → C) → OracleComp (attackSpec M S C aux) Bool) : ProbComp Bool := do
  let h ← $ᵗ (M × S → C)
  let f ← $ᵗ (M → C)
  run other h (test f)

noncomputable def programmed (other : QueryImpl aux Id)
    (test : (M → C) → OracleComp (attackSpec M S C aux) Bool) : ProbComp Bool := do
  let s ← $ᵗ S
  let h ← $ᵗ (M × S → C)
  let f ← $ᵗ (M → C)
  run other (WithdrawGame.ROM.program (saltCoord s) h f) (test f)

theorem programmed_eq_real (other : QueryImpl aux Id)
    (test : (M → C) → OracleComp (attackSpec M S C aux) Bool) :
    𝒮[programmed other test] = 𝒮[real other test] := by
  apply evalSPMF_bind_congr_left
  intro s
  exact WithdrawGame.ROM.program_bind_restrict (saltCoord_injective s)
    (fun h f => run other h (test f))

/-- Replacing a complete hidden salt slice costs at most one salt hit per charged query. -/
theorem switch_bound (other : QueryImpl aux Id)
    (test : (M → C) → OracleComp (attackSpec M S C aux) Bool)
    (q : Nat) (hq : ∀ f, (test f).IsQueryBoundP (charged (C := C) (aux := aux)) q) :
    (real other test).boolDistAdvantage (ideal other test) ≤ (q : ℝ) / Fintype.card S := by
  let ordered (prog : Bool) : ProbComp Bool := do
    let h ← $ᵗ (M × S → C)
    let f ← $ᵗ (M → C)
    let s ← $ᵗ S
    if prog then run other (WithdrawGame.ROM.program (saltCoord s) h f) (test f)
    else run other h (test f)
  have hp : 𝒮[programmed other test] = 𝒮[ordered true] := by
    unfold programmed ordered
    simp only [if_true]
    rw [evalSPMF_bind_comm ($ᵗ S)]
    apply evalSPMF_bind_congr_left
    intro h
    rw [evalSPMF_bind_comm ($ᵗ S)]
  have hi : 𝒮[ideal other test] = 𝒮[ordered false] := by
    unfold ideal ordered
    simp only [Bool.false_eq_true, if_false]
    apply evalSPMF_bind_congr_left
    intro h
    apply evalSPMF_bind_congr_left
    intro f
    exact (evalSPMF_bind_const_neverFails _ (by simp) _).symm
  have hb : (ordered false).boolDistAdvantage (ordered true) ≤ (q : ℝ) / Fintype.card S := by
    unfold ordered
    simp only [Bool.false_eq_true, if_false, if_true]
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro h _
    apply PoolGame.Averaging.boolDistAdvantage_bind_le_const
    intro f _
    exact programming_bound other h f (test f) q (hq f)
  unfold ProbComp.boolDistAdvantage at *
  rw [← probOutput_congr (x := true) rfl (programmed_eq_real other test),
    probOutput_congr (x := true) rfl hp, probOutput_congr (x := true) rfl hi, abs_sub_comm]
  exact hb

end LeanShieldedPool.CommitROM
