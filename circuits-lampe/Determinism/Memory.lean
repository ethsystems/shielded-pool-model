import Determinism.Builtins

/-!
Determinism of the allocation builtin `ref` and of the lens update `modifyLens`, which the
extracted code uses for `let mut` and for `a[i] = …` assignments.
-/

namespace Determinism
open Lampe

theorem exists_fresh {p} (st : ValHeap p) : ∃ a : Address, a ∉ st := by
  refine ⟨⟨(st.keys.image Address.val).sup id + 1⟩, ?_⟩
  intro hmem
  have hk : (⟨(st.keys.image Address.val).sup id + 1⟩ : Address) ∈ st.keys := Finmap.mem_keys.mpr hmem
  have hle : (st.keys.image Address.val).sup id + 1 ≤ (st.keys.image Address.val).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem Address.val hk)
  omega

theorem bdet_ref {p argTps outTp} : BDet p Builtin.ref argTps outTp := by
  intro st args Q₁ Q₂ h₁ h₂
  cases h₁ with
  | mk hq₁ =>
    cases h₂ with
    | mk hq₂ =>
      obtain ⟨a, ha⟩ := exists_fresh st
      exact ⟨_, hq₁ a ha, hq₂ a ha⟩

theorem bdet_modifyLens {p rep tp₁ tp₂} (lens : Lens rep tp₁ tp₂) {argTps outTp} :
    BDet p (Builtin.modifyLens lens) argTps outTp := by
  intro st args Q₁ Q₂ h₁ h₂
  cases h₁ with
  | ok hl₁ hg₁ hm₁ hb₁ hq₁ =>
    cases h₂ with
    | ok hl₂ hg₂ hm₂ hb₂ hq₂ =>
      have hb := eq_of_heq (Sigma.mk.inj (Option.some.inj (hl₁.symm.trans hl₂))).2
      subst hb hg₁ hg₂ hb₁ hb₂
      have hs := Option.some.inj (hm₁.trans hm₂.symm)
      subst hs
      exact ⟨_, hq₁, hq₂⟩
    | err hl₂ hg₂ hm₂ hq₂ =>
      have hb := eq_of_heq (Sigma.mk.inj (Option.some.inj (hl₁.symm.trans hl₂))).2
      subst hb hg₁ hg₂
      exact absurd (hm₁.trans hm₂.symm) (by simp)
  | err hl₁ hg₁ hm₁ hq₁ =>
    cases h₂ with
    | ok hl₂ hg₂ hm₂ hb₂ hq₂ =>
      have hb := eq_of_heq (Sigma.mk.inj (Option.some.inj (hl₁.symm.trans hl₂))).2
      subst hb hg₁ hg₂
      exact absurd (hm₂.trans hm₁.symm) (by simp)
    | err _ _ _ hq₂ => exact ⟨none, hq₁, hq₂⟩

#print axioms exists_fresh
#print axioms bdet_ref
#print axioms bdet_modifyLens
end Determinism
