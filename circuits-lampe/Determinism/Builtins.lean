import Determinism.Config

/-!
Determinism (`BDet`) of further builtins that the extracted Poseidon code reaches.
Pure builtins go through `bdet_pure` with an injective signature; the reference reads and writes
are proved directly. Not covered here: `ref`, the lens builtins and `toLeBits` (`Determinism.Memory`, `Determinism.Bits`).
-/

namespace Determinism
open Lampe

theorem bdet_fAdd {p argTps outTp} : BDet p Builtin.fAdd argTps outTp := bdet_pure inj_unit
theorem bdet_fMul {p argTps outTp} : BDet p Builtin.fMul argTps outTp := bdet_pure inj_unit
theorem bdet_fSub {p argTps outTp} : BDet p Builtin.fSub argTps outTp := bdet_pure inj_unit
theorem bdet_bNot {p argTps outTp} : BDet p Builtin.bNot argTps outTp := bdet_pure inj_unit
theorem bdet_bNeq {p argTps outTp} : BDet p Builtin.bNeq argTps outTp := bdet_pure inj_unit
theorem bdet_asWitness {p argTps outTp} : BDet p Builtin.asWitness argTps outTp := bdet_pure inj_unit
theorem bdet_isUnconstrained {p argTps outTp} : BDet p Builtin.isUnconstrained argTps outTp :=
  bdet_pure inj_unit
theorem bdet_uSub {p argTps outTp} : BDet p Builtin.uSub argTps outTp :=
  bdet_pure (inj_width_out (fun _ => rfl))
theorem bdet_uDiv {p argTps outTp} : BDet p Builtin.uDiv argTps outTp :=
  bdet_pure (inj_width_out (fun _ => rfl))
theorem bdet_uLt {p argTps outTp} : BDet p Builtin.uLt argTps outTp :=
  bdet_pure (inj_width_arg (fun _ => ⟨_, rfl⟩))
theorem bdet_uLeq {p argTps outTp} : BDet p Builtin.uLeq argTps outTp :=
  bdet_pure (inj_width_arg (fun _ => ⟨_, rfl⟩))
theorem bdet_uNeq {p argTps outTp} : BDet p Builtin.uNeq argTps outTp :=
  bdet_pure (inj_width_arg (fun _ => ⟨_, rfl⟩))
theorem bdet_vectorIndex {p argTps outTp} : BDet p Builtin.vectorIndex argTps outTp :=
  bdet_pure (fun _ _ _ h2 => h2)

theorem bdet_arrayIndex {p argTps outTp} : BDet p Builtin.arrayIndex argTps outTp := by
  apply bdet_pure
  rintro ⟨t, n⟩ ⟨t', n'⟩ h1 _
  simp only [List.cons.injEq, Tp.array.injEq] at h1
  obtain ⟨⟨rfl, rfl⟩, -⟩ := h1
  rfl

theorem bdet_mkArray {p argTps outTp} : BDet p Builtin.mkArray argTps outTp := by
  apply bdet_pure
  rintro ⟨n, t⟩ ⟨n', t'⟩ _ h2
  simp only [Tp.array.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rfl

theorem bdet_mkRepeatedArray {p argTps outTp} : BDet p Builtin.mkRepeatedArray argTps outTp := by
  apply bdet_pure
  rintro ⟨n, t⟩ ⟨n', t'⟩ _ h2
  simp only [Tp.array.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rfl

theorem bdet_arrayLen {p argTps outTp} : BDet p Builtin.arrayLen argTps outTp := by
  apply bdet_pure
  rintro (⟨t⟩ | ⟨t, n⟩) (⟨t'⟩ | ⟨t', n'⟩) h1 _ <;>
    simp only [Builtin.arrayLenSgn, List.cons.injEq, Tp.vector.injEq, Tp.array.injEq, and_true,
      reduceCtorEq] at h1
  · rw [h1]
  · obtain ⟨rfl, rfl⟩ := h1; rfl

theorem bdet_modulusLeBits {p argTps outTp} : BDet p Builtin.modulusLeBits argTps outTp := by
  apply bdet_pure
  rintro (_ | _) (_ | _) _ h2 <;> simp_all [Builtin.modulusLeBitsSgn]

theorem bdet_readRef {p argTps outTp} : BDet p Builtin.readRef argTps outTp := by
  intro st args Q₁ Q₂ h₁ h₂
  cases h₁ with
  | mk hl₁ hq₁ =>
    cases h₂ with
    | mk hl₂ hq₂ =>
      have hb := eq_of_heq (Sigma.mk.inj (Option.some.inj (hl₁.symm.trans hl₂))).2
      subst hb
      exact ⟨_, hq₁, hq₂⟩

theorem bdet_writeRef {p argTps outTp} : BDet p Builtin.writeRef argTps outTp := by
  intro st args Q₁ Q₂ h₁ h₂
  cases h₁ with
  | mk hl₁ hq₁ =>
    cases h₂ with
    | mk hl₂ hq₂ =>
      have hb := eq_of_heq (Sigma.mk.inj (Option.some.inj (hl₁.symm.trans hl₂))).2
      subst hb
      exact ⟨_, hq₁, hq₂⟩

#print axioms bdet_fAdd
#print axioms bdet_fMul
#print axioms bdet_fSub
#print axioms bdet_bNot
#print axioms bdet_bNeq
#print axioms bdet_asWitness
#print axioms bdet_isUnconstrained
#print axioms bdet_uSub
#print axioms bdet_uDiv
#print axioms bdet_uLt
#print axioms bdet_uLeq
#print axioms bdet_uNeq
#print axioms bdet_vectorIndex
#print axioms bdet_arrayIndex
#print axioms bdet_mkArray
#print axioms bdet_mkRepeatedArray
#print axioms bdet_arrayLen
#print axioms bdet_modulusLeBits
#print axioms bdet_readRef
#print axioms bdet_writeRef
end Determinism
