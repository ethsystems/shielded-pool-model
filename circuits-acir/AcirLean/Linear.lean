import AcirLean.Witness

/-!
# Linear facts about printed ACIR opcodes

Lemmas for the two opcode shapes of the linear rules: a copy `ASSERT wK = wI` and a sum
`ASSERT wK = wI + wJ`. Canonical field values lie in `[0, P)`. A difference that is zero mod
`P` and lies strictly between `-P` and `P` is zero, so these field equations are equations
over the naturals. `setW` changes one value of an assignment (for the negative controls).
-/

namespace AcirLean

theorem P_int : (P : Int) =
    21888242871839275222246405745257275088548364400416034343698204186575808495617 := rfl

theorem val_lt_P_lit (x : Fin P) :
    x.val < 21888242871839275222246405745257275088548364400416034343698204186575808495617 :=
  x.isLt

theorem two_pow_128_add_lt_P : 2 ^ 128 + 2 ^ 128 < P := by decide

/-- `ASSERT wK = wI`: the two canonical values are equal. -/
theorem Opcode.holds_copy {w : Assignment} {k i : Nat}
    (h : (Opcode.assertZero (some k) ⟨[], [(1, i)], 0⟩).Holds w) : w k = w i := by
  have hk := val_lt_P_lit (w k)
  have hi := val_lt_P_lit (w i)
  simp only [Opcode.Holds, lhsVal, Expr.eval, List.foldl, P_int] at h
  exact Fin.ext (by omega)

/-- `ASSERT wK = wI + wJ` with `wI + wJ < P`: the sum holds over the naturals. -/
theorem Opcode.holds_add {w : Assignment} {k i j : Nat}
    (h : (Opcode.assertZero (some k) ⟨[], [(1, i), (1, j)], 0⟩).Holds w)
    (hlt : (w i).val + (w j).val < P) : (w k).val = (w i).val + (w j).val := by
  have hk := val_lt_P_lit (w k)
  have hlt' : (w i).val + (w j).val <
      21888242871839275222246405745257275088548364400416034343698204186575808495617 := hlt
  simp only [Opcode.Holds, lhsVal, Expr.eval, List.foldl, P_int] at h
  omega

/-- The assignment `w` with the value at index `i` replaced by `v mod P`. -/
def setW (w : Assignment) (i v : Nat) : Assignment :=
  fun j => if j = i then ⟨v % P, Nat.mod_lt _ P_pos⟩ else w j

end AcirLean
