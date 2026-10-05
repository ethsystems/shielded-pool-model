import AcirLean.Transfer.NonVacuity
import AcirLean.Transfer.Rules

/-!
# Transfer: negative controls for the amount ranges, conservation and token consistency

For each rule a mutated witness must fail, or a strengthened statement must be false.
-/

namespace AcirLean.Transfer

open AcirLean

/-! ## Amount ranges -/

/-- Mutated witness (amount_out_1, w18, set to 2^128): the RANGE opcode rejects it. -/
theorem control_range_rejects_amount_out_1 :
    (Opcode.range 18 128).check (setW solved 18 (2 ^ 128)) = false := by
  decide +kernel

/-- Mutated witness: the kernel check of chunk 0 (opcodes 0 to 255) fails on it. -/
theorem control_chunk0_rejects_amount_out_1 :
    chunk0.all (fun op => op.check (setW solved 18 (2 ^ 128))) = false := by
  decide +kernel

/-- Strengthened statement refuted: amount_in_0 < 1000 is false for the solved witness. -/
theorem control_amount_bound_1000_false :
    ¬ ∀ w : Assignment, circuit.Satisfied w → (w 8).val < 1000 := fun hall =>
  absurd (hall solved solved_satisfies) (by rw [solved_values.1]; decide)

/-! ## Conservation -/

/-- Mutated witness (amount_in_0, w8, set to 1001): the sum ASSERT (opcode 23535) rejects it. -/
theorem control_sum_in_rejects :
    (Opcode.assertZero (some 17906) ⟨[], [(1, 8), (1, 11)], 0⟩).check (setW solved 8 1001)
      = false := by
  decide +kernel

/-- Mutated witness: the kernel check of chunk 91 (opcodes 23296 to 23542) fails on it. -/
theorem control_chunk91_rejects_amount_in_0 :
    chunk91.all (fun op => op.check (setW solved 8 1001)) = false := by
  decide +kernel

/-- An assignment with amount_in_0 = P - 1, amount_in_1 = 2, amount_out_0 = 1,
    amount_out_1 = 0, and both sums 1. -/
def wrapW : Assignment :=
  setW (setW (setW (setW (setW (fun _ => ⟨0, P_pos⟩) 8 (P - 1)) 11 2) 17906 1) 14 1) 17907 1

/-- Strengthened statement refuted: the three conservation ASSERTs alone (opcodes 23535,
    23537, 23539) do not give conservation over the naturals. `wrapW` satisfies them, the
    sums differ over the naturals (they agree mod P), and the RANGE on w8 rejects it. -/
theorem control_asserts_alone_allow_wrap :
    (Opcode.assertZero (some 17906) ⟨[], [(1, 8), (1, 11)], 0⟩).check wrapW = true ∧
    (Opcode.assertZero (some 17907) ⟨[], [(1, 14), (1, 18)], 0⟩).check wrapW = true ∧
    (Opcode.assertZero (some 17907) ⟨[], [(1, 17906)], 0⟩).check wrapW = true ∧
    (Opcode.range 8 128).check wrapW = false ∧
    (wrapW 8).val + (wrapW 11).val ≠ (wrapW 14).val + (wrapW 18).val := by
  decide +kernel

/-! ## Token consistency -/

/-- Mutated witness (token_out_1, w17, set to the token plus 1): the ASSERT at opcode 23542
    rejects it. -/
theorem control_token_rejects :
    (Opcode.assertZero (some 17) ⟨[], [(1, 7)], 0⟩).check
      (setW solved 17 435537695816263162368054109405345813312609277317) = false := by
  decide +kernel

/-- Mutated witness: the kernel check of chunk 91 fails on it. -/
theorem control_chunk91_rejects_token_out_1 :
    chunk91.all (fun op => op.check
      (setW solved 17 435537695816263162368054109405345813312609277317)) = false := by
  decide +kernel

end AcirLean.Transfer
