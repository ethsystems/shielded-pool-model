import AcirLean.Withdraw.NonVacuity
import AcirLean.Withdraw.Amount
import AcirLean.Linear

/-!
# Withdraw: negative controls for the amount range

A mutated witness must fail, and a strengthened statement must be false.
-/

namespace AcirLean.Withdraw

open AcirLean

/-- Mutated witness (amount w2 set to 2^128): the RANGE opcode rejects it. -/
theorem control_range_rejects_2_pow_128 :
    (Opcode.range 2 128).check (setW solved 2 (2 ^ 128)) = false := by
  decide +kernel

/-- Mutated witness: the kernel check of chunk 1 (opcodes 256 to 511, with opcode 362)
    fails on it. -/
theorem control_chunk1_rejects_2_pow_128 :
    chunk1.all (fun op => op.check (setW solved 2 (2 ^ 128))) = false := by
  decide +kernel

/-- Strengthened statement refuted: the bound cannot be lowered to 700, because the solved
    witness satisfies the circuit with amount 700. -/
theorem control_bound_700_false :
    ¬ ∀ w : Assignment, circuit.Satisfied w → (w 2).val < 700 := fun hall =>
  absurd (hall solved solved_satisfies) (by rw [solved_values]; decide)

/-- The RANGE opcode alone allows amount `2^127`, the smallest amount that breaks a 127-bit
    bound: it accepts the solved witness with w2 set to `2^127`. This shows only that the
    RANGE opcode gives no 127-bit bound. It does not show that the whole circuit accepts
    amount `2^127`. -/
theorem control_range_alone_allows_2_pow_127 :
    (Opcode.range 2 128).check (setW solved 2 (2 ^ 127)) = true := by
  decide +kernel

end AcirLean.Withdraw
