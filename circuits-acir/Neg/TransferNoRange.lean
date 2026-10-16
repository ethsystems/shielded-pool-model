import AcirLean.Transfer.Rules
open AcirLean AcirLean.Transfer
-- Negative control: this file MUST FAIL. It is a failed proof attempt, not a false
-- statement: the conclusion follows from `conservation`, but this proof uses only the three
-- ASSERTs and omits the RANGE facts, so `omega` cannot close it. Without the RANGE opcodes
-- the ASSERTs alone allow a wrap (`control_asserts_alone_allow_wrap` in Controls.lean).
theorem neg_conservation_without_ranges (w : Assignment) (h : circuit.Satisfied w) :
    (w 8).val + (w 11).val = (w 14).val + (w 18).val := by
  have hk := val_lt_P_lit (w 17906)
  have h1 := Circuit.holds_of_mem h sum_in_mem
  have h2 := Circuit.holds_of_mem h sum_out_mem
  have e3 := congrArg Fin.val (Opcode.holds_copy (Circuit.holds_of_mem h sums_eq_mem))
  simp only [Opcode.Holds, lhsVal, Expr.eval, List.foldl, P_int] at h1 h2
  omega
