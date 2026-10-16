import AcirLean.Deposit.Amount
open AcirLean AcirLean.Deposit
-- Negative control: this file MUST FAIL. It claims a 127-bit bound with the proof of the
-- 128-bit rule; opcode 23 is `RANGE w2 128`, so the membership step cannot close.
theorem neg_amount_lt_two_pow_127 (w : Assignment) (h : circuit.Satisfied w) :
    (w 2).val < 2 ^ 127 :=
  Circuit.range_of_mem h (List.mem_of_getElem? (l := opcodes) (i := 23) (by decide +kernel))
