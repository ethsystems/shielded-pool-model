import AcirLean.Transfer.Rules
open AcirLean AcirLean.Transfer
-- Negative control: this file MUST FAIL. It claims that opcode 23542 equates token_out_1
-- (w17) with amount_out_1 (w18) instead of token_in_0 (w7).
theorem neg_token_out_1_mem : Opcode.assertZero (some 17) ⟨[], [(1, 18)], 0⟩ ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23542) (by decide +kernel)
