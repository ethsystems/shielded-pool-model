import AcirLean.Transfer.Data
import AcirLean.Linear

/-!
# Transfer: amount ranges, value conservation with no wrap, token consistency

Over the complete printed ACIR of the transfer circuit (23543 opcodes in 92 chunks, in five
part modules assembled by `Data.lean`). Witness names come from the flattened ABI
(`paramNames`, checked by the extractor against the printed parameter lists).
-/

namespace AcirLean.Transfer

open AcirLean

/-! ## The four amount ranges (opcodes 0 to 3) -/

theorem range_amount_in_0_mem : Opcode.range 8 128 ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 0) rfl

theorem range_amount_in_1_mem : Opcode.range 11 128 ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 1) rfl

theorem range_amount_out_0_mem : Opcode.range 14 128 ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 2) rfl

theorem range_amount_out_1_mem : Opcode.range 18 128 ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 3) rfl

/-- In every satisfying assignment the four note amounts are below 2^128. -/
theorem amount_ranges (w : Assignment) (h : circuit.Satisfied w) :
    (w 8).val < 2 ^ 128 ∧ (w 11).val < 2 ^ 128 ∧ (w 14).val < 2 ^ 128 ∧ (w 18).val < 2 ^ 128 :=
  ⟨Circuit.range_of_mem h range_amount_in_0_mem, Circuit.range_of_mem h range_amount_in_1_mem,
   Circuit.range_of_mem h range_amount_out_0_mem, Circuit.range_of_mem h range_amount_out_1_mem⟩

/-- Witnesses 8, 11, 14 and 18 are the ABI parameters `amount_in_0`, `amount_in_1`,
    `amount_out_0` and `amount_out_1`. -/
theorem amount_names :
    paramNames[8]? = some "amount_in_0" ∧ paramNames[11]? = some "amount_in_1" ∧
    paramNames[14]? = some "amount_out_0" ∧ paramNames[18]? = some "amount_out_1" :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Conservation (opcodes 23535 to 23539) -/

theorem sum_in_mem :
    Opcode.assertZero (some 17906) ⟨[], [(1, 8), (1, 11)], 0⟩ ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23535) (by decide +kernel)

theorem range_sum_in_mem : Opcode.range 17906 128 ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23536) (by decide +kernel)

theorem sum_out_mem :
    Opcode.assertZero (some 17907) ⟨[], [(1, 14), (1, 18)], 0⟩ ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23537) (by decide +kernel)

theorem range_sum_out_mem : Opcode.range 17907 128 ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23538) (by decide +kernel)

theorem sums_eq_mem :
    Opcode.assertZero (some 17907) ⟨[], [(1, 17906)], 0⟩ ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23539) (by decide +kernel)

/-- Value conservation over the naturals, with no wrap: in every satisfying assignment,
    `amount_in_0 + amount_in_1 = amount_out_0 + amount_out_1` as natural numbers, and the
    sum is below 2^128. -/
theorem conservation (w : Assignment) (h : circuit.Satisfied w) :
    (w 8).val + (w 11).val = (w 14).val + (w 18).val ∧ (w 8).val + (w 11).val < 2 ^ 128 := by
  obtain ⟨r8, r11, r14, r18⟩ := amount_ranges w h
  have rs := Circuit.range_of_mem h range_sum_in_mem
  have hP := two_pow_128_add_lt_P
  have e1 := Opcode.holds_add (Circuit.holds_of_mem h sum_in_mem) (by omega)
  have e2 := Opcode.holds_add (Circuit.holds_of_mem h sum_out_mem) (by omega)
  have e3 := congrArg Fin.val (Opcode.holds_copy (Circuit.holds_of_mem h sums_eq_mem))
  exact ⟨by omega, by omega⟩

/-! ## Token consistency (opcodes 23540 to 23542) -/

theorem token_in_1_mem : Opcode.assertZero (some 10) ⟨[], [(1, 7)], 0⟩ ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23540) (by decide +kernel)

theorem token_out_0_mem : Opcode.assertZero (some 13) ⟨[], [(1, 7)], 0⟩ ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23541) (by decide +kernel)

theorem token_out_1_mem : Opcode.assertZero (some 17) ⟨[], [(1, 7)], 0⟩ ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 23542) (by decide +kernel)

/-- In every satisfying assignment the four note tokens are equal field elements. -/
theorem token_consistency (w : Assignment) (h : circuit.Satisfied w) :
    w 10 = w 7 ∧ w 13 = w 7 ∧ w 17 = w 7 :=
  ⟨Opcode.holds_copy (Circuit.holds_of_mem h token_in_1_mem),
   Opcode.holds_copy (Circuit.holds_of_mem h token_out_0_mem),
   Opcode.holds_copy (Circuit.holds_of_mem h token_out_1_mem)⟩

/-- Witnesses 7, 10, 13 and 17 are the ABI parameters `token_in_0`, `token_in_1`,
    `token_out_0` and `token_out_1`. -/
theorem token_names :
    paramNames[7]? = some "token_in_0" ∧ paramNames[10]? = some "token_in_1" ∧
    paramNames[13]? = some "token_out_0" ∧ paramNames[17]? = some "token_out_1" :=
  ⟨rfl, rfl, rfl, rfl⟩

end AcirLean.Transfer
