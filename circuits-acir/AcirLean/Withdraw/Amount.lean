import AcirLean.Withdraw.Data

/-!
# Withdraw: the public input `amount` is below 2^128 in every satisfying assignment

Over the complete printed ACIR of the withdraw circuit (11508 opcodes in 45 chunks, in three
part modules assembled by `Data.lean`).
-/

namespace AcirLean.Withdraw

open AcirLean

/-- Opcode 362 of the withdraw circuit is `BLACKBOX::RANGE input: w2, bits: 128`. -/
theorem range_amount_mem : Opcode.range 2 128 ∈ circuit.opcodes :=
  List.mem_of_getElem? (l := opcodes) (i := 362) (by decide +kernel)

/-- Every assignment that satisfies all opcodes of the withdraw ACIR gives witness 2 a
    canonical value below 2^128. -/
theorem amount_lt_two_pow_128 (w : Assignment) (h : circuit.Satisfied w) :
    (w 2).val < 2 ^ 128 :=
  Circuit.range_of_mem h range_amount_mem

/-- Witness 2 is the third public parameter, and its flattened ABI name is `amount`
    (`paramNames`, the list that the extractor checks against the ABI sizes). -/
theorem amount_is_public_input_2 :
    circuit.publicParams[2]? = some 2 ∧ paramNames[2]? = some "amount" :=
  ⟨rfl, rfl⟩

end AcirLean.Withdraw
