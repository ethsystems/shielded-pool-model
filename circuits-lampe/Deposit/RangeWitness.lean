import Deposit.Steps

/-! The range call in deposit main has an outcome in every accepting derivation. -/

namespace Deposit.Rules
open Lampe

set_option pp.deepTerms false in
set_option pp.maxSteps 2000 in
set_option maxHeartbeats 400000 in
theorem range_wit {p} (amount : Fp p) :
    Wit p «deposit-0.0.0».env
      («std-1.0.0-beta.21::field::assert_max_bit_size».call h![(128 : U 32)] h![amount]) := by
  apply wit_call Deposit.Range.range_unique
  dsimp only [«std-1.0.0-beta.21::field::assert_max_bit_size»]
  repeat' first
    | (apply wit_let_pure; intro)
    | (apply wit_let_cast; intro)
    | apply wit_let_constU
    | apply wit_let_litU
    | apply wit_skip

#print axioms range_wit
end Deposit.Rules
