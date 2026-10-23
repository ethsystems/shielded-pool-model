import Transfer.CastSteps

namespace Controls.Transfer
open Lampe Deposit.Rules Determinism Transfer.CastSteps



theorem cast_u128_field_plus_one {p Γ st} {v : U 128} {Q}
    (h : Omni p Γ st (.callBuiltin [.u 128] .field Builtin.cast h![v]) Q) :
    Q (some (st, ((v.toNat + 1 : ℕ) : Fp p))) := by
  cases h with
  | callBuiltin h =>
    obtain ⟨_, hq⟩ := Builtin.castOmni_inv h
    exact hq

#print axioms cast_u128_field_plus_one
end Controls.Transfer
