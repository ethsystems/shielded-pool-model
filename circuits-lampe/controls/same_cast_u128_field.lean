import Transfer.CastSteps

namespace Controls.Transfer
open Lampe Deposit.Rules Determinism Transfer.CastSteps



theorem same_cast_u128_field {p Γ st} {v : U 128} {Q}
    (h : Omni p Γ st (.callBuiltin [.u 128] .field Builtin.cast h![v]) Q) :
    Q (some (st, ((v.toNat : ℕ) : Fp p))) := by
  cases h with
  | callBuiltin h =>
    obtain ⟨_, hq⟩ := Builtin.castOmni_inv h
    exact hq

#print axioms same_cast_u128_field
end Controls.Transfer
