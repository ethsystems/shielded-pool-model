import Deposit.PinnedCast

namespace Controls.DepositCast
open Lampe Deposit.Rules Deposit.PinnedCast



theorem cast_u64_field_plus_one {p Γ st} {v : U 64} {Q}
    (h : Omni p Γ st (.callBuiltin [.u 64] .field Builtin.cast h![v]) Q) :
    Q (some (st, ((v.toNat + 1 : ℕ) : Fp p))) := by
  cases h with
  | callBuiltin h =>
    obtain ⟨_, hq⟩ := Builtin.castOmni_inv h
    exact hq

#print axioms cast_u64_field_plus_one
end Controls.DepositCast
