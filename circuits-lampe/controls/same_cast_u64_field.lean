import Deposit.PinnedCast

namespace Controls.DepositCast
open Lampe Deposit.Rules Deposit.PinnedCast



theorem same_cast_u64_field {p Γ st} {v : U 64} {Q}
    (h : Omni p Γ st (.callBuiltin [.u 64] .field Builtin.cast h![v]) Q) :
    Q (some (st, ((v.toNat : ℕ) : Fp p))) := by
  cases h with
  | callBuiltin h =>
    obtain ⟨_, hq⟩ := Builtin.castOmni_inv h
    exact hq

#print axioms same_cast_u64_field
end Controls.DepositCast
