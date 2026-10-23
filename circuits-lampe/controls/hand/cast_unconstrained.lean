import Deposit.Rules

/-! Must-fail control: the theorem `cast_unconstrained` of the unpatched Lampe, verbatim. On the patched
Lampe (`CastTp` is a proposition) the hand-made instance does not elaborate, so this file must
fail to compile. -/

namespace Controls.DepositCast
open Lampe
variable {p : Prime}

/-- Lampe's cast rule admits any `CastTp` instance: a derivation of `v as Field` may return any
field element. This is why the leaf's timestamp arguments stay existential above. -/
theorem cast_unconstrained {Γ} (st : State p) (v : U 64) (c : Fp p) :
    Omni p Γ st (.callBuiltin [.u 64] .field Builtin.cast h![v]) (fun r => r = some (st, c)) := by
  apply Omni.callBuiltin
  classical
  exact @Builtin.castOmni.ok _ _ (.u 64) .field v _
    ⟨fun {q} _ => if h : q = p then h ▸ c else 0⟩ (by simp [mapToValHeapCondition])

end Controls.DepositCast
