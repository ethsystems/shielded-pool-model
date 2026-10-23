import Exec.BitWrapper
namespace Exec.Loop
open Lampe Exec.Basic
set_option backward.isDefEq.respectTransparency false

theorem loop_inv {p Γ w} (lo hi : U w)
    (body : U w → Expr (Tp.denote p) .unit) (Inv : U w → State p → Prop)
    (step : ∀ i st, lo ≤ i → i < hi → Inv i st →
      Omni p Γ st (body i) (fun r => ∃ st', r = some (st', ()) ∧ Inv (i+1) st'))
    (hle : lo ≤ hi) {st} (hinit : Inv lo st) :
    Omni p Γ st (.loop lo hi body)
      (fun r => ∃ st', r = some (st', ()) ∧ Inv hi st') := by
  suffices h : ∀ n i st, hi.toNat - i.toNat = n → lo ≤ i → i ≤ hi → Inv i st →
      Omni p Γ st (.loop i hi body)
        (fun r => ∃ st', r = some (st', ()) ∧ Inv hi st') from
    h _ lo st rfl (BitVec.le_refl _) hle hinit
  intro n
  induction n with
  | zero =>
    intro i st hn hlo hhi hinv
    have heq : i = hi := by
      apply BitVec.eq_of_toNat_eq
      change i.toNat ≤ hi.toNat at hhi
      omega
    subst i
    exact Omni.loopDone (BitVec.le_refl _) ⟨st, rfl, hinv⟩
  | succ n ih =>
    intro i st hn hlo hhi hinv
    have hlt : i < hi := by change i.toNat < hi.toNat; omega
    have hv : (i+1).toNat = i.toNat + 1 := by
      change (i.toNat + 1 % 2^w) % 2^w = i.toNat + 1
      have hw : 1 < 2^w := by
        have := hi.isLt
        change i.toNat < hi.toNat at hlt
        omega
      rw [Nat.mod_eq_of_lt hw]
      apply Nat.mod_eq_of_lt
      have := hi.isLt
      change i.toNat < hi.toNat at hlt
      omega
    apply Omni.loopNext hlt
    apply Omni.letIn (step i st hlo hlt hinv)
    · rintro _ _ ⟨st', heq, hinv'⟩
      cases Option.some.inj heq
      apply ih (i+1) _ (by omega) (by change lo.toNat ≤ (i+1).toNat; change lo.toNat ≤ i.toNat at hlo; omega)
        (by change (i+1).toNat ≤ hi.toNat; change i.toNat < hi.toNat at hlt; omega) hinv'
    · rintro ⟨_, h, _⟩; cases h

theorem loop_exact {p Γ w} (lo hi : U w) (f : Nat → State p)
    (body : U w → Expr (Tp.denote p) .unit)
    (hlo : lo ≤ hi)
    (step : ∀ i, lo ≤ i → i < hi → Omni p Γ (f i.toNat) (body i)
      (fun r => r = some (f (i.toNat+1), ()))) :
    Omni p Γ (f lo.toNat) (.loop lo hi body)
      (fun r => r = some (f hi.toNat, ())) := by
  refine Omni.consequence (loop_inv lo hi body (fun i st => st = f i.toNat) ?_ hlo rfl) ?_
  · intro i st hil hih heq
    subst st
    refine Omni.consequence (step i hil hih) ?_
    intro r hr
    refine ⟨_, hr, ?_⟩
    have hv : (i+1).toNat = i.toNat+1 := by
      have hlt : i.toNat < hi.toNat := hih
      have hh := hi.isLt
      have hw : 1 < 2^w := by omega
      change (i.toNat + 1 % 2^w) % 2^w = i.toNat+1
      rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (by omega)]
    rw [hv]
  · rintro _ ⟨st, hr, rfl⟩; exact hr

#print axioms loop_exact
#print axioms loop_inv
end Exec.Loop
