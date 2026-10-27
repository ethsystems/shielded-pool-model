import CommitROM.Model

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.CommitROM.Model
variable {P : PrimSpec} {cap : Nat}

abbrev commitPrim (P : PrimSpec) (cap : Nat) (hc : Table P cap) : PrimSpec :=
  oraclePrim P cap P.derivePub (fun x => P.nullify x.2 x.1) hc

def lowerImpl (hc : Table P cap) : QueryImpl (Spec P cap) (OracleComp (WithdrawGame.ROM.attackSpec P)) :=
  fun t => match t with
  | .inl coin => liftM ((WithdrawGame.ROM.attackSpec P).query (.inl coin))
  | .inr (.inl x) => pure (hc x)
  | .inr (.inr x) => liftM ((WithdrawGame.ROM.attackSpec P).query (.inr x))

def lower {A : Type} (hc : Table P cap) (oa : OracleComp (Spec P cap) A) :
    OracleComp (WithdrawGame.ROM.attackSpec P) A := simulateQ (lowerImpl hc) oa

theorem lower_bound {A : Type} (hc : Table P cap) (oa : OracleComp (Spec P cap) A)
    (q : Nat) (hq : oa.IsQueryBoundP
      (charged (C := P.Commitment) (aux := WithdrawGame.ROM.hashSpec P)) q) :
    (lower hc oa).IsQueryBoundP (WithdrawGame.ROM.charged P) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => simp [lower]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [lower, simulateQ_bind, simulateQ_query]
    cases t with
    | inl coin =>
      change (liftM ((WithdrawGame.ROM.attackSpec P).query (.inl coin)) >>=
        fun u => lower hc (k u)).IsQueryBoundP (WithdrawGame.ROM.charged P) q
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [WithdrawGame.ROM.charged]), fun u => by
        simpa [charged, WithdrawGame.ROM.charged] using ih u q (by simpa [charged] using hq.2 u)⟩
    | inr hash =>
      cases hash with
      | inl x =>
        change (pure (hc x) >>= fun u => lower hc (k u)).IsQueryBoundP _ q
        rw [pure_bind]
        exact (ih (hc x) (q-1) (by simpa [charged] using hq.2 (hc x))).mono (Nat.sub_le _ _)
      | inr x =>
        change (liftM ((WithdrawGame.ROM.attackSpec P).query (.inr x)) >>=
          fun u => lower hc (k u)).IsQueryBoundP (WithdrawGame.ROM.charged P) q
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr (hq.1.resolve_left (by simp [charged])), fun u => by
          simpa [WithdrawGame.ROM.charged] using ih u (q-1) (by simpa [charged] using hq.2 u)⟩

theorem run_lower {A : Type} (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Table P cap)
    (oa : OracleComp (Spec P cap) A) :
    WithdrawGame.ROM.runAttack hp hn (lower hc oa) = run (WithdrawGame.ROM.answers hp hn) hc oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [lower, WithdrawGame.ROM.runAttack, run, simulateQ_bind, simulateQ_query] at ih ⊢
    cases t with
    | inl coin =>
      simp only [lowerImpl]
      apply bind_congr
      intro u
      exact ih u
    | inr hash =>
      cases hash with
      | inl x =>
        change (pure (hc x) >>= _) = (pure (hc x) >>= _)
        simpa only [pure_bind] using ih (hc x)
      | inr x =>
        simp only [lowerImpl]
        apply bind_congr
        intro u
        exact ih u

end LeanShieldedPool.CommitROM.Model
