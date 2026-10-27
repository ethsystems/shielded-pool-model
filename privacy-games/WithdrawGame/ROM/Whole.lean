import WithdrawGame.ROM.Coupling

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.WithdrawGame.ROM
variable {P : PrimSpec} {ι : Type}

/-- The common prefix and terminal response share one oracle computation. -/
noncomputable def whole (adv : Adversary P ι) (pk : ι → P.PubKey)
    (f : Transport.Table P ι) (b : Bool) : OracleComp (attackSpec P) Bool := by
  classical
  exact do
    let (c, s) ← adv.choose pk
    if Transport.Fresh pk c then do
      let g ← adv.guess s pk (Transport.view pk f c b)
      pure (b == g)
    else liftComp ($ᵗ Bool) (attackSpec P)

theorem coins_bound {α : Type} (oa : ProbComp α) (q : Nat) :
    (liftComp oa (attackSpec P)).IsQueryBoundP (charged P) q := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [liftComp_bind]
    change IsQueryBoundP (liftM ((attackSpec P).query (.inl t)) >>=
      fun u => liftComp (k u) (attackSpec P)) (charged P) q
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [charged]), fun u => by simpa [charged] using ih u⟩

theorem whole_bound (adv : Adversary P ι) (qc qg : Nat) (h : QueryBound adv qc qg)
    (pk : ι → P.PubKey) (f : Transport.Table P ι) (b : Bool) :
    (whole adv pk f b).IsQueryBoundP (charged P) (qc + qg) := by
  classical
  unfold whole
  apply isQueryBoundP_bind (h.1 pk)
  intro x _
  dsimp only
  by_cases hf : Transport.Fresh pk x.1
  · rw [if_pos hf]
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using h.2 x.2 pk _
  · rw [if_neg hf]
    exact coins_bound _ _

theorem run_whole (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier)
    (pk : ι → P.PubKey) (f : Transport.Table P ι) (b : Bool) :
    runAttack hp hn (whole adv pk f b) = (do
      let (c,s) ← runAttack hp hn (adv.choose pk)
      Transport.response (baseAdversary adv hp hn) pk f c s b) := by
  simp only [whole, runAttack, simulateQ_bind]
  apply bind_congr
  intro x
  simp only [Transport.response, baseAdversary]
  split
  · simp [runAttack]
  · rw [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftComp_left]
    rfl

theorem test_eq_whole (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier)
    (pk : ι → P.PubKey) (f : Transport.Table P ι) :
    𝒮[Transport.test (baseAdversary adv hp hn) pk f] =
      𝒮[do let b ← $ᵗ Bool; runAttack hp hn (whole adv pk f b)] := by
  simp only [run_whole, Transport.test, baseAdversary]
  exact evalSPMF_bind_comm _ _ _

end LeanShieldedPool.WithdrawGame.ROM
