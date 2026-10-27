import WithdrawGame.ROM.Kernel
import SenderGame.Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame.ROM
open GameCorrespondence WithdrawGame.ROM
attribute [local instance 200000] chargedDecidable
variable {P : PrimSpec} {ι : Type}

def rebaseOutput (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (o : Output P ι) :
    Output (oraclePrim P hp hn) ι := ⟨o.token,o.amount,o.owner⟩

def rebaseWorld (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (w : World P ι) :
    World (oraclePrim P hp hn) ι :=
  ⟨rebaseNote hp hn w.input, rebaseNote hp hn w.otherInput,
    rebaseOutput hp hn w.out1, rebaseOutput hp hn w.out2⟩

def rebaseChallenge (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (c : Challenge P ι) :
    Challenge (oraclePrim P hp hn) ι :=
  ⟨c.prior.map (rebaseIntent hp hn), rebaseWorld hp hn c.left, rebaseWorld hp hn c.right,c.snapshot⟩

structure Adversary (P : PrimSpec) (ι : Type) where
  State : Type
  choose : (ι → P.PubKey) → OracleComp (attackSpec P) (Challenge P ι × State)
  guess : State → (ι → P.PubKey) → List (PoolGame.Event (gamePrim P)) → OracleComp (attackSpec P) Bool

def QueryBound (adv : Adversary P ι) (qc qg : Nat) : Prop :=
  (∀ pk, (adv.choose pk).IsQueryBoundP (charged P) qc) ∧
  (∀ s pk log, (adv.guess s pk log).IsQueryBoundP (charged P) qg)

def baseAdversary (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) : SenderGame.Adversary P ι where
  State := adv.State
  choose := fun pk => runAttack hp hn (adv.choose pk)
  guess := fun s pk log => runAttack hp hn (adv.guess s pk log)

def gameAdversary (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) : SenderGame.Adversary (oraclePrim P hp hn) ι where
  State := adv.State
  choose := fun pk => do
    let (c,s) ← runAttack hp hn (adv.choose pk)
    pure (rebaseChallenge hp hn c,s)
  guess := fun s pk log => runAttack hp hn (adv.guess s pk (log.map (eventBack hp hn)))

noncomputable def test [SampleableType P.Salt] (adv : Adversary P ι)
    (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) : OracleComp (attackSpec P) Bool := by
  classical
  exact do
    let (c,s) ← adv.choose pk
    let s₁ ← liftComp ($ᵗ P.Salt) (attackSpec P)
    let s₂ ← liftComp ($ᵗ P.Salt) (attackSpec P)
    let b ← liftComp ($ᵗ Bool) (attackSpec P)
    if Fresh pk c then do
      let g ← adv.guess s pk (view pk f c s₁ s₂ b)
      pure (b == g)
    else liftComp ($ᵗ Bool) (attackSpec P)

theorem test_bound [SampleableType P.Salt] (adv : Adversary P ι) (qc qg : Nat)
    (hq : QueryBound adv qc qg) (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) :
    (test adv pk f).IsQueryBoundP (charged P) (qc+qg) := by
  classical
  unfold test
  apply isQueryBoundP_bind (hq.1 pk)
  intro x _
  dsimp only
  refine (isQueryBoundP_bind (n := 0) (m := qg) (coins_bound (P := P) _ 0) ?_).mono (by simp)
  intro s₁ _
  refine (isQueryBoundP_bind (n := 0) (m := qg) (coins_bound (P := P) _ 0) ?_).mono (by simp)
  intro s₂ _
  refine (isQueryBoundP_bind (n := 0) (m := qg) (coins_bound (P := P) _ 0) ?_).mono (by simp)
  intro b _
  by_cases hf : Fresh pk x.1
  · rw [if_pos hf]
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using hq.2 x.2 pk _
  · rw [if_neg hf]
    exact coins_bound _ _

theorem run_coins {α : Type} (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (oa : ProbComp α) :
    runAttack hp hn (liftComp oa (attackSpec P)) = oa := by
  unfold runAttack
  rw [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftComp_left, QueryImpl.simulateQ_toQueryImpl]

theorem run_test [SampleableType P.Salt] (adv : Adversary P ι)
    (hp : P.SpendKey → P.PubKey) (hn : (P.SpendKey × P.Commitment) → P.Nullifier)
    (pk : ι → P.PubKey) (f : WithdrawGame.Transport.Table P ι) :
    runAttack hp hn (test adv pk f) = SenderGame.test (baseAdversary adv hp hn) pk f := by
  unfold test SenderGame.test
  simp only [runAttack, simulateQ_bind, baseAdversary]
  apply bind_congr; intro x
  have hc {α : Type} (oa : ProbComp α) :
      simulateQ (unifFwdAnswerImpl (answers hp hn)) (liftComp oa (attackSpec P)) = oa :=
    run_coins hp hn oa
  simp only [hc]
  apply bind_congr; intro s₁
  apply bind_congr; intro s₂
  apply bind_congr; intro b
  simp only [response]
  split
  · simp only [simulateQ_bind, simulateQ_pure]
  · exact hc _

theorem rebase_fresh (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey) (c : Challenge P ι) :
    Fresh (P := oraclePrim P hp hn) pk (rebaseChallenge hp hn c) ↔ Fresh pk c := by
  simp only [Fresh, rebaseChallenge, List.flatMap_map, rebase_queries]
  apply forall_congr'
  intro b
  cases b <;> rfl

theorem rebase_view (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (f : WithdrawGame.Transport.Table P ι) (c : Challenge P ι) (s₁ s₂ : P.Salt) (b : Bool) :
    (view (P := oraclePrim P hp hn) pk f (rebaseChallenge hp hn c) s₁ s₂ b).map (eventBack hp hn) =
      view pk f c s₁ s₂ b := by
  simp only [view, rebaseChallenge, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, rebase_event]
  cases b <;> rfl

theorem rebase_response (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (f : WithdrawGame.Transport.Table P ι) (c : Challenge P ι) (s : adv.State) (s₁ s₂ : P.Salt) (b : Bool) :
    response (gameAdversary adv hp hn) pk f (rebaseChallenge hp hn c) s s₁ s₂ b =
      response (baseAdversary adv hp hn) pk f c s s₁ s₂ b := by
  simp only [response, gameAdversary, baseAdversary, rebase_view]
  rw [propext (rebase_fresh hp hn pk c)]

theorem rebase_test [SampleableType P.Salt] (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (f : WithdrawGame.Transport.Table P ι) :
    SenderGame.test (gameAdversary adv hp hn) pk f = SenderGame.test (baseAdversary adv hp hn) pk f := by
  simp only [SenderGame.test, gameAdversary, baseAdversary, bind_assoc, pure_bind]
  apply bind_congr; intro x
  apply bind_congr; intro s₁
  apply bind_congr; intro s₂
  apply bind_congr; intro b
  exact rebase_response adv hp hn pk f x.1 x.2 s₁ s₂ b

end LeanShieldedPool.SenderGame.ROM
