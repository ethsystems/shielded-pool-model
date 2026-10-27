import WithdrawGame.RejectionTerms
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.LoggingOracle

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame.ROM
open GameCorrespondence
variable {P : PrimSpec} {ι : Type}

/-- The domains are disjoint: a public-key query and a nullifier query never share a cell. -/
abbrev hashSpec (P : PrimSpec) :=
  (P.SpendKey →ₒ P.PubKey) + ((P.SpendKey × P.Commitment) →ₒ P.Nullifier)

abbrev attackSpec (P : PrimSpec) := unifSpec + hashSpec P

/-- Private random coins are free; either hash query consumes one unit. -/
def charged (P : PrimSpec) : (attackSpec P).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance chargedDecidable (P : PrimSpec) : DecidablePred (charged P) :=
  fun q => match q with
    | .inl _ => isFalse (fun h => h)
    | .inr _ => isTrue trivial

abbrev oraclePrim (P : PrimSpec) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) : PrimSpec :=
  { P with derivePub := hp, nullify := fun cm k => hn (k, cm) }

def rebaseNote (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (n : NotePlan P ι) :
    NotePlan (oraclePrim P hp hn) ι := ⟨n.token, n.amount, n.owner, n.salt⟩

def rebaseIntent (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) :
    Intent P ι → Intent (oraclePrim P hp hn) ι
  | .deposit n a => .deposit (rebaseNote hp hn n) a
  | .transfer i n₁ n₂ o₁ o₂ s => .transfer i
      (rebaseNote hp hn n₁) (rebaseNote hp hn n₂) (rebaseNote hp hn o₁) (rebaseNote hp hn o₂) s
  | .withdraw n a s => .withdraw (rebaseNote hp hn n) a s

def rebaseChallenge (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (c : Challenge P ι) :
    Challenge (oraclePrim P hp hn) ι :=
  ⟨c.prior.map (rebaseIntent hp hn), rebaseNote hp hn c.left, rebaseNote hp hn c.right,
    c.recipient, c.snapshot⟩

def eventBack (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) :
    PoolGame.Event (gamePrim (oraclePrim P hp hn)) → PoolGame.Event (gamePrim P)
  | .deposit cm => .deposit cm
  | .transfer a b c d => .transfer a b c d
  | .withdraw nf => .withdraw nf

structure Adversary (P : PrimSpec) (ι : Type) where
  State : Type
  choose : (ι → P.PubKey) → OracleComp (attackSpec P) (Challenge P ι × State)
  guess : State → (ι → P.PubKey) → List (PoolGame.Event (gamePrim P)) →
    OracleComp (attackSpec P) Bool

/-- Pointwise phase bounds. The total attacker hash budget is qChoose + qGuess.
Challenger computations are outside this budget. -/
def QueryBound (adv : Adversary P ι) (qChoose qGuess : Nat) : Prop :=
  (∀ pk, (adv.choose pk).IsQueryBoundP (charged P) qChoose) ∧
  (∀ s pk log, (adv.guess s pk log).IsQueryBoundP (charged P) qGuess)

def answers (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) : QueryImpl (hashSpec P) Id :=
  QueryImpl.ofFn hp + QueryImpl.ofFn hn

def runAttack {α : Type} (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier)
    (oa : OracleComp (attackSpec P) α) : ProbComp α :=
  simulateQ (unifFwdAnswerImpl (answers hp hn)) oa

def gameAdversary (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) :
    WithdrawGame.Adversary (oraclePrim P hp hn) ι where
  State := adv.State
  choose := fun pk => do
    let (c, s) ← runAttack hp hn (adv.choose pk)
    pure (rebaseChallenge hp hn c, s)
  guess := fun s pk log => runAttack hp hn (adv.guess s pk (log.map (eventBack hp hn)))

/-- Finite eager ROM: two independent uniform tables, one shared realization across both
attacker phases and every challenger operation. Honest account keys remain uniform. -/
noncomputable def experiment [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  WithdrawGame.experiment (P := oraclePrim P hp hn) sup (gameAdversary adv hp hn)

noncomputable def advantage [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  |(Pr[= true | experiment sup adv]).toReal - 1 / 2|

noncomputable def rejectionProbability [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  (Pr[= true | do
    let hp ← $ᵗ (P.SpendKey → P.PubKey)
    let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
    let b ← $ᵗ Bool
    let keys ← $ᵗ (ι → P.SpendKey)
    let (c, _) ← (gameAdversary adv hp hn).choose (hp ∘ keys)
    pure (WithdrawGame.rejected (P := oraclePrim P hp hn) sup keys c b)]).toReal

/-- Cached/eager equivalence for each of the two independent oracle domains.
The instantiated declaration is VCV-io's full finite-table random-oracle theorem. -/
theorem public_oracle_lazy_eager [DecidableEq P.SpendKey] [Finite P.SpendKey]
    [Finite P.PubKey] [Nonempty P.PubKey] [SampleableType P.PubKey]
    [SampleableType (P.SpendKey → P.PubKey)] {α : Type}
    (oa : OracleComp (P.SpendKey →ₒ P.PubKey) α) :
    𝒮[(simulateQ randomOracle oa).run' ∅] =
      𝒮[do let hp ← $ᵗ (P.SpendKey → P.PubKey); pure (evalWithAnswerFn (QueryImpl.ofFn hp) oa)] := by
  exact evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable oa

theorem nullifier_oracle_lazy_eager [DecidableEq (P.SpendKey × P.Commitment)]
    [Finite P.SpendKey] [Finite P.Commitment]
    [Finite P.Nullifier] [Nonempty P.Nullifier] [SampleableType P.Nullifier]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)] {α : Type}
    (oa : OracleComp ((P.SpendKey × P.Commitment) →ₒ P.Nullifier) α) :
    𝒮[(simulateQ randomOracle oa).run' ∅] =
      𝒮[do let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier);
           pure (evalWithAnswerFn (QueryImpl.ofFn hn) oa)] := by
  exact evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable oa

/-- A checked first-hit kernel, not yet a theorem about experiment above.
The strategy here sees only hit/miss replies; a ROM transcript factorization is still required. -/
theorem hidden_key_probe_bound {K : Type} [Fintype K] [DecidableEq K]
    [SampleableType K] (n q : Nat) (σ : List Bool → K) :
    Pr[fun b : Bool => b = true | hiddenReadList ($ᵗ K) q σ n] ≤
      (n : ℝ≥0∞) * q / Fintype.card K := by
  have h := probEvent_hiddenReadList_le
    (oa := ($ᵗ K)) (ε := (Fintype.card K : ℝ≥0∞)⁻¹)
    (fun k => (probOutput_uniformSample K k).le) q σ n
  simpa only [div_eq_mul_inv, mul_assoc] using h

def baseAdversary (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) : WithdrawGame.Adversary P ι where
  State := adv.State
  choose := fun pk => runAttack hp hn (adv.choose pk)
  guess := fun s pk log => runAttack hp hn (adv.guess s pk log)

theorem rebase_queries (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (i : Intent P ι) :
    Transport.queries (P := oraclePrim P hp hn) pk (rebaseIntent hp hn i) = Transport.queries pk i := by
  cases i <;> rfl

theorem rebase_fresh (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (c : Challenge P ι) :
    Transport.Fresh (P := oraclePrim P hp hn) pk (rebaseChallenge hp hn c) ↔ Transport.Fresh pk c := by
  simp [Transport.Fresh, rebaseChallenge, List.flatMap_map, rebase_queries]
  rfl

theorem rebase_event (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (f : Transport.Table P ι) (i : Intent P ι) :
    eventBack hp hn (Transport.event pk f (rebaseIntent hp hn i)) = Transport.event pk f i := by
  cases i <;> rfl

theorem rebase_view (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (f : Transport.Table P ι) (c : Challenge P ι) (b : Bool) :
    (Transport.view (P := oraclePrim P hp hn) pk f (rebaseChallenge hp hn c) b).map (eventBack hp hn) =
      Transport.view pk f c b := by
  simp only [Transport.view, rebaseChallenge, List.map_append, List.map_cons,
    List.map_nil, List.map_map, Function.comp_def, rebase_event]
  cases b <;> rfl

theorem rebase_response (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (f : Transport.Table P ι) (c : Challenge P ι) (s : adv.State) (b : Bool) :
    Transport.response (gameAdversary adv hp hn) pk f (rebaseChallenge hp hn c) s b =
      Transport.response (baseAdversary adv hp hn) pk f c s b := by
  simp only [Transport.response, gameAdversary, baseAdversary, rebase_view]
  rw [propext (rebase_fresh hp hn pk c)]

theorem rebase_test (adv : Adversary P ι) (hp : P.SpendKey → P.PubKey)
    (hn : (P.SpendKey × P.Commitment) → P.Nullifier) (pk : ι → P.PubKey)
    (f : Transport.Table P ι) :
    Transport.test (gameAdversary adv hp hn) pk f =
      Transport.test (baseAdversary adv hp hn) pk f := by
  simp only [Transport.test, gameAdversary, baseAdversary, bind_assoc, pure_bind]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  exact rebase_response adv hp hn pk f a.1 a.2 b

noncomputable def realUnguarded [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (adv : Adversary P ι) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  let keys ← $ᵗ (ι → P.SpendKey)
  Transport.test (baseAdversary adv hp hn) (hp ∘ keys) (fun x => hn (keys x.1, x.2))

/-- Reference game: independent public keys and independent per-account nullifier tables.
The attacker's two hash oracles are separate from these private account tables. -/
noncomputable def ideal [SampleableType (ι → P.PubKey)]
    [SampleableType (Transport.Table P ι)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (adv : Adversary P ι) : ProbComp Bool := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  let pk ← $ᵗ (ι → P.PubKey)
  let f ← $ᵗ (Transport.Table P ι)
  Transport.test (baseAdversary adv hp hn) pk f

theorem ideal_fair [Finite ι] [Finite P.Commitment]
    [Finite P.Nullifier] [Nonempty P.Nullifier] [SampleableType P.Nullifier]
    [SampleableType (ι → P.PubKey)] [SampleableType (Transport.Table P ι)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (adv : Adversary P ι) : Pr[= true | ideal adv] = 1 / 2 := by
  unfold ideal
  rw [probOutput_bind_of_const _ (r := 1 / 2)]
  · simp
  · intro hp _
    rw [probOutput_bind_of_const _ (r := 1 / 2)]
    · simp
    · intro hn _
      rw [probOutput_bind_of_const _ (r := 1 / 2)]
      · simp
      · intro pk _
        simpa using OracleComp.probOutput_congr (x := true) rfl
          (Transport.ideal_test_fair (baseAdversary adv hp hn) pk)

structure Draw (adv : Adversary P ι) where
  hp : P.SpendKey → P.PubKey
  hn : (P.SpendKey × P.Commitment) → P.Nullifier
  keys : ι → P.SpendKey
  challenge : Challenge P ι
  state : adv.State
  bit : Bool

noncomputable def draws [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (adv : Adversary P ι) : ProbComp (Draw adv) := do
  let hp ← $ᵗ (P.SpendKey → P.PubKey)
  let hn ← $ᵗ ((P.SpendKey × P.Commitment) → P.Nullifier)
  let b ← $ᵗ Bool
  let keys ← $ᵗ (ι → P.SpendKey)
  let (c, s) ← runAttack hp hn (adv.choose (hp ∘ keys))
  pure ⟨hp, hn, keys, c, s, b⟩

noncomputable def drawRejected (sup : P.Token → Prop) {adv : Adversary P ι} (a : Draw adv) : Bool :=
  WithdrawGame.rejected (P := oraclePrim P a.hp a.hn) sup a.keys
    (rebaseChallenge a.hp a.hn a.challenge) a.bit

noncomputable def drawResponse {adv : Adversary P ι} (a : Draw adv) : ProbComp Bool :=
  Transport.response (baseAdversary adv a.hp a.hn) (a.hp ∘ a.keys)
    (fun x => a.hn (a.keys x.1, x.2)) a.challenge a.state a.bit

theorem experiment_draws [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (sup : P.Token → Prop) (adv : Adversary P ι) :
    experiment sup adv = (do
      let a ← draws adv
      if drawRejected sup a then $ᵗ Bool else drawResponse a) := by
  simp only [experiment, WithdrawGame.experiment, gameAdversary, draws, bind_assoc, pure_bind,
    drawRejected, drawResponse, Transport.challenge_eq_reject_response]
  apply bind_congr
  intro hp
  apply bind_congr
  intro hn
  apply bind_congr
  intro b
  apply bind_congr
  intro keys
  apply bind_congr
  intro a
  exact congrArg (fun r => if WithdrawGame.rejected (P := oraclePrim P hp hn) sup keys
    (rebaseChallenge hp hn a.1) b then ($ᵗ Bool : ProbComp Bool) else r)
    (rebase_response adv hp hn (hp ∘ keys) (fun x => hn (keys x.1, x.2)) a.1 a.2 b)

theorem unguarded_draws [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (adv : Adversary P ι) :
    𝒮[realUnguarded adv] = 𝒮[draws adv >>= drawResponse] := by
  simp only [realUnguarded, draws, bind_assoc, pure_bind, drawResponse]
  apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
  intro hp
  apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
  intro hn
  rw [OracleComp.DeferredSampling.evalSPMF_bind_comm ($ᵗ Bool)]
  apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
  intro keys
  simp only [Transport.test, baseAdversary]
  exact (OracleComp.DeferredSampling.evalSPMF_bind_comm _ _ _).symm

theorem guarded_distance [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (sup : P.Token → Prop) (adv : Adversary P ι) :
    (experiment sup adv).boolDistAdvantage (realUnguarded adv) ≤
      rejectionProbability sup adv / 2 := by
  have h := RecipientGame.rejection_distance_le (draws adv) (drawRejected sup) drawResponse
  rw [← experiment_draws] at h
  unfold ProbComp.boolDistAdvantage at *
  rw [OracleComp.probOutput_congr (x := true) rfl (unguarded_draws adv)]
  simpa only [draws, drawRejected, rejectionProbability, gameAdversary,
    bind_assoc, pure_bind] using h

/-- Exact missing lemma: derive this distance bound from QueryBound. The first term
charges key hits across both hash domains; the second charges repeated account keys.
No declaration in this module proves OracleSwitch from QueryBound. -/
def OracleSwitch [Fintype ι] [Fintype P.SpendKey] [SampleableType (ι → P.SpendKey)]
    [SampleableType (ι → P.PubKey)] [SampleableType (Transport.Table P ι)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (adv : Adversary P ι) (qChoose qGuess : Nat) : Prop :=
  (realUnguarded adv).boolDistAdvantage (ideal adv) ≤
    (Fintype.card ι : ℝ) * (qChoose + qGuess) / Fintype.card P.SpendKey +
    (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card P.SpendKey

/-- Conditional transport only. OracleSwitch is the open ROM reduction, not an established
consequence of the query bound. The ideal and guard steps are discharged here. -/
theorem advantage_le_of_oracle_switch [Fintype ι] [Fintype P.SpendKey]
    [Finite P.Commitment] [Finite P.Nullifier] [Nonempty P.Nullifier]
    [SampleableType P.Nullifier] [SampleableType (ι → P.SpendKey)]
    [SampleableType (ι → P.PubKey)] [SampleableType (Transport.Table P ι)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (sup : P.Token → Prop) (adv : Adversary P ι) (qChoose qGuess : Nat)
    (hSwitch : OracleSwitch adv qChoose qGuess) :
    advantage sup adv ≤
      (Fintype.card ι : ℝ) * (qChoose + qGuess) / Fintype.card P.SpendKey +
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card P.SpendKey +
      rejectionProbability sup adv / 2 := by
  have hd := guarded_distance sup adv
  have hi := ideal_fair adv
  have ht := abs_sub_le (Pr[= true | experiment sup adv]).toReal
    (Pr[= true | realUnguarded adv]).toReal (1 / 2)
  unfold OracleSwitch ProbComp.boolDistAdvantage at hSwitch
  rw [hi] at hSwitch
  norm_num at hSwitch
  unfold advantage ProbComp.boolDistAdvantage at *
  linarith

/-- This proposition names the full target; it is not a proved security claim. -/
def PrivacyGoal [Fintype ι] [Fintype P.SpendKey] [SampleableType (ι → P.SpendKey)]
    [SampleableType (P.SpendKey → P.PubKey)]
    [SampleableType ((P.SpendKey × P.Commitment) → P.Nullifier)]
    (sup : P.Token → Prop) (adv : Adversary P ι) (qChoose qGuess : Nat) : Prop :=
  QueryBound adv qChoose qGuess →
  advantage sup adv ≤
    (Fintype.card ι : ℝ) * (qChoose + qGuess) / Fintype.card P.SpendKey +
    (Fintype.card ι : ℝ) * (Fintype.card ι - 1) / Fintype.card P.SpendKey +
    rejectionProbability sup adv / 2

end LeanShieldedPool.WithdrawGame.ROM
