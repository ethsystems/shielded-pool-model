import WithdrawGame.Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.OwnerGame
open GameCorrespondence WithdrawGame
variable {P : PrimSpec} {ι : Type}

/-- Information-theoretic commitment hiding in acceptance-probability distance units. -/
def Hiding [SampleableType P.Salt] (ε : ℝ) : Prop :=
  ∀ t a pk t' a' pk' (test : P.Commitment → ProbComp Bool),
    (do let s ← $ᵗ P.Salt; test (P.commit t a pk s)).boolDistAdvantage
    (do let s ← $ᵗ P.Salt; test (P.commit t' a' pk' s)) ≤ ε

structure Challenge (P : PrimSpec) (ι : Type) where
  prior : List (Intent P ι)
  token : P.Token
  amount : Nat
  funding : P.Address
  left : ι
  right : ι

def Challenge.deposit (c : Challenge P ι) (keys : ι → P.SpendKey)
    (salt : P.Salt) (b : Bool) : DepositData P :=
  ⟨⟨c.token, c.amount, P.derivePub (keys (if b then c.right else c.left)), salt⟩, c.funding⟩

def Challenge.history (c : Challenge P ι) (keys : ι → P.SpendKey)
    (salt : P.Salt) (b : Bool) : List (Tx P) :=
  c.prior.map (Intent.resolve keys) ++ [.deposit (c.deposit keys salt b)]

def Legal (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι)
    (salt : P.Salt) (b : Bool) : Prop :=
  ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
    (c.deposit keys salt b).guard st

structure Adversary (P : PrimSpec) (ι : Type) where
  State : Type
  choose : (ι → P.PubKey) → ProbComp (Challenge P ι × State)
  guess : State → (ι → P.PubKey) → List (PoolGame.Event (gamePrim P)) → ProbComp Bool


theorem public_agreement (c : Challenge P ι) (keys : ι → P.SpendKey) (salt : P.Salt) :
    ChosenWorldGame.PublicAgreement (c.history keys salt false) (c.history keys salt true) := by
  simp [ChosenWorldGame.PublicAgreement, Challenge.history, ChosenWorldGame.publicData, Challenge.deposit]

noncomputable def response (adv : Adversary P ι) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (s : adv.State) (salt : P.Salt) (b : Bool) : ProbComp Bool := do
  let g ← adv.guess s (P.derivePub ∘ keys) (observerView (c.history keys salt b))
  pure (b == g)

noncomputable def challengeExp (sup : P.Token → Prop) (adv : Adversary P ι)
    (keys : ι → P.SpendKey) (c : Challenge P ι) (s : adv.State)
    (salt : P.Salt) (b : Bool) : ProbComp Bool := by
  classical
  exact if Legal sup keys c salt b then
    match RecipientGame.guardedLog sup (c.history keys salt b) with
    | none => $ᵗ Bool
    | some log => do let g ← adv.guess s (P.derivePub ∘ keys) log; pure (b == g)
  else $ᵗ Bool

theorem legal_guarded_log (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (salt : P.Salt) (b : Bool) (h : Legal sup keys c salt b) :
    RecipientGame.guardedLog sup (c.history keys salt b) = some (observerView (c.history keys salt b)) := by
  obtain ⟨st, hs, hg⟩ := h
  have hr : Run sup (c.prior.map (Intent.resolve keys)) st := by
    simpa using RecipientGame.runChecked_sound _ Run.empty hs
  have hfull := Run.step hr (Step.deposit hg)
  simp [RecipientGame.guardedLog, Challenge.history, RecipientGame.runChecked_complete hfull]

noncomputable def draws [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (adv : Adversary P ι) : ProbComp ((ι → P.SpendKey) × Challenge P ι × adv.State × P.Salt × Bool) := do
  let keys ← $ᵗ (ι → P.SpendKey)
  let (c, s) ← adv.choose (P.derivePub ∘ keys)
  let salt ← $ᵗ P.Salt
  let b ← $ᵗ Bool
  pure (keys, c, s, salt, b)

noncomputable def experiment [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ProbComp Bool := do
  let (keys, c, s, salt, b) ← draws adv
  challengeExp sup adv keys c s salt b

noncomputable def unguarded [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (adv : Adversary P ι) : ProbComp Bool := do
  let (keys, c, s, salt, b) ← draws adv
  response adv keys c s salt b

noncomputable def advantage [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  |(Pr[= true | experiment sup adv]).toReal - 1/2|

noncomputable def rejectionProbability [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ := by
  classical
  exact (Pr[= true | do
    let (keys, c, _, salt, b) ← draws adv
    pure (decide (¬ Legal sup keys c salt b))]).toReal

theorem rejection_transport [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) :
    (experiment sup adv).boolDistAdvantage (unguarded adv) ≤ rejectionProbability sup adv / 2 := by
  classical
  have he (keys) (c) (s) (salt) (b) : challengeExp sup adv keys c s salt b =
      if decide (¬ Legal sup keys c salt b) then $ᵗ Bool else response adv keys c s salt b := by
    by_cases h : Legal sup keys c salt b
    · simp [challengeExp, h, legal_guarded_log sup keys c salt b h, response]
    · simp [challengeExp, h]
  have hd := RecipientGame.rejection_distance_le (draws adv)
    (fun a => decide (¬ Legal sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2))
    (fun a => response adv a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
  simpa only [experiment, unguarded, rejectionProbability, he] using hd

noncomputable def branch [SampleableType P.Salt] (adv : Adversary P ι)
    (keys : ι → P.SpendKey) (c : Challenge P ι) (s : adv.State) (b : Bool) : ProbComp Bool := do
  let salt ← $ᵗ P.Salt
  adv.guess s (P.derivePub ∘ keys) (observerView (c.history keys salt b))

theorem branch_distance [SampleableType P.Salt] (adv : Adversary P ι)
    (keys : ι → P.SpendKey) (c : Challenge P ι) (s : adv.State) (ε : ℝ)
    (h : Hiding (P := P) ε) :
    (branch adv keys c s true).boolDistAdvantage (branch adv keys c s false) ≤ ε := by
  let test : P.Commitment → ProbComp Bool := fun cm => adv.guess s (P.derivePub ∘ keys)
    (observerView (c.prior.map (Intent.resolve keys)) ++ [PoolGame.Event.deposit cm])
  have hh := h c.token c.amount (P.derivePub (keys c.right)) c.token c.amount
    (P.derivePub (keys c.left)) test
  have hv (salt : P.Salt) (b : Bool) :
      observerView (c.history keys salt b) =
      observerView (c.prior.map (Intent.resolve keys)) ++
        [.deposit (P.commit c.token c.amount (P.derivePub (keys (if b then c.right else c.left))) salt)] := by
    simp only [Challenge.history, observerView, events, List.map_append, List.map_cons,
      List.map_nil]
    rfl
  simpa only [branch, hv, if_true, Bool.false_eq_true, if_false] using hh

theorem unguarded_bias_le [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (adv : Adversary P ι) (ε : ℝ) (h : Hiding (P := P) ε) :
    |(Pr[= true | unguarded adv]).toReal - 1/2| ≤ ε / 2 := by
  let pref : ProbComp ((ι → P.SpendKey) × Challenge P ι × adv.State) := do
    let keys ← $ᵗ (ι → P.SpendKey)
    let (c, s) ← adv.choose (P.derivePub ∘ keys)
    pure (keys, c, s)
  let f := fun a : (ι → P.SpendKey) × Challenge P ι × adv.State => branch adv a.1 a.2.1 a.2.2 true
  let g := fun a : (ι → P.SpendKey) × Challenge P ι × adv.State => branch adv a.1 a.2.1 a.2.2 false
  have he : 𝒮[unguarded adv] = 𝒮[do
      let a ← pref
      let b ← $ᵗ Bool
      let z ← if b then f a else g a
      pure (b == z)] := by
    simp only [unguarded, draws, pref, bind_assoc, pure_bind]
    apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro keys
    apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro a
    rw [OracleComp.DeferredSampling.evalSPMF_bind_comm]
    apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro b
    cases b <;> simp [f, g, branch, response]
  have hb := ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage pref f g
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half,
    ← OracleComp.probOutput_congr (x := true) rfl he] at hb
  have hd := PoolGame.Averaging.boolDistAdvantage_bind_le_const pref f g ε
    (fun a _ => branch_distance adv a.1 a.2.1 a.2.2 ε h)
  linarith

/-- One distance-unit hiding premise, one terminal deposit, and exact rejection cost. -/
theorem advantage_le [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) (ε : ℝ) (h : Hiding (P := P) ε) :
    advantage sup adv ≤ ε / 2 + rejectionProbability sup adv / 2 := by
  have hu := unguarded_bias_le adv ε h
  have hd := rejection_transport sup adv
  have ht := abs_sub_le (Pr[= true | experiment sup adv]).toReal
    (Pr[= true | unguarded adv]).toReal (1/2)
  unfold advantage ProbComp.boolDistAdvantage at *
  linarith

end LeanShieldedPool.OwnerGame
