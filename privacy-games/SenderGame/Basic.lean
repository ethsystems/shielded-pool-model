import OwnerGame.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.SenderGame
open GameCorrespondence WithdrawGame Transport
variable {P : PrimSpec} {ι : Type}

/-- Output salts are absent from the attacker's message plans. -/
structure Output (P : PrimSpec) (ι : Type) where
  token : P.Token
  amount : Nat
  owner : ι

def Output.note (o : Output P ι) (salt : P.Salt) : NotePlan P ι :=
  ⟨o.token, o.amount, o.owner, salt⟩

structure World (P : PrimSpec) (ι : Type) where
  input : NotePlan P ι
  otherInput : NotePlan P ι
  out1 : Output P ι
  out2 : Output P ι

structure Challenge (P : PrimSpec) (ι : Type) where
  prior : List (Intent P ι)
  left : World P ι
  right : World P ι
  snapshot : Nat

def Challenge.world (c : Challenge P ι) (b : Bool) : World P ι := if b then c.right else c.left

def World.transfer (w : World P ι) (keys : ι → P.SpendKey)
    (s₁ s₂ : P.Salt) (snapshot : Nat) : TransferData P :=
  ⟨keys w.input.owner, w.input.resolve keys, w.otherInput.resolve keys,
    (w.out1.note s₁).resolve keys, (w.out2.note s₂).resolve keys, snapshot⟩

def Challenge.history (c : Challenge P ι) (keys : ι → P.SpendKey)
    (s₁ s₂ : P.Salt) (b : Bool) : List (Tx P) :=
  c.prior.map (Intent.resolve keys) ++ [.transfer ((c.world b).transfer keys s₁ s₂ c.snapshot)]

/-- Two eligible primary notes and both frozen transfer guards. The second input may
be real or zero-valued. The primary owner supplies the single key for both slots. -/
def Legal (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι)
    (s₁ s₂ : P.Salt) : Prop :=
  c.left.input.token = c.right.input.token ∧
  c.left.input.amount = c.right.input.amount ∧
  c.left.input.amount ≠ 0 ∧
  c.left.otherInput.token = c.right.otherInput.token ∧
  c.left.otherInput.amount = c.right.otherInput.amount ∧
  c.left.out1.token = c.right.out1.token ∧ c.left.out1.amount = c.right.out1.amount ∧
  c.left.out2.token = c.right.out2.token ∧ c.left.out2.amount = c.right.out2.amount ∧
  (c.left.input.resolve keys).cm ≠ (c.right.input.resolve keys).cm ∧
  ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
    c.left.input.resolve keys ∈ st.minted ∧ c.right.input.resolve keys ∈ st.minted ∧
    (c.left.transfer keys s₁ s₂ c.snapshot).guard st ∧
    (c.right.transfer keys s₁ s₂ c.snapshot).guard st

structure Adversary (P : PrimSpec) (ι : Type) where
  State : Type
  choose : (ι → P.PubKey) → ProbComp (Challenge P ι × State)
  guess : State → (ι → P.PubKey) → List (PoolGame.Event (gamePrim P)) → ProbComp Bool

theorem public_agreement (c : Challenge P ι) (keys : ι → P.SpendKey) (s₁ s₂ : P.Salt) :
    ChosenWorldGame.PublicAgreement (c.history keys s₁ s₂ false) (c.history keys s₁ s₂ true) := by
  simp [ChosenWorldGame.PublicAgreement, Challenge.history, ChosenWorldGame.publicData, World.transfer]

theorem legal_guards (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (s₁ s₂ : P.Salt) (h : Legal sup keys c s₁ s₂) (b : Bool) :
    ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
      ((c.world b).transfer keys s₁ s₂ c.snapshot).guard st := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, st, hs, _, _, hl, hr⟩ := h
  exact ⟨st, hs, by cases b <;> assumption⟩

theorem legal_guarded_log (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (s₁ s₂ : P.Salt) (h : Legal sup keys c s₁ s₂) (b : Bool) :
    RecipientGame.guardedLog sup (c.history keys s₁ s₂ b) =
      some (observerView (c.history keys s₁ s₂ b)) := by
  obtain ⟨st, hs, hg⟩ := legal_guards sup keys c s₁ s₂ h b
  have hr : Run sup (c.prior.map (Intent.resolve keys)) st := by
    simpa using RecipientGame.runChecked_sound _ Run.empty hs
  have hfull := Run.step hr (Step.transfer hg)
  simp [RecipientGame.guardedLog, Challenge.history, RecipientGame.runChecked_complete hfull]

noncomputable def challengeExp (sup : P.Token → Prop) (adv : Adversary P ι)
    (keys : ι → P.SpendKey) (c : Challenge P ι) (state : adv.State)
    (s₁ s₂ : P.Salt) (b : Bool) : ProbComp Bool := by
  classical
  exact if Legal sup keys c s₁ s₂ then
    match RecipientGame.guardedLog sup (c.history keys s₁ s₂ b) with
    | none => $ᵗ Bool
    | some log => do let g ← adv.guess state (P.derivePub ∘ keys) log; pure (b == g)
  else $ᵗ Bool

noncomputable def draws [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (adv : Adversary P ι) : ProbComp ((ι → P.SpendKey) × Challenge P ι × adv.State × P.Salt × P.Salt × Bool) := do
  let keys ← $ᵗ (ι → P.SpendKey)
  let (c, s) ← adv.choose (P.derivePub ∘ keys)
  let s₁ ← $ᵗ P.Salt
  let s₂ ← $ᵗ P.Salt
  let b ← $ᵗ Bool
  pure (keys, c, s, s₁, s₂, b)

noncomputable def experiment [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ProbComp Bool := do
  let (keys, c, state, s₁, s₂, b) ← draws adv
  challengeExp sup adv keys c state s₁ s₂ b

noncomputable def advantage [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  |(Pr[= true | experiment sup adv]).toReal - 1/2|

noncomputable def rejectionProbability [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ := by
  classical
  exact (Pr[= true | do
    let (keys, c, _, s₁, s₂, _) ← draws adv
    pure (decide (¬ Legal sup keys c s₁ s₂))]).toReal

def first (pk : ι → P.PubKey) (w : World P ι) : ι × P.Commitment := coordinate pk w.input

def second (pk : ι → P.PubKey) (w : World P ι) : ι × P.Commitment :=
  (w.input.owner, cm pk w.otherInput)

/-- The ideal experiment requires two different unqueried coordinates in each world. -/
def Fresh (pk : ι → P.PubKey) (c : Challenge P ι) : Prop :=
  ∀ b, first pk (c.world b) ∉ c.prior.flatMap (queries pk) ∧
    second pk (c.world b) ∉ c.prior.flatMap (queries pk) ∧
    first pk (c.world b) ≠ second pk (c.world b)

def view (pk : ι → P.PubKey) (f : Table P ι) (c : Challenge P ι)
    (s₁ s₂ : P.Salt) (b : Bool) : List (PoolGame.Event (gamePrim P)) :=
  let w := c.world b
  c.prior.map (event pk f) ++ [.transfer (f (first pk w)) (f (second pk w))
    (cm pk (w.out1.note s₁)) (cm pk (w.out2.note s₂))]

theorem view_real (keys : ι → P.SpendKey) (c : Challenge P ι) (s₁ s₂ : P.Salt) (b : Bool) :
    view (P.derivePub ∘ keys) (realTable keys) c s₁ s₂ b =
      observerView (c.history keys s₁ s₂ b) := by
  have he (i : Intent P ι) : event (P.derivePub ∘ keys) (realTable keys) i =
      gameEvent (i.resolve keys).event := by cases i <;> rfl
  simp only [view, Challenge.history, observerView, events, List.map_append,
    List.map_cons, List.map_nil, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => he i

theorem legal_fresh (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (s₁ s₂ : P.Salt) (h : Legal sup keys c s₁ s₂) :
    Fresh (P.derivePub ∘ keys) c := by
  intro b
  obtain ⟨st, hs, hg⟩ := legal_guards sup keys c s₁ s₂ h b
  have run : Run sup (c.prior.map (Intent.resolve keys)) st := by
    simpa using RecipientGame.runChecked_sound _ Run.empty hs
  have step (x : ι × P.Commitment) (hx : realTable keys x ∉ st.nullifiers) :
      x ∉ c.prior.flatMap (queries (P.derivePub ∘ keys)) := by
    intro hm
    apply hx
    apply (run_nullifiers run _).mp
    obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp hm
    apply List.mem_flatMap.mpr
    refine ⟨i.resolve keys, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    rw [← queries_real]
    exact List.mem_map.mpr ⟨_, hm, rfl⟩
  have h₁ := hg.2.2.2.2.2.1
  have h₂ := hg.2.2.2.2.2.2.1
  have hne := hg.2.2.2.2.2.2.2.1
  refine ⟨step _ h₁, step _ h₂, ?_⟩
  intro he
  exact hne (congrArg (realTable keys) he)

noncomputable def response (adv : Adversary P ι) (pk : ι → P.PubKey)
    (f : Table P ι) (c : Challenge P ι) (state : adv.State)
    (s₁ s₂ : P.Salt) (b : Bool) : ProbComp Bool := by
  classical
  exact if Fresh pk c then do
    let g ← adv.guess state pk (view pk f c s₁ s₂ b)
    pure (b == g)
  else $ᵗ Bool

noncomputable def unguarded [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (adv : Adversary P ι) : ProbComp Bool := do
  let (keys, c, state, s₁, s₂, b) ← draws adv
  response adv (P.derivePub ∘ keys) (realTable keys) c state s₁ s₂ b

noncomputable def test [SampleableType P.Salt] (adv : Adversary P ι)
    (pk : ι → P.PubKey) (f : Table P ι) : ProbComp Bool := do
  let (c, state) ← adv.choose pk
  let s₁ ← $ᵗ P.Salt
  let s₂ ← $ᵗ P.Salt
  let b ← $ᵗ Bool
  response adv pk f c state s₁ s₂ b

theorem rejection_transport [SampleableType (ι → P.SpendKey)] [SampleableType P.Salt]
    (sup : P.Token → Prop) (adv : Adversary P ι) :
    (experiment sup adv).boolDistAdvantage (unguarded adv) ≤ rejectionProbability sup adv / 2 := by
  classical
  have he (keys) (c) (state) (s₁) (s₂) (b) : challengeExp sup adv keys c state s₁ s₂ b =
      if decide (¬ Legal sup keys c s₁ s₂) then $ᵗ Bool
      else response adv (P.derivePub ∘ keys) (realTable keys) c state s₁ s₂ b := by
    by_cases h : Legal sup keys c s₁ s₂
    · simp [challengeExp, h, legal_guarded_log sup keys c s₁ s₂ h b, response,
        legal_fresh sup keys c s₁ s₂ h, view_real]
    · simp [challengeExp, h]
  have hd := RecipientGame.rejection_distance_le (draws adv)
    (fun a => decide (¬ Legal sup a.1 a.2.1 a.2.2.2.1 a.2.2.2.2.1))
    (fun a => response adv (P.derivePub ∘ a.1) (realTable a.1)
      a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2)
  simpa only [experiment, unguarded, rejectionProbability, he] using hd

end LeanShieldedPool.SenderGame
