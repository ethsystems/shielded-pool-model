import ChosenWorldGame.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.WithdrawGame
open GameCorrespondence
variable {P : PrimSpec} {ι : Type}

/-- An attacker can name an account, but cannot supply its spending key. -/
structure NotePlan (P : PrimSpec) (ι : Type) where
  token : P.Token
  amount : Nat
  owner : ι
  salt : P.Salt

def NotePlan.resolve (keys : ι → P.SpendKey) (n : NotePlan P ι) : Note P :=
  ⟨n.token, n.amount, P.derivePub (keys n.owner), n.salt⟩

/-- The challenger inserts every spending witness. All operation choices are public-key only. -/
inductive Intent (P : PrimSpec) (ι : Type) where
  | deposit (note : NotePlan P ι) (funding : P.Address)
  | transfer (account : ι) (in1 in2 out1 out2 : NotePlan P ι) (snapshot : Nat)
  | withdraw (note : NotePlan P ι) (recipient : P.Address) (snapshot : Nat)

def Intent.resolve (keys : ι → P.SpendKey) : Intent P ι → Tx P
  | .deposit n a => .deposit ⟨n.resolve keys, a⟩
  | .transfer i n1 n2 o1 o2 s =>
      .transfer ⟨keys i, n1.resolve keys, n2.resolve keys, o1.resolve keys, o2.resolve keys, s⟩
  | .withdraw n a s => .withdraw ⟨keys n.owner, n.resolve keys, a, s⟩

/-- A common ordered prefix and a terminal withdrawal from one of two earlier notes. -/
structure Challenge (P : PrimSpec) (ι : Type) where
  prior : List (Intent P ι)
  left : NotePlan P ι
  right : NotePlan P ι
  recipient : P.Address
  snapshot : Nat

def Challenge.withdrawal (c : Challenge P ι) (keys : ι → P.SpendKey) (b : Bool) :
    WithdrawData P :=
  let n := if b then c.right else c.left
  ⟨keys n.owner, n.resolve keys, c.recipient, c.snapshot⟩

def Challenge.history (c : Challenge P ι) (keys : ι → P.SpendKey) (b : Bool) : List (Tx P) :=
  c.prior.map (Intent.resolve keys) ++ [.withdraw (c.withdrawal keys b)]

/-- Both exact notes were minted, have distinct commitments, and are eligible at the common root.
The prefix passes every frozen guard. Token, amount, recipient, snapshot and position agree. -/
def Legal (sup : P.Token → Prop) (keys : ι → P.SpendKey) (c : Challenge P ι) : Prop :=
  c.left.token = c.right.token ∧ c.left.amount = c.right.amount ∧
  (c.left.resolve keys).cm ≠ (c.right.resolve keys).cm ∧
  ∃ st, RecipientGame.runChecked (St.empty P sup) (c.prior.map (Intent.resolve keys)) = some st ∧
    c.left.resolve keys ∈ st.minted ∧ c.right.resolve keys ∈ st.minted ∧
    (c.withdrawal keys false).guard st ∧ (c.withdrawal keys true).guard st

/-- Public keys are auxiliary input, not extra events. The event view is exactly the recipient game's.
It contains no proofs, encrypted payloads, or call metadata. -/
structure Adversary (P : PrimSpec) (ι : Type) where
  State : Type
  choose : (ι → P.PubKey) → ProbComp (Challenge P ι × State)
  guess : State → (ι → P.PubKey) → List (PoolGame.Event (gamePrim P)) → ProbComp Bool

noncomputable def challengeExp (sup : P.Token → Prop) (adv : Adversary P ι)
    (keys : ι → P.SpendKey) (c : Challenge P ι) (state : adv.State) (b : Bool) : ProbComp Bool := by
  classical
  exact if Legal sup keys c then
    match RecipientGame.guardedLog sup (c.history keys b) with
    | none => $ᵗ Bool
    | some log => do
      let guess ← adv.guess state (P.derivePub ∘ keys) log
      pure (b == guess)
  else $ᵗ Bool

/-- The bit is drawn first but never given to either attacker phase. Keys are fresh independent
uniform account keys. The attacker chooses notes, amounts, recipients and prefix order. -/
noncomputable def experiment [SampleableType (ι → P.SpendKey)]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let keys ← $ᵗ (ι → P.SpendKey)
  let (c, state) ← adv.choose (P.derivePub ∘ keys)
  challengeExp sup adv keys c state b

noncomputable def advantage [SampleableType (ι → P.SpendKey)]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  |(Pr[= true | experiment sup adv]).toReal - 1 / 2|

theorem legal_public_agreement (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (h : Legal sup keys c) :
    ChosenWorldGame.PublicAgreement (c.history keys false) (c.history keys true) := by
  rcases h with ⟨ht, ha, _⟩
  simp [ChosenWorldGame.PublicAgreement, Challenge.history, ChosenWorldGame.publicData, Challenge.withdrawal,
    NotePlan.resolve, ht, ha]

theorem legal_realizable (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (h : Legal sup keys c) (b : Bool) :
    ∃ st, Run sup (c.history keys b) st := by
  rcases h with ⟨_, _, _, st, hs, _, _, hl, hr⟩
  have run : Run sup (c.prior.map (Intent.resolve keys)) st := by
    simpa using RecipientGame.runChecked_sound _ Run.empty hs
  exact ⟨_, Run.step run (Step.withdraw (by cases b <;> assumption))⟩

theorem legal_guarded_log (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (h : Legal sup keys c) (b : Bool) :
    RecipientGame.guardedLog sup (c.history keys b) = some (observerView (c.history keys b)) := by
  obtain ⟨st, run⟩ := legal_realizable sup keys c h b
  simp [RecipientGame.guardedLog, RecipientGame.runChecked_complete run]

/-- Illegal choices receive the same fair-win convention as rejected executions. -/
noncomputable def rejected (sup : P.Token → Prop) (keys : ι → P.SpendKey)
    (c : Challenge P ι) (b : Bool) : Bool := by
  classical
  exact if Legal sup keys c then
    (RecipientGame.runChecked (St.empty P sup) (c.history keys b)).isNone
  else true

noncomputable def rejectionProbability [SampleableType (ι → P.SpendKey)]
    (sup : P.Token → Prop) (adv : Adversary P ι) : ℝ :=
  (Pr[= true | do
    let b ← $ᵗ Bool
    let keys ← $ᵗ (ι → P.SpendKey)
    let (c, _) ← adv.choose (P.derivePub ∘ keys)
    pure (rejected sup keys c b)]).toReal

/-- An eager random function is uniform over the full finite table. This premise gives the
attacker the entire table, but no correlated public key. -/
def PlainPRF [SampleableType (P.Commitment → P.Nullifier)] (keygen : ProbComp P.SpendKey) (epsPRF : ℝ) : Prop :=
  ∀ test : (P.Commitment → P.Nullifier) → ProbComp Bool,
    |(Pr[= true | do let k ← keygen; test (fun cm => P.nullify cm k)]).toReal -
      (Pr[= true | do let f ← $ᵗ (P.Commitment → P.Nullifier); test f]).toReal| ≤ epsPRF

/-- The additional assumption needed when derived public keys accompany the oracle. -/
def PublicKeyPRF [SampleableType (P.Commitment → P.Nullifier)] (keygen : ProbComp P.SpendKey) (epsPRF : ℝ) : Prop :=
  ∀ test : P.PubKey → (P.Commitment → P.Nullifier) → ProbComp Bool,
    |(Pr[= true | do let k ← keygen; test (P.derivePub k) (fun cm => P.nullify cm k)]).toReal -
      (Pr[= true | do
        let k ← keygen
        let f ← $ᵗ (P.Commitment → P.Nullifier)
        test (P.derivePub k) f]).toReal| ≤ epsPRF

/-- Hiding, ordinary PRF security and the two spreads remain separate named requirements.
The obstruction below shows that this record does not imply withdrawal privacy. -/
structure Assumptions (P : PrimSpec) [SampleableType P.Salt] [SampleableType P.SpendKey]
    [SampleableType (P.Commitment → P.Nullifier)]
    (qC qN : Nat) where
  epsHiding : ℝ
  hiding_bound : ∀ t a pk t' a' pk' (test : P.Commitment → ProbComp Bool),
    |(Pr[= true | do let s ← $ᵗ P.Salt; test (P.commit t a pk s)]).toReal -
      (Pr[= true | do let s ← $ᵗ P.Salt; test (P.commit t' a' pk' s)]).toReal| ≤ epsHiding
  epsPRF : ℝ
  prf : PlainPRF (P := P) ($ᵗ P.SpendKey) epsPRF
  commitmentSpread : RecipientGame.Rejection.CommitmentSpread (P := P) qC
  nullifierSpread : ChainGame.NullifierSpread (P := P) qN

end LeanShieldedPool.WithdrawGame
