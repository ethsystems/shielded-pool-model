/-
The game interface: the shielded pool's observer view as a VCVio oracle interface, and the
two-world transfer indistinguishability game against it. Illegal challenges return a fair
win bit.

Not part of the gated model build. Elaborated against VCV-io `dfc7ff07` (Lean v4.33.1,
Mathlib `0df444a360`, the Mathlib of the gated model).
-/

import VCVio.CryptoFoundations.CommitmentScheme
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.SecExp

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace PoolGame

/-! ## Repeated model declarations

`PrimSpec` and `Event` repeat, word for word, `LeanShieldedPool/Pool/State.lean` lines
40-53 and `LeanShieldedPool/Pool/Events.lean` lines 17-20 of the gated model, so that
this interface does not import the model. `GameCorrespondence.gamePrim` and
`GameCorrespondence.gameEvent` map the model's declarations to these. Nothing here
changes the model. -/

structure PrimSpec where
  Token : Type
  Address : Type
  PubKey : Type
  SpendKey : Type
  Salt : Type
  Commitment : Type
  Nullifier : Type
  /-- `spending_pubkey = Poseidon1(spending_key)` (Section 5.1). -/
  derivePub : SpendKey → PubKey
  /-- `commitment = Poseidon4(token, amount, owner_pubkey, salt)` (Section 5.1). -/
  commit : Token → Nat → PubKey → Salt → Commitment
  /-- `nullifier = Poseidon2(commitment, spending_key)` (Section 5.1). -/
  nullify : Commitment → SpendKey → Nullifier

inductive Event (P : PrimSpec) where
  | deposit (commitment : P.Commitment)
  | transfer (nf1 nf2 : P.Nullifier) (out1 out2 : P.Commitment)
  | withdraw (nullifier : P.Nullifier)

/-! End of the repeated declarations. -/

variable {P : PrimSpec}

/-! ## The observer view as a VCVio oracle interface

The public observer sees the ordered `Event` log and nothing else. As a VCVio
`OracleSpec` that is a single oracle whose answer is the log. The challenger
implements it; the adversary may only read through it. -/

/-- Observer oracle interface: one oracle, answering every read with the public
event log. Keys, note witnesses and encrypted payloads are outside `Event`
(SPEC-MAP simplification 8), so they are outside this interface too. -/
@[reducible] def observerSpec (P : PrimSpec) : OracleSpec Unit := Unit →ₒ List (Event P)

/-- The challenger's handler: answer every observer read with the log of the
synthetic world it published. -/
def observerImpl (log : List (Event P)) : QueryImpl (observerSpec P) ProbComp :=
  fun _ => pure log

/-! ## Transfer witnesses

The data behind one transfer, as the two-world adversary supplies it. Output
salts are *not* adversary-chosen: the challenger samples them, which is what
makes the commitment-hiding reduction available. -/

/-- One transfer's secret data, minus the salts the challenger samples. Slots
keep public-input order (spec line 234). -/
structure TransferWitness (P : PrimSpec) where
  inCm1 : P.Commitment
  inCm2 : P.Commitment
  spendKey1 : P.SpendKey
  spendKey2 : P.SpendKey
  outToken1 : P.Token
  outAmt1 : Nat
  outPk1 : P.PubKey
  outToken2 : P.Token
  outAmt2 : Nat
  outPk2 : P.PubKey

/-- The event this transfer publishes, given the salts the challenger drew.
Uses the same event constructor and primitive formulas as `Tx.event`. This
does not establish that the witness belongs to a valid ledger execution. -/
def TransferWitness.toEvent (w : TransferWitness P) (s1 s2 : P.Salt) : Event P :=
  .transfer (P.nullify w.inCm1 w.spendKey1) (P.nullify w.inCm2 w.spendKey2)
    (P.commit w.outToken1 w.outAmt1 w.outPk1 s1)
    (P.commit w.outToken2 w.outAmt2 w.outPk2 s2)

/-- Publish a synthetic world with two independent salt draws per transfer.
New draws may collide. No ownership, balance, input existence, double-spend,
or inter-transfer consistency checks occur here. -/
def publish [SampleableType P.Salt] :
    List (TransferWitness P) → ProbComp (List (Event P))
  | [] => pure []
  | w :: ws => do
      let s1 ← $ᵗ P.Salt
      let s2 ← $ᵗ P.Salt
      let rest ← publish ws
      return w.toEvent s1 s2 :: rest

/-! ## The legal-challenge side condition

"Two histories differing only in recipient allocation": same inputs spent with
the same keys, same token and same amount in every output slot, differing only
in the recipient public keys. Equal tokens and amounts define the scope of
this recipient-only question. Amounts occur inside commitments; this game
has no balance check that would expose them. -/

/-- The two worlds differ in recipients only. -/
def RecipientOnly (w₀ w₁ : TransferWitness P) : Prop :=
  w₀.inCm1 = w₁.inCm1 ∧ w₀.inCm2 = w₁.inCm2 ∧
    w₀.spendKey1 = w₁.spendKey1 ∧ w₀.spendKey2 = w₁.spendKey2 ∧
    w₀.outToken1 = w₁.outToken1 ∧ w₀.outAmt1 = w₁.outAmt1 ∧
    w₀.outToken2 = w₁.outToken2 ∧ w₀.outAmt2 = w₁.outAmt2

/-- Lifted to whole histories: pointwise, which already forces equal length. -/
def LegalChallenge (ws₀ ws₁ : List (TransferWitness P)) : Prop :=
  List.Forall₂ RecipientOnly ws₀ ws₁

/-- A legal challenge pair has equal length, so the hybrid chain is well formed. -/
theorem lengths_match_of_legalChallenge {ws₀ ws₁ : List (TransferWitness P)}
    (h : LegalChallenge ws₀ ws₁) : ws₀.length = ws₁.length :=
  List.Forall₂.length_eq h

/-! ## The two-world game

Shaped on VCVio's own `CommitmentScheme.hidingExp`: the adversary picks the two
worlds, the challenger flips a coin and runs one, the adversary reads the log
through `observerSpec` and guesses. -/

/-- A two-phase transfer-indistinguishability adversary. Phase one chooses the
two histories; phase two reads the published log and guesses the coin. -/
structure TransferIndAdv (P : PrimSpec) where
  State : Type
  chooseWorlds : ProbComp (List (TransferWitness P) × List (TransferWitness P) × State)
  distinguish : State → OracleComp (observerSpec P) Bool

/-- Run one challenge. Illegal pairs produce an independent fair win bit,
without publishing a log or invoking the distinguisher. Classical legality
is used because `PrimSpec` does not require decidable equality. -/
noncomputable def transferChallengeExp [SampleableType P.Salt]
    (adv : TransferIndAdv P) (ws₀ ws₁ : List (TransferWitness P))
    (st : adv.State) : ProbComp Bool := by
  classical
  exact if LegalChallenge ws₀ ws₁ then do
    let b ← $ᵗ Bool
    let log ← publish (if b then ws₁ else ws₀)
    let b' ← simulateQ (observerImpl log) (adv.distinguish st)
    return (b == b')
  else $ᵗ Bool

/-- The recipient-only experiment, with legality enforced for each sampled pair. -/
noncomputable def transferIndExp [SampleableType P.Salt]
    (adv : TransferIndAdv P) : ProbComp Bool := do
  let (ws₀, ws₁, st) ← adv.chooseWorlds
  transferChallengeExp adv ws₀ ws₁ st

theorem transferChallengeExp_of_legal [SampleableType P.Salt]
    (adv : TransferIndAdv P) (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (h : LegalChallenge ws₀ ws₁) :
    transferChallengeExp adv ws₀ ws₁ st = (do
      let b ← $ᵗ Bool
      let log ← publish (if b then ws₁ else ws₀)
      let b' ← simulateQ (observerImpl log) (adv.distinguish st)
      return (b == b')) := by
  simp [transferChallengeExp, h]

theorem transferChallengeExp_of_illegal [SampleableType P.Salt]
    (adv : TransferIndAdv P) (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (h : ¬ LegalChallenge ws₀ ws₁) :
    transferChallengeExp adv ws₀ ws₁ st = ($ᵗ Bool) := by
  simp [transferChallengeExp, h]

/-- Advantage: deviation of the guess from a coin flip. Mirrors
`CommitmentScheme.hidingAdvantage`. -/
noncomputable def transferIndAdvantage [SampleableType P.Salt]
    (adv : TransferIndAdv P) : ℝ :=
  |(Pr[= true | transferIndExp adv]).toReal - 1 / 2|

theorem transferIndAdvantage_nonneg [SampleableType P.Salt] (adv : TransferIndAdv P) :
    0 ≤ transferIndAdvantage adv := abs_nonneg _

/-- A fixed illegal challenge gives zero advantage for every second phase. -/
theorem transferIndAdvantage_of_illegal_pure [SampleableType P.Salt]
    (adv : TransferIndAdv P) (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (hchoose : adv.chooseWorlds = pure (ws₀, ws₁, st))
    (hillegal : ¬ LegalChallenge ws₀ ws₁) : transferIndAdvantage adv = 0 := by
  simp [transferIndAdvantage, transferIndExp, hchoose,
    transferChallengeExp_of_illegal adv ws₀ ws₁ st hillegal]

/-- Unequal lengths cannot give an advantage, regardless of the distinguisher. -/
theorem transferIndAdvantage_of_length_ne [SampleableType P.Salt]
    (adv : TransferIndAdv P) (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (hchoose : adv.chooseWorlds = pure (ws₀, ws₁, st))
    (hlen : ws₀.length ≠ ws₁.length) : transferIndAdvantage adv = 0 := by
  exact transferIndAdvantage_of_illegal_pure adv ws₀ ws₁ st hchoose
    (fun h => hlen (lengths_match_of_legalChallenge h))

/-- Regression case from the review: empty versus singleton logs. -/
theorem transferIndAdvantage_nil_singleton [SampleableType P.Salt]
    (adv : TransferIndAdv P) (w : TransferWitness P) (st : adv.State)
    (hchoose : adv.chooseWorlds = pure ([], [w], st)) :
    transferIndAdvantage adv = 0 := by
  exact transferIndAdvantage_of_length_ne adv [] [w] st hchoose (by simp)

/-! ## The named assumptions

The reduction targets from the proposal, each pinned to a VCVio structure so
the hardness hypothesis is a VCVio object rather than a fresh axiom. -/

/-- The primitive assumptions the pool's privacy claim rests on, named against
VCVio's own scheme structures. The bounds quantify over all adversaries.
They have information-theoretic strength, with no security parameter or
computation bound. Their satisfiability for Poseidon is not established.
The PRF fields are unused for this recipient-only game.

Zero-knowledge of the spend proofs is deliberately absent: `Event` carries no
proof field, so the observer interface never exposes one. The boundary
excludes proof leakage; it does not prove deployed proof security. Observed
proofs or proof-dependent acceptance would require further modeling. -/
structure PoolAssumptions (P : PrimSpec) [SampleableType P.Salt]
    [DecidableEq P.Commitment] [SampleableType P.Nullifier] where
  /-- Poseidon4 read as a commitment scheme: commit to `(token, amount, pubkey)`
  under a uniform salt, opening with that salt. -/
  cs : CommitmentScheme Unit (P.Token × Nat × P.PubKey) P.Commitment P.Salt
  /-- The scheme's commit algorithm is exactly the pool's `P.commit` under a
  uniform salt. This is the bridge clause; it says the VCVio object and the pool
  model agree, and nothing more. -/
  cs_commit : ∀ t a pk,
    cs.commit () (t, a, pk) = (do let s ← $ᵗ P.Salt; return (P.commit t a pk s, s))
  /-- Poseidon2 nullifier derivation read as a PRF keyed by the spending key. -/
  prf : PRFScheme P.SpendKey P.Commitment P.Nullifier
  /-- The PRF's evaluation is exactly the pool's `P.nullify`. -/
  prf_eval : ∀ k cm, prf.eval k cm = P.nullify cm k
  /-- Unrestricted hiding bound in success-bias units, `|Pr[win] - 1/2|`. -/
  εHiding : ℝ
  hiding_bound : ∀ A : CommitmentScheme.HidingAdv Unit (P.Token × Nat × P.PubKey) P.Commitment,
    cs.hidingAdvantage A ≤ εHiding
  /-- Unrestricted PRF bound in Boolean distinguishing-distance units. -/
  εPRF : ℝ
  prf_bound : ∀ A : PRFScheme.PRFAdversary P.Commitment P.Nullifier,
    prf.prfAdvantage A ≤ εPRF

/-! ## The hybrid skeleton

The proof campaign is a hybrid over transfers. The scaffolding below is proved
outright for fixed worlds and state. Per-step reductions, averaging over the
joint challenge/state distribution, normalization, and history-length bounds
remain open. No theorem below bounds `transferIndAdvantage`. -/

/-- The `i`-th hybrid world: the first `i` transfers come from world one, the
rest from world zero. -/
def hybridWorld (ws₀ ws₁ : List (TransferWitness P)) (i : ℕ) : List (TransferWitness P) :=
  ws₁.take i ++ ws₀.drop i

@[simp] theorem hybridWorld_zero (ws₀ ws₁ : List (TransferWitness P)) :
    hybridWorld ws₀ ws₁ 0 = ws₀ := by
  simp [hybridWorld]

theorem hybridWorld_length (ws₀ ws₁ : List (TransferWitness P))
    (h : ws₀.length = ws₁.length) :
    hybridWorld ws₀ ws₁ ws₀.length = ws₁ := by
  simp [hybridWorld, h]

/-- The game played against the `i`-th hybrid world, with the coin removed: the
challenger publishes hybrid `i` and the adversary guesses. Consecutive hybrids
are what each reduction step must separate. -/
def hybridExp [SampleableType P.Salt] (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State) (i : ℕ) : ProbComp Bool := do
  let log ← publish (hybridWorld ws₀ ws₁ i)
  simulateQ (observerImpl log) (adv.distinguish st)

/-- Telescoping for Boolean distinguishing advantage: the gap between the ends
of a chain of games is at most the sum of the consecutive gaps. This is the
hybrid argument itself; VCVio ships the `Unit`-valued analogue and the Boolean
triangle inequality, so only the induction is new here. -/
theorem boolDistAdvantage_le_sum_range {n : ℕ} (games : ℕ → ProbComp Bool) :
    (games 0).boolDistAdvantage (games n) ≤
      ∑ i ∈ Finset.range n, (games i).boolDistAdvantage (games (i + 1)) := by
  induction n with
  | zero => simp [ProbComp.boolDistAdvantage]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (ProbComp.boolDistAdvantage_triangle _ (games n) _).trans (by gcongr)

/-- The endpoints of the chain really are the two worlds the adversary chose. -/
theorem hybridExp_zero [SampleableType P.Salt] (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State) :
    hybridExp adv ws₀ ws₁ st 0 =
      (do let log ← publish ws₀; simulateQ (observerImpl log) (adv.distinguish st)) := by
  simp [hybridExp]

theorem hybridExp_last [SampleableType P.Salt] (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State) (h : ws₀.length = ws₁.length) :
    hybridExp adv ws₀ ws₁ st ws₀.length =
      (do let log ← publish ws₁; simulateQ (observerImpl log) (adv.distinguish st)) := by
  rw [hybridExp, hybridWorld_length ws₀ ws₁ h]

/-- **The hybrid bound.** For a legal challenge pair, the distance between the
two synthetic worlds is at most the sum of the consecutive hybrid steps.
Two commitment replacements should cost at most `4 * εHiding` per summand,
since hiding uses half the Boolean distinguishing distance. That reduction
is not proved here. Nullifiers agree under `RecipientOnly`; no PRF step is needed. -/
theorem hybrid_bound [SampleableType P.Salt] (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (h : LegalChallenge ws₀ ws₁) :
    ProbComp.boolDistAdvantage
        (do let log ← publish ws₀; simulateQ (observerImpl log) (adv.distinguish st))
        (do let log ← publish ws₁; simulateQ (observerImpl log) (adv.distinguish st)) ≤
      ∑ i ∈ Finset.range ws₀.length,
        (hybridExp adv ws₀ ws₁ st i).boolDistAdvantage
          (hybridExp adv ws₀ ws₁ st (i + 1)) := by
  rw [← hybridExp_zero adv ws₀ ws₁ st,
    ← hybridExp_last adv ws₀ ws₁ st (lengths_match_of_legalChallenge h)]
  exact boolDistAdvantage_le_sum_range _

end PoolGame
