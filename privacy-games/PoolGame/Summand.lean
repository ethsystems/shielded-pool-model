import PoolGame.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace PoolGame
namespace Summand

variable {P : PrimSpec} [SampleableType P.Salt]
  [DecidableEq P.Commitment] [SampleableType P.Nullifier]

/-- The reduction samples the shared prefix before receiving the challenge. -/
def hidingReduction {α : Type} (pref : ProbComp α)
    (m₀ m₁ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → ProbComp Bool) :
    CommitmentScheme.HidingAdv Unit (P.Token × Nat × P.PubKey) P.Commitment where
  State := α
  chooseMessages := fun _ => do
    let a ← pref
    return (m₀, m₁, a)
  distinguish := observe

/-- A branch samples one fresh commitment salt after the shared prefix. -/
def commitBranch {α : Type} (pref : ProbComp α)
    (m : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → ProbComp Bool) : ProbComp Bool := do
  let a ← pref
  let s ← $ᵗ P.Salt
  observe a (P.commit m.1 m.2.1 m.2.2 s)

theorem commitment_distance_eq {α : Type} (A : PoolAssumptions P)
    (pref : ProbComp α) (m₀ m₁ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → ProbComp Bool) :
    (commitBranch pref m₀ observe).boolDistAdvantage (commitBranch pref m₁ observe) =
      2 * A.cs.hidingAdvantage (hidingReduction pref m₀ m₁ observe) := by
  let game : ProbComp Bool := do
    let a ← pref
    let b ← $ᵗ Bool
    let z ← if b then
      (do let s ← $ᵗ P.Salt; observe a (P.commit m₀.1 m₀.2.1 m₀.2.2 s))
      else (do let s ← $ᵗ P.Salt; observe a (P.commit m₁.1 m₁.2.1 m₁.2.2 s))
    return (b == z)
  have hexp : ∀ z, Pr[= z | A.cs.hidingExp (hidingReduction pref m₀ m₁ observe)] =
      Pr[= z | game] := by
    intro z
    simp only [CommitmentScheme.hidingExp, hidingReduction, bind_assoc, pure_bind]
    have h : ∀ pp : Unit,
        (do
          let a ← pref
          let b ← $ᵗ Bool
          let cd ← A.cs.commit pp (if b then m₀ else m₁)
          let guess ← observe a cd.1
          pure (b == guess)) = game := by
      intro pp
      cases pp
      congr 1
      funext a
      congr 1
      funext b
      cases b <;> simp [A.cs_commit]
    simp only [h]
    simp
  unfold commitBranch
  rw [← ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage]
  change game.boolBiasAdvantage = _
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half]
  unfold CommitmentScheme.hidingAdvantage
  rw [hexp true]

theorem commitment_distance_le {α : Type} (A : PoolAssumptions P)
    (pref : ProbComp α) (m₀ m₁ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → ProbComp Bool) :
    (commitBranch pref m₀ observe).boolDistAdvantage (commitBranch pref m₁ observe) ≤
      2 * A.εHiding := by
  rw [commitment_distance_eq A]
  exact mul_le_mul_of_nonneg_left (A.hiding_bound _) (by norm_num)

/-- Two fresh commitments followed by an arbitrary observation. -/
def twoCommitExp {α : Type} (pref : ProbComp α)
    (m₁ m₂ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) : ProbComp Bool := do
  let a ← pref
  let s₁ ← $ᵗ P.Salt
  let s₂ ← $ᵗ P.Salt
  observe a (P.commit m₁.1 m₁.2.1 m₁.2.2 s₁) (P.commit m₂.1 m₂.2.1 m₂.2.2 s₂)

/-- The first output is the challenge; the second uses an independent salt. -/
def firstOutputReduction {α : Type} (pref : ProbComp α)
    (m₀ m₁ other : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) :=
  hidingReduction pref m₀ m₁ (fun a c₁ => do
    let s₂ ← $ᵗ P.Salt
    observe a c₁ (P.commit other.1 other.2.1 other.2.2 s₂))

/-- The second output is the challenge; the first salt is sampled in phase one. -/
def secondOutputReduction {α : Type} (pref : ProbComp α)
    (other m₀ m₁ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) :=
  hidingReduction (do let a ← pref; let s₁ ← $ᵗ P.Salt; pure (a, s₁)) m₀ m₁
    (fun (a, s₁) c₂ => observe a (P.commit other.1 other.2.1 other.2.2 s₁) c₂)

theorem first_output_distance_eq {α : Type} (A : PoolAssumptions P)
    (pref : ProbComp α) (m₀ m₁ other : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) :
    (twoCommitExp pref m₀ other observe).boolDistAdvantage
      (twoCommitExp pref m₁ other observe) =
      2 * A.cs.hidingAdvantage (firstOutputReduction pref m₀ m₁ other observe) := by
  simpa only [twoCommitExp, commitBranch, firstOutputReduction] using
    (commitment_distance_eq A pref m₀ m₁ (fun a c₁ => do
      let s₂ ← $ᵗ P.Salt
      observe a c₁ (P.commit other.1 other.2.1 other.2.2 s₂)))

theorem second_output_distance_eq {α : Type} (A : PoolAssumptions P)
    (pref : ProbComp α) (other m₀ m₁ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) :
    (twoCommitExp pref other m₀ observe).boolDistAdvantage
      (twoCommitExp pref other m₁ observe) =
      2 * A.cs.hidingAdvantage (secondOutputReduction pref other m₀ m₁ observe) := by
  simpa [twoCommitExp, commitBranch, secondOutputReduction, bind_assoc] using
    (commitment_distance_eq A
      (do let a ← pref; let s₁ ← $ᵗ P.Salt; pure (a, s₁)) m₀ m₁
      (fun (a, s₁) c₂ => observe a (P.commit other.1 other.2.1 other.2.2 s₁) c₂))

theorem first_output_distance_le {α : Type} (A : PoolAssumptions P)
    (pref : ProbComp α) (m₀ m₁ other : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) :
    (twoCommitExp pref m₀ other observe).boolDistAdvantage
      (twoCommitExp pref m₁ other observe) ≤ 2 * A.εHiding := by
  rw [first_output_distance_eq A]
  exact mul_le_mul_of_nonneg_left (A.hiding_bound _) (by norm_num)

theorem second_output_distance_le {α : Type} (A : PoolAssumptions P)
    (pref : ProbComp α) (other m₀ m₁ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) :
    (twoCommitExp pref other m₀ observe).boolDistAdvantage
      (twoCommitExp pref other m₁ observe) ≤ 2 * A.εHiding := by
  rw [second_output_distance_eq A]
  exact mul_le_mul_of_nonneg_left (A.hiding_bound _) (by norm_num)

theorem two_output_distance_le {α : Type} (A : PoolAssumptions P)
    (pref : ProbComp α) (m₁₀ m₁₁ m₂₀ m₂₁ : P.Token × Nat × P.PubKey)
    (observe : α → P.Commitment → P.Commitment → ProbComp Bool) :
    (twoCommitExp pref m₁₀ m₂₀ observe).boolDistAdvantage
      (twoCommitExp pref m₁₁ m₂₁ observe) ≤ 4 * A.εHiding := by
  have ht := ProbComp.boolDistAdvantage_triangle
    (twoCommitExp pref m₁₀ m₂₀ observe) (twoCommitExp pref m₁₁ m₂₀ observe)
    (twoCommitExp pref m₁₁ m₂₁ observe)
  have h₁ := first_output_distance_le A pref m₁₀ m₁₁ m₂₀ observe
  have h₂ := second_output_distance_le A pref m₁₁ m₂₀ m₂₁ observe
  linarith

omit [DecidableEq P.Commitment] [SampleableType P.Nullifier] in
/-- Split publication at a fixed prefix without changing sampling order. -/
theorem publish_append (pre post : List (TransferWitness P)) :
    publish (pre ++ post) = (do
      let l ← publish pre
      let r ← publish post
      pure (l ++ r)) := by
  induction pre with
  | nil => simp [publish]
  | cons w pre ih => simp [publish, ih, bind_assoc]

/-- Observe the full log with the two challenge slots inserted in order. -/
def observeTransfer (adv : TransferIndAdv P) (st : adv.State)
    (post : List (TransferWitness P)) (nf₁ nf₂ : P.Nullifier)
    (prefixLog : List (Event P)) (c₁ c₂ : P.Commitment) : ProbComp Bool := do
  let suffixLog ← publish post
  simulateQ (observerImpl (prefixLog ++ .transfer nf₁ nf₂ c₁ c₂ :: suffixLog))
    (adv.distinguish st)

def outputMessage₁ (w : TransferWitness P) : P.Token × Nat × P.PubKey :=
  (w.outToken1, w.outAmt1, w.outPk1)

def outputMessage₂ (w : TransferWitness P) : P.Token × Nat × P.PubKey :=
  (w.outToken2, w.outAmt2, w.outPk2)

omit [DecidableEq P.Commitment] [SampleableType P.Nullifier] in
/-- An exact factorization of the frozen publisher around one transfer. -/
theorem publish_transfer (adv : TransferIndAdv P) (st : adv.State)
    (pre post : List (TransferWitness P)) (w : TransferWitness P) :
    (do let log ← publish (pre ++ w :: post)
        simulateQ (observerImpl log) (adv.distinguish st)) =
      twoCommitExp (publish pre) (outputMessage₁ w) (outputMessage₂ w)
        (observeTransfer adv st post
          (P.nullify w.inCm1 w.spendKey1) (P.nullify w.inCm2 w.spendKey2)) := by
  simp [publish_append, publish, twoCommitExp, outputMessage₁, outputMessage₂,
    observeTransfer, TransferWitness.toEvent, bind_assoc]

/-- Replace both output recipients in one transfer of a fixed history. -/
theorem transfer_distance_le (A : PoolAssumptions P)
    (adv : TransferIndAdv P) (st : adv.State)
    (pre post : List (TransferWitness P)) (w₀ w₁ : TransferWitness P)
    (h : RecipientOnly w₀ w₁) :
    ProbComp.boolDistAdvantage
      (do let log ← publish (pre ++ w₀ :: post)
          simulateQ (observerImpl log) (adv.distinguish st))
      (do let log ← publish (pre ++ w₁ :: post)
          simulateQ (observerImpl log) (adv.distinguish st)) ≤ 4 * A.εHiding := by
  rw [publish_transfer, publish_transfer]
  rcases h with ⟨hc₁, hc₂, hk₁, hk₂, _⟩
  rw [hc₁, hc₂, hk₁, hk₂]
  exact two_output_distance_le A _ _ _ _ _ _

/-- One consecutive hybrid step, with legality required only at the changed slot. -/
theorem hybrid_step_distance_le (A : PoolAssumptions P)
    (adv : TransferIndAdv P) (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (i : Nat) (h₀ : i < ws₀.length) (h₁ : i < ws₁.length)
    (h : RecipientOnly ws₀[i] ws₁[i]) :
    (hybridExp adv ws₀ ws₁ st i).boolDistAdvantage
      (hybridExp adv ws₀ ws₁ st (i + 1)) ≤ 4 * A.εHiding := by
  unfold hybridExp hybridWorld
  rw [List.drop_eq_getElem_cons h₀, List.take_succ_eq_append_getElem h₁]
  simpa only [List.append_assoc, List.singleton_append] using
    (transfer_distance_le A adv st (ws₁.take i) (ws₀.drop (i + 1)) ws₀[i] ws₁[i] h)

/-- Every in-range summand of a fixed legal challenge has the stated bound. -/
theorem legal_hybrid_step_distance_le (A : PoolAssumptions P)
    (adv : TransferIndAdv P) (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (h : LegalChallenge ws₀ ws₁) (i : Nat) (hi : i < ws₀.length) :
    (hybridExp adv ws₀ ws₁ st i).boolDistAdvantage
      (hybridExp adv ws₀ ws₁ st (i + 1)) ≤ 4 * A.εHiding := by
  have hi₁ : i < ws₁.length := by rw [← lengths_match_of_legalChallenge h]; exact hi
  exact hybrid_step_distance_le A adv ws₀ ws₁ st i hi hi₁ (List.Forall₂.get h hi hi₁)

#print axioms commitment_distance_eq
#print axioms commitment_distance_le
#print axioms first_output_distance_eq
#print axioms second_output_distance_eq
#print axioms first_output_distance_le
#print axioms second_output_distance_le
#print axioms two_output_distance_le
#print axioms publish_append
#print axioms publish_transfer
#print axioms transfer_distance_le
#print axioms hybrid_step_distance_le
#print axioms legal_hybrid_step_distance_le

end Summand
end PoolGame
