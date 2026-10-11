-- Refutation control for the last-owner equation of `hasAnonymitySet`. This
-- file MUST BUILD. The mutation deletes exactly one conjunct, the equation
-- `lastTransferFirstOwner (es i).1 = some (owners i)`; the explanations, the
-- supported-token predicate, and both injectivity premises all remain. On
-- the constant-commitment toy, a transfer-free single-deposit log then
-- reaches count 1, while `constant_commit_blocks_transfer` rules out every
-- transfer guard. So the frozen `hasAnonymitySet.accepted_transfer`
-- universal, restated over the mutated definition, is FALSE: the equation
-- is what makes k count recipients of an actual transfer rather than bare
-- explanations.
import LeanShieldedPool.Extensions.KAnonymity

namespace LeanShieldedPool
namespace RefuteKAnonymityTransfer

open KAnonymity

/-- The frozen constant-commitment toy: no transfer guard can ever fire. -/
abbrev K : PrimSpec := ConstantCommitToy.Toy

-- MUTATION: only the last conjunct is REMOVED; both injectivity premises
-- stay. `owners` stays, but it is unconstrained: with the last-owner
-- equation removed nothing connects it to the explanations, so its
-- injectivity premise has no content.
def hasAnonymitySetNoOwnerEq (sup : K.Token → Prop) (log : List (Event K))
    (k : Nat) : Prop :=
  ∃ (es : Fin k → List (Tx K) × St K) (owners : Fin k → K.PubKey),
    (∀ i, es i ∈ explanations sup log) ∧
    Function.Injective es ∧ Function.Injective owners

/-- One 5-unit deposit; its commitment is the constant 0. -/
abbrev note : Note K := ⟨(), 5, 0, 0⟩
abbrev dep : DepositData K := ⟨note, ()⟩
abbrev hist : List (Tx K) := [.deposit dep]

theorem deposit_guard : dep.guard (St.empty K ConstantCommitToy.sup) := by
  refine ⟨trivial, by norm_num, ?_, ?_⟩
  · show U128 5
    unfold U128 maxU128; norm_num
  · norm_num [St.empty, St.leaves]

theorem accepted :
    Run ConstantCommitToy.sup hist (dep.post (St.empty K ConstantCommitToy.sup)) :=
  Run.step Run.empty (Step.deposit deposit_guard)

/-- One note, no spending key: collision freedom holds in this history. -/
theorem crypto : CryptoHyp K hist := by
  constructor
  · intro n hn n' hn' _ _ _
    simp only [hist, runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn hn'
    subst hn; subst hn'; rfl
  · intro k _ k' _ h
    exact h

/-- The transfer-free log reaches count 1 under the mutated definition. Every
remaining premise is discharged: an accepted run, its `CryptoHyp`, the
reflexive observation relation, and both injectivity obligations. -/
theorem mutated_one :
    hasAnonymitySetNoOwnerEq ConstantCommitToy.sup (events hist) 1 := by
  refine ⟨fun _ => (hist, dep.post (St.empty K ConstantCommitToy.sup)),
    fun _ => 0, ?_, ?_, ?_⟩
  · intro i
    exact ⟨accepted, crypto, ObsEquiv.refl _⟩
  · intro i j _
    exact Subsingleton.elim i j
  · intro i j _
    exact Subsingleton.elim i j

/-- `hasAnonymitySet.accepted_transfer`, restated over the mutated
definition with its quantifiers intact, is FALSE: the constant commitment
blocks every transfer guard. The control passes only if this refutation
builds. -/
theorem transfer_counterexample :
    ¬ ∀ (sup : K.Token → Prop) (log : List (Event K)) (k : Nat),
      hasAnonymitySetNoOwnerEq sup log k → 0 < k →
      ∃ (d : TransferData K) (st : St K), d.guard st := by
  intro h
  obtain ⟨d, st, hg⟩ :=
    h ConstantCommitToy.sup (events hist) 1 mutated_one Nat.one_pos
  exact constant_commit_blocks_transfer (P := K) 0 (fun _ _ _ _ => rfl) d st hg

end RefuteKAnonymityTransfer
end LeanShieldedPool
