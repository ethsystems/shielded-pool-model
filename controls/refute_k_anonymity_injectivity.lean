-- Refutation control for the observation relation's injectivity. This file
-- MUST BUILD. The mutation replaces the commitment embedding in `ObsEquiv`
-- with a plain function; the nullifier embedding, `renameEvent`, event order
-- and slots are untouched, so exactly one thing changes. A constant
-- commitment renaming then collapses two distinct deposits onto a repeated deposit, so
-- the frozen `distinct_deposits_not_obsEquiv` universal, restated over the
-- mutated relation, is FALSE. What is lost is exactly the reflection of
-- inequality: the weakened relation still preserves constructors, slots and
-- repeated atoms, but no longer keeps distinct atoms distinct.
import LeanShieldedPool.Extensions.KAnonymity

namespace LeanShieldedPool
namespace RefuteKAnonymityInjectivity

open KAnonymity

/-- The frozen two-recipient toy: `Commitment = Nat`, enough atoms to differ. -/
abbrev K : PrimSpec := TwoRecipientToy.Toy

-- MUTATION: a plain function instead of the `↪` embedding, for `cm` only.
def ObsEquivNoInj (log₁ log₂ : List (Event K)) : Prop :=
  ∃ (cm : K.Commitment → K.Commitment) (nf : K.Nullifier ↪ K.Nullifier),
    log₁.map (renameEvent cm nf) = log₂

/-- `distinct_deposits_not_obsEquiv`, restated over the mutated relation, is
FALSE: the constant commitment renaming is a legal witness once injectivity
is dropped. The control passes only if this refutation builds. -/
theorem injectivity_counterexample :
    ¬ ∀ (a b c : K.Commitment), a ≠ b →
      ¬ ObsEquivNoInj [Event.deposit a, Event.deposit b]
        [Event.deposit c, Event.deposit c] := by
  intro h
  exact h 0 1 0 Nat.zero_ne_one ⟨fun _ => 0, Function.Embedding.refl _, rfl⟩

end RefuteKAnonymityInjectivity
end LeanShieldedPool
