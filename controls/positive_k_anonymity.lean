-- Positive control for the symbolic k-anonymity extension. This file MUST
-- BUILD. It applies the frozen names outside their home file, so the gate
-- catches a statement that drifts into something these instances no longer
-- satisfy. Everything here is a symbolic observer example, not
-- cryptographic evidence.
import LeanShieldedPool.Extensions.KAnonymity

namespace LeanShieldedPool
namespace PositiveKAnonymity

open KAnonymity

-- The two-recipient family applies at k = 2, and monotonicity gives k = 1.
example : acceptedAnonymityCandidate TwoRecipientToy.Toy TwoRecipientToy.sup 2 :=
  TwoRecipientToy.candidate_two

example : acceptedAnonymityCandidate TwoRecipientToy.Toy TwoRecipientToy.sup 1 :=
  TwoRecipientToy.candidate_two.mono (by norm_num)

-- Arbitrarily large finite counts: a concrete 7-member family.
example : acceptedAnonymityCandidate (ManyRecipientToy.Toy' 7)
    ManyRecipientToy.sup 7 :=
  ManyRecipientToy.candidate (by norm_num)

-- The hiding bridge applies to a nonconstant observer predicate: equality
-- of event-shape lists. `ObsEquiv.shapes` discharges the named hypothesis.
example (i j : Fin 2) :
    (events (TwoRecipientToy.history i)).map eventShape =
      (events (TwoRecipientToy.history j)).map eventShape :=
  TwoRecipientToy.indistinguishable_under_hiding
    (fun log₁ log₂ => log₁.map eventShape = log₂.map eventShape)
    (fun _ _ h => h.shapes) i j

-- The same predicate separates logs the relation must separate: a deposit
-- log and a withdraw log differ in shape, hence are not equivalent.
example (c : TwoRecipientToy.Toy.Commitment)
    (n : TwoRecipientToy.Toy.Nullifier) :
    ¬ ObsEquiv [Event.deposit c] [Event.withdraw n] :=
  deposit_not_obsEquiv_withdraw c n

-- The cardinality-only implication stays refuted at every positive count.
example (k : Nat) (hk : 0 < k) :
    ¬ cardinalityOnlyCandidate ConstantCommitToy.Toy ConstantCommitToy.sup k :=
  ConstantCommitToy.not_cardinalityOnlyCandidate k hk

-- The vacuous base case stays available for every log.
example (log : List (Event TwoRecipientToy.Toy)) :
    hasAnonymitySet TwoRecipientToy.sup log 0 :=
  hasAnonymitySet_zero TwoRecipientToy.sup log

end PositiveKAnonymity
end LeanShieldedPool
