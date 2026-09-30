-- Positive control: the two L4 Tier B theorems instantiate on the concrete
-- toy PrimSpec. Must build.
import LeanShieldedPool.Proofs.TierB
import LeanShieldedPool.Proofs.EventReplay

open LeanShieldedPool

example : noTheft NonVacuity.Toy := noTheft_proof _
example : eventReplayFaithful NonVacuity.Toy := eventReplayFaithful_proof _
