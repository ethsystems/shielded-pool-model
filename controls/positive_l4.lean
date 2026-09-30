-- Positive control: the four L4 Tier A theorems instantiate on the
-- concrete toy PrimSpec. Must build.
import LeanShieldedPool.Proofs.TierA
import LeanShieldedPool.Proofs.TierAConditional
import LeanShieldedPool.Draft.NonVacuity

open LeanShieldedPool

example : poolSolvency NonVacuity.Toy := poolSolvency_proof _
example : noOverWithdrawal NonVacuity.Toy := noOverWithdrawal_proof _
example : noMinting NonVacuity.Toy := noMinting_proof _
example : balanceIsLiveValue NonVacuity.Toy := balanceIsLiveValue_proof _
