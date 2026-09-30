-- Positive control: the three L3 theorems instantiate on the concrete toy
-- PrimSpec. Must build.
import LeanShieldedPool.Proofs.NoDoubleSpend
import LeanShieldedPool.Proofs.Conservation
import LeanShieldedPool.Draft.NonVacuity

open LeanShieldedPool

example : noDoubleSpend NonVacuity.Toy := noDoubleSpend_proof _
example : valueConservation NonVacuity.Toy := valueConservation_proof _
example : nullifierUniqueness NonVacuity.Toy := nullifierUniqueness_proof _
