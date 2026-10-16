import AcirLean.Deposit.WitnessData

namespace AcirLean.Deposit

open AcirLean

/-- The witness solved by `nargo execute` (beta.21) for the committed Prover.toml. -/
noncomputable def solved : Assignment := witnessTrie.toAssignment witnessDepth

end AcirLean.Deposit
