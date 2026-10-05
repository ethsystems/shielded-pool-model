import AcirLean.Withdraw.WitnessData

namespace AcirLean.Withdraw

open AcirLean

/-- The witness solved by `nargo execute` (beta.21) for the committed Prover.toml. -/
noncomputable def solved : Assignment := witnessTrie.toAssignment witnessDepth

end AcirLean.Withdraw
