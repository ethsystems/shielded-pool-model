import AcirLean.Transfer.WitnessData

namespace AcirLean.Transfer

open AcirLean

/-- The witness solved by `nargo execute` (beta.21) for the committed Prover.toml. -/
noncomputable def solved : Assignment := witnessTrie.toAssignment witnessDepth

end AcirLean.Transfer
