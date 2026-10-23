import Transfer.Execution

namespace Controls.Transfer
open Lampe Determinism Transfer.HashGood Transfer.Forward Transfer.Rules Transfer.Execution



theorem transfer_nonvacuous_ballast_bound (st : State p) :
    N0 = Poseidon.Hash2.hash2v C0 0 ∧ N1 = Poseidon.Hash2.hash2v C1 0 ∧ (0 : U 32) ≤ 32 ∧ ((33 : U 32) ≤ 32) := by
  have h := accepting_main_transfer_rules N0 N1 D0 D0 C0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 33
    (List.Vector.replicate 32 0) (List.Vector.replicate 32 0)
    (List.Vector.replicate 32 false) (List.Vector.replicate 32 false)
    (main_accepting_execution st) (by rintro ⟨_, h⟩; cases h)
  exact ⟨h.2.2.1, h.2.2.2.1, h.1.1, by decide⟩

#print axioms transfer_nonvacuous_ballast_bound
end Controls.Transfer
