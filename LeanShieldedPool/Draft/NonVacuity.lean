import LeanShieldedPool.Statements.L3

/-!
# Non-vacuity witnesses (DRAFT)

The statements of `StatementsL3.lean` are worthless if no `Step` can fire:
over-strong guards would make every claim vacuously true. This file pins a
toy `PrimSpec` and shows that each of the three operation guards is
satisfiable, so `Reachable` and `Run` have content.

The toy primitives are NOT a cryptographic claim: `commit` is addition and
`nullify` is the identity. They exist only to witness satisfiability.

No `sorry`, no `axiom`.
-/

namespace LeanShieldedPool
namespace NonVacuity

/-- A toy instantiation of the opaque primitives (Section 5.1). -/
abbrev Toy : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Unit
  SpendKey := Unit
  Salt := Nat
  Commitment := Nat
  Nullifier := Nat
  derivePub := fun _ => ()
  commit := fun _ a _ s => a + s
  nullify := fun c _ => c

/-- A 5-unit note; its commitment is 5. -/
abbrev n0 : Note Toy := ⟨(), 5, (), 0⟩
abbrev d0 : DepositData Toy := ⟨n0, ()⟩
abbrev st0 : St Toy := St.empty Toy (fun _ => True)

/-- The deposit guard fires on the empty pool (Section 4.1). -/
example : d0.guard st0 := by
  refine ⟨trivial, by norm_num, ?_, ?_⟩
  · show U128 5
    unfold U128 maxU128
    norm_num
  · show _ ∉ (st0.minted.map Note.cm)
    norm_num [St.empty]

/-- A 2-in-2-out transfer: one real input, one ballast input, 5 = 3 + 2. -/
abbrev t0 : TransferData Toy :=
  { key := ()
    in1 := n0
    in2 := ⟨(), 0, (), 1⟩
    out1 := ⟨(), 3, (), 7⟩
    out2 := ⟨(), 2, (), 9⟩
    snapshot := 1 }

/-- The transfer guard fires after one deposit (Section 4.2). -/
example : t0.guard (d0.post st0) := by
  norm_num [TransferData.guard, TransferData.nf1, TransferData.nf2, Note.nf, Note.cm,
    Note.ownedBy, Note.isBallast, St.rootInWindow, St.inTreeAt, St.fresh, St.leaves,
    St.empty, St.pushWindow, rootWindow, DepositData.post, U128, maxU128]

abbrev w0 : WithdrawData Toy := ⟨(), n0, (), 1⟩

/-- The withdraw guard fires after one deposit (Section 4.3). -/
example : w0.guard (d0.post st0) := by
  refine ⟨?_, ?_, rfl, ?_, by norm_num, ?_, ?_⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∈ List.take 1 _
    norm_num [DepositData.post, St.empty, St.leaves, Note.cm]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty]
  · show U128 5
    unfold U128 maxU128; norm_num
  · show (5:Nat) ≤ _
    norm_num [DepositData.post, St.empty, bump]

end NonVacuity

-- Trust surface of the two L3 statements, for the gate to read.
#print axioms valueConservation
#print axioms noDoubleSpend

end LeanShieldedPool
