-- EXPECT: unsolved goals
-- Negative control for `noMinting_proof`.
-- The transfer guard with the FIRST-INPUT membership conjunct REMOVED
-- accepts a transfer that spends a 7-unit note never deposited, minting
-- its value into two live outputs. Live value (5 + 4 + 3 = 12) then
-- exceeds total deposits (5). The proof attempt below must not close.
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool
namespace NegL4NoMinting

open NonVacuity

-- GUARD REMOVED: no `st.inTreeAt d.snapshot d.in1.cm`.
def guardNoMembership (d : TransferData Toy) (st : St Toy) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.in1.ownedBy d.key ∧
  d.in2.ownedBy d.key ∧
  (d.in2.isBallast ∨ st.inTreeAt d.snapshot d.in2.cm) ∧
  st.fresh d.nf1 ∧
  st.fresh d.nf2 ∧
  d.nf1 ≠ d.nf2 ∧
  d.in2.token = d.in1.token ∧
  d.out1.token = d.in1.token ∧
  d.out2.token = d.in1.token ∧
  U128 d.in1.amount ∧
  U128 d.in2.amount ∧
  U128 d.out1.amount ∧
  U128 d.out2.amount ∧
  d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount ∧
  d.out1.cm ∉ st.leaves ∧
  d.out2.cm ∉ st.leaves ∧
  d.out1.cm ≠ d.out2.cm

/-- A transfer spending a 7-unit note never deposited (commitment 16),
with a ballast second input, into 4 + 3 outputs. -/
abbrev tMint : TransferData Toy :=
  { key := ()
    in1 := ⟨(), 7, (), 9⟩
    in2 := ⟨(), 0, (), 1⟩
    out1 := ⟨(), 4, (), 11⟩
    out2 := ⟨(), 3, (), 20⟩
    snapshot := 1 }

/-- After one 5-unit deposit, the weakened guard accepts the minting
transfer. This part must elaborate. -/
example : guardNoMembership tMint (d0.post st0) := by
  refine ⟨?_, rfl, rfl, Or.inl rfl, ?_, ?_, by norm_num [TransferData.nf1,
      TransferData.nf2, Note.nf, Note.cm], rfl, rfl, rfl, ?_, ?_, ?_, ?_,
      by norm_num, ?_, ?_, by norm_num [Note.cm]⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show U128 7
    unfold U128 maxU128; norm_num
  · show U128 0
    unfold U128 maxU128; norm_num
  · show U128 4
    unfold U128 maxU128; norm_num
  · show U128 3
    unfold U128 maxU128; norm_num
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.leaves, Note.cm]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.leaves, Note.cm]

/-- Live value after the minting transfer. FALSE: it reads 12 ≤ 5.
The control passes only if this proof fails. -/
example :
    liveValue (tMint.post (d0.post st0)) () ≤ (tMint.post (d0.post st0)).deposited () := by
  norm_num [TransferData.post, DepositData.post, St.empty, St.spent, Note.cm,
    liveValue, noteValue, bump]

end NegL4NoMinting
end LeanShieldedPool
