-- EXPECT: unsolved goals
-- Negative control for `spendRequiresOwnerKey_proof`.
-- On a PrimSpec with nontrivial ownership (PubKey = Bool), the withdraw
-- guard with the ownedBy conjunct REMOVED accepts a spend of a note owned
-- by pubkey `true` using witness key `false`. The spendRequiresOwnerKey conclusion for
-- that operation is then FALSE. The proof attempt below must not close.
import LeanShieldedPool.Proofs.TierB

namespace LeanShieldedPool
namespace NegL4BOwnerKey

/-- Toy primitives with real ownership: two pubkeys, derivePub = id. -/
abbrev K : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool
  Salt := Nat
  Commitment := Nat
  Nullifier := Nat × Bool
  derivePub := id
  commit := fun _ a _ s => a + s
  nullify := fun c k => (c, k)

/-- A 5-unit note owned by pubkey `true` (commitment 5). -/
abbrev nOwned : Note K := ⟨(), 5, true, 0⟩
abbrev dOwned : DepositData K := ⟨nOwned, ()⟩
abbrev stK : St K := St.empty K (fun _ => True)

-- GUARD REMOVED: no `d.note.ownedBy d.key`.
def guardNoOwner (d : WithdrawData K) (st : St K) : Prop :=
  st.rootInWindow d.snapshot ∧
  st.inTreeAt d.snapshot d.note.cm ∧
  st.fresh d.nf ∧
  d.note.amount ≠ 0 ∧
  U128 d.note.amount ∧
  d.note.amount ≤ st.balance d.note.token

/-- The thief's withdrawal: witness key `false` on the `true`-owned note. -/
abbrev wSteal : WithdrawData K := ⟨false, nOwned, (), 1⟩

/-- After the deposit, the ownership-free guard accepts the theft. This
part must elaborate. -/
theorem steal_guard : guardNoOwner wSteal (dOwned.post stK) := by
  refine ⟨?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · show (1:Nat) ∈ _
    norm_num [DepositData.post, St.empty, St.pushWindow, rootWindow]
  · show _ ∈ List.take 1 _
    norm_num [DepositData.post, St.empty, St.leaves, Note.cm]
  · show _ ∉ _
    norm_num [DepositData.post, St.empty, St.fresh]
  · show U128 5
    unfold U128 maxU128; norm_num
  · show (5:Nat) ≤ _
    norm_num [DepositData.post, St.empty, bump]

/-- The step relation with the ownership-free withdraw; deposit is real. -/
inductive StepNT : St K → Tx K → St K → Prop where
  | deposit {st : St K} {d : DepositData K} :
      d.guard st → StepNT st (.deposit d) (d.post st)
  | withdraw {st : St K} {d : WithdrawData K} :
      guardNoOwner d st → StepNT st (.withdraw d) (d.post st)

inductive RunNT : List (Tx K) → St K → Prop where
  | empty : RunNT [] stK
  | step {txs : List (Tx K)} {st st' : St K} {tx : Tx K} :
      RunNT txs st → StepNT st tx st' → RunNT (txs ++ [tx]) st'

theorem deposit_guard : dOwned.guard stK := by
  refine ⟨trivial, by norm_num, ?_, ?_⟩
  · show U128 5
    unfold U128 maxU128; norm_num
  · norm_num [St.empty, St.leaves]

/-- The ownership-free model ACCEPTS the end-to-end theft history. This
part must elaborate. -/
theorem theft_run :
    RunNT [.deposit dOwned, .withdraw wSteal] (wSteal.post (dOwned.post stK)) :=
  RunNT.step (RunNT.step RunNT.empty (StepNT.deposit deposit_guard))
    (StepNT.withdraw steal_guard)

/-- The theft history satisfies the conditional theorem's cryptographic
hypotheses (one note; one run key), so the failure below is due only to
the dropped ownership guard. This part must elaborate. -/
theorem theft_cryptoHyp : CryptoHyp K [.deposit dOwned, .withdraw wSteal] := by
  constructor
  · intro n hn m hm _ _ _
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl <;> rcases hm with rfl | rfl <;> rfl
  · intro k hk k' hk' _
    simp only [runKeys, List.flatMap_cons, List.flatMap_nil, Tx.keys,
      List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hk hk'
    subst hk; subst hk'; rfl

/-- The spendRequiresOwnerKey conclusion for the theft operation in the accepted history.
FALSE: the only witness key is `false` and `derivePub false = false ≠ true`.
The control passes only if this proof fails. -/
example : ∃ k ∈ (Tx.withdraw wSteal).keys, nOwned.ownedBy k := by
  norm_num [Tx.keys, Note.ownedBy]

end NegL4BOwnerKey
end LeanShieldedPool
