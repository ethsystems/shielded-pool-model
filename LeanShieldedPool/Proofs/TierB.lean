import LeanShieldedPool.Statements.L4B
import LeanShieldedPool.Proofs.Invariants
import LeanShieldedPool.Proofs.NoDoubleSpend
import LeanShieldedPool.Draft.NonVacuity

namespace LeanShieldedPool

variable {P : PrimSpec}

/-- Every operation in an accepted history has an accepted step. -/
theorem Run.step_of_mem {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (hr : Run sup txs st)
    {tx : Tx P} (htx : tx ∈ txs) :
    ∃ before after, Step before tx after := by
  induction hr with
  | empty => exact False.elim (List.not_mem_nil htx)
  | @step txs st st' last hr hs ih =>
      simp only [List.mem_append, List.mem_singleton] at htx
      rcases htx with hold | hlast
      · exact ih hold
      · subst tx
        exact ⟨st, st', hs⟩

/-- Only commitment binding is needed from the cryptographic hypotheses. -/
theorem spendRequiresOwnerKey_proof (P : PrimSpec) : spendRequiresOwnerKey P := by
  intro sup txs st hr hc tx htx n hn hcons
  obtain ⟨before, after, hs⟩ := hr.step_of_mem htx
  obtain ⟨input, hin, k, hk, hcm, howned, _, _⟩ := hs.consumes_witness hcons
  have hinRun : input ∈ runNotes txs :=
    List.mem_flatMap.mpr ⟨tx, htx, hin⟩
  have heq : input = n := hc.commit_inj input hinRun n hn
    (hr.runNotes_wf input hinRun) (hr.runNotes_wf n hn) hcm
  exact ⟨k, hk, heq ▸ howned⟩

/-- A spent commitment in the final state has an authorized consuming operation. -/
theorem Run.spent_ownedBy {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (hr : Run sup txs st)
    (hc : CryptoHyp P txs) {n : Note P} (hn : n ∈ runNotes txs)
    (hspent : st.spent n) :
    ∃ tx ∈ txs, n.cm ∈ tx.consumes ∧ ∃ k ∈ tx.keys, n.ownedBy k := by
  obtain ⟨tx, htx, hcons⟩ := List.mem_flatMap.mp (hr.spentCms_mem_iff.mp hspent)
  exact ⟨tx, htx, hcons, spendRequiresOwnerKey_proof P sup txs st hr hc tx htx n hn hcons⟩

namespace OwnerKeyNonVacuity

open NonVacuity

theorem deposit_guard : d0.guard st0 := by
  norm_num [DepositData.guard, St.empty, St.leaves, U128, maxU128]

theorem transfer_guard : t0.guard (d0.post st0) := by
  norm_num [TransferData.guard, TransferData.nf1, TransferData.nf2, Note.nf, Note.cm,
    Note.ownedBy, Note.isBallast, St.rootInWindow, St.inTreeAt, St.fresh, St.leaves,
    St.empty, St.pushWindow, rootWindow, DepositData.post, U128, maxU128]

theorem withdraw_guard : w0.guard (d0.post st0) := by
  norm_num [WithdrawData.guard, WithdrawData.nf, Note.nf, Note.cm, Note.ownedBy,
    St.rootInWindow, St.inTreeAt, St.fresh, St.leaves, St.empty, St.pushWindow,
    rootWindow, DepositData.post, U128, maxU128, bump]

theorem transfer_run : Run (fun _ => True) [.deposit d0, .transfer t0]
    (t0.post (d0.post st0)) :=
  Run.step (Run.step Run.empty (Step.deposit deposit_guard))
    (Step.transfer transfer_guard)

theorem withdraw_run : Run (fun _ => True) [.deposit d0, .withdraw w0]
    (w0.post (d0.post st0)) :=
  Run.step (Run.step Run.empty (Step.deposit deposit_guard))
    (Step.withdraw withdraw_guard)

theorem transfer_crypto : CryptoHyp Toy [.deposit d0, .transfer t0] := by
  constructor
  · intro n hn m hm _ _ hcm
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl | rfl | rfl | rfl <;>
      rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | norm_num [Note.cm, Toy, n0, t0] at hcm
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

theorem withdraw_crypto : CryptoHyp Toy [.deposit d0, .withdraw w0] := by
  constructor
  · intro n hn m hm _ _ _
    simp only [runNotes, List.flatMap_cons, List.flatMap_nil, Tx.notes,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hn hm
    rcases hn with rfl | rfl <;> rcases hm with rfl | rfl <;> rfl
  · intro k _ k' _ _
    exact Subsingleton.elim k k'

/-- Both spending operations have nonempty runs satisfying all hypotheses.
The consumed note has value five; the transfer also consumes its ballast input. -/
theorem spendRequiresOwnerKey_nonVacuity :
    ∃ (sup : Toy.Token → Prop) (txs : List (Tx Toy)) (st : St Toy)
      (n : Note Toy),
      Run sup txs st ∧ CryptoHyp Toy txs ∧ n.amount > 0 ∧
      n ∈ runNotes txs ∧ st.spent n ∧
      (∃ tx ∈ txs, n.cm ∈ tx.consumes ∧ ∃ k ∈ tx.keys, n.ownedBy k) := by
  have hn : n0 ∈ runNotes [.deposit d0, .withdraw w0] :=
    List.mem_cons_self
  have hs : (w0.post (d0.post st0)).spent n0 := List.mem_cons_self
  exact ⟨_, _, _, n0, withdraw_run, withdraw_crypto, by decide, hn, hs,
    withdraw_run.spent_ownedBy withdraw_crypto hn hs⟩

example : ∃ k ∈ (Tx.transfer t0).keys, t0.in1.ownedBy k :=
  spendRequiresOwnerKey_proof Toy _ _ _ transfer_run transfer_crypto (.transfer t0)
    (List.mem_cons_of_mem _ List.mem_cons_self) t0.in1 List.mem_cons_self
    List.mem_cons_self

example : ∃ k ∈ (Tx.transfer t0).keys, t0.in2.ownedBy k :=
  spendRequiresOwnerKey_proof Toy _ _ _ transfer_run transfer_crypto (.transfer t0)
    (List.mem_cons_of_mem _ List.mem_cons_self) t0.in2
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ List.mem_cons_self)

end OwnerKeyNonVacuity

#print axioms spendRequiresOwnerKey_proof
#print axioms Run.spent_ownedBy
#print axioms OwnerKeyNonVacuity.spendRequiresOwnerKey_nonVacuity

end LeanShieldedPool
