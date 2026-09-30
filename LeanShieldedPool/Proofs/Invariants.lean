import LeanShieldedPool.Statements.L3

namespace LeanShieldedPool

variable {P : PrimSpec}

theorem Tx.consumes_mem_notes {tx : Tx P} {c : P.Commitment}
    (hc : c ∈ tx.consumes) : ∃ n ∈ tx.notes, n.cm = c := by
  cases tx with
  | deposit d =>
      simp only [Tx.consumes, List.not_mem_nil] at hc
  | transfer d =>
      simp only [Tx.consumes, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h
      · exact ⟨d.in1, List.mem_cons_self, h.symm⟩
      · exact ⟨d.in2, List.mem_cons_of_mem _ List.mem_cons_self, h.symm⟩
  | withdraw d =>
      simp only [Tx.consumes, List.mem_singleton] at hc
      exact ⟨d.note, List.mem_cons_self, hc.symm⟩

theorem spentCommitments_mem_runNotes {txs : List (Tx P)} {c : P.Commitment}
    (hc : c ∈ spentCommitments txs) : ∃ n ∈ runNotes txs, n.cm = c := by
  obtain ⟨tx, htx, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨n, hn, hcm⟩ := Tx.consumes_mem_notes hc
  exact ⟨n, List.mem_flatMap.mpr ⟨tx, htx, hn⟩, hcm⟩

theorem Step.spentCms_perm {st st' : St P} {tx : Tx P}
    (h : Step st tx st') :
    (st.spentCms ++ tx.consumes).Perm st'.spentCms := by
  cases h with
  | deposit hg =>
      simp only [Tx.consumes, DepositData.post, List.append_nil]
      exact List.Perm.refl _
  | transfer hg =>
      exact List.perm_append_comm
  | withdraw hg =>
      exact List.perm_append_comm

/-- Transfers prepend their inputs in public-input order, so use permutation. -/
theorem Run.spentCommitments_perm {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st) :
    (spentCommitments txs).Perm st.spentCms := by
  induction h with
  | empty => exact List.Perm.refl []
  | @step txs st st' tx hr hs ih =>
      simp only [spentCommitments, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact (ih.append_right tx.consumes).trans hs.spentCms_perm

theorem Run.spentCms_mem_iff {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st) {c : P.Commitment} :
    c ∈ st.spentCms ↔ c ∈ txs.flatMap Tx.consumes :=
  h.spentCommitments_perm.mem_iff.symm

theorem Run.spentCms_mem_runNotes {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st)
    {c : P.Commitment} (hc : c ∈ st.spentCms) :
    (∃ n ∈ runNotes txs, n.cm = c) ∧ c ∈ txs.flatMap Tx.consumes := by
  have hcons := h.spentCms_mem_iff.mp hc
  exact ⟨spentCommitments_mem_runNotes hcons, hcons⟩

theorem Step.minted_mem {st st' : St P} {tx : Tx P}
    (h : Step st tx st') {n : Note P} (hn : n ∈ st'.minted) :
    n ∈ st.minted ∨ n ∈ tx.notes := by
  cases h <;>
    simp only [DepositData.post, TransferData.post, WithdrawData.post,
      Tx.notes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at * <;>
    tauto

theorem Run.minted_mem_runNotes {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st)
    {n : Note P} (hn : n ∈ st.minted) : n ∈ runNotes txs := by
  induction h with
  | empty => exact False.elim (List.not_mem_nil hn)
  | @step txs st st' tx hr hs ih =>
      simp only [runNotes, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append]
      rcases hs.minted_mem hn with hold | hnew
      · exact Or.inl (ih hold)
      · exact Or.inr hnew

theorem Step.leaves_nodup {st st' : St P} {tx : Tx P}
    (h : Step st tx st') (hn : st.leaves.Nodup) : st'.leaves.Nodup := by
  cases h with
  | @deposit d hg =>
      have hfresh := hg.2.2.2
      simp only [St.leaves, DepositData.post, List.map_append, List.map_cons,
        List.map_nil]
      apply List.nodup_append.mpr
      refine ⟨hn, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro heq
      exact hfresh (heq ▸ ha)
  | @transfer d hg =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, hne⟩ := hg
      simp only [St.leaves, TransferData.post, List.map_append, List.map_cons,
        List.map_nil]
      apply List.nodup_append.mpr
      refine ⟨hn, ?_, ?_⟩
      · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]
        exact hne
      · intro a ha b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with hb | hb
        · subst b
          intro heq
          exact h1 (heq ▸ ha)
        · subst b
          intro heq
          exact h2 (heq ▸ ha)
  | withdraw hg => exact hn

theorem Run.leaves_nodup {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st) : st.leaves.Nodup := by
  induction h with
  | empty => exact List.nodup_nil
  | step hr hs ih => exact hs.leaves_nodup ih

end LeanShieldedPool
