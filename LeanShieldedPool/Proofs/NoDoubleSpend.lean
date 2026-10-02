import LeanShieldedPool.Proofs.Invariants

namespace LeanShieldedPool

variable {P : PrimSpec}

theorem Step.nullifiers_eq {st st' : St P} {tx : Tx P}
    (h : Step st tx st') : st'.nullifiers = tx.spends ++ st.nullifiers := by
  cases h <;> rfl

theorem Step.nullifiers_nodup {st st' : St P} {tx : Tx P}
    (h : Step st tx st') (hn : st.nullifiers.Nodup) : st'.nullifiers.Nodup := by
  cases h with
  | deposit hg => exact hn
  | transfer hg =>
      obtain ⟨_, _, _, _, _, h1, h2, hne, _⟩ := hg
      exact List.nodup_cons.mpr ⟨by
        simp only [List.mem_cons, not_or]
        exact ⟨hne, h1⟩, List.nodup_cons.mpr ⟨h2, hn⟩⟩
  | withdraw hg =>
      exact List.nodup_cons.mpr ⟨hg.2.2.2.1, hn⟩

theorem Run.nullifiers_nodup {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st) : st.nullifiers.Nodup := by
  induction h with
  | empty => exact List.nodup_nil
  | step hr hs ih => exact hs.nullifiers_nodup ih

theorem Run.spends_perm {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st) :
    (txs.flatMap Tx.spends).Perm st.nullifiers := by
  induction h with
  | empty => exact List.Perm.refl []
  | @step txs st st' tx hr hs ih =>
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, hs.nullifiers_eq]
      exact (ih.append_right tx.spends).trans List.perm_append_comm

theorem nullifierUniqueness_proof (P : PrimSpec) : nullifierUniqueness P := by
  intro sup txs st hr
  exact hr.spends_perm.nodup_iff.mpr hr.nullifiers_nodup

theorem Step.consumes_witness {st st' : St P} {tx : Tx P}
    (h : Step st tx st') {c : P.Commitment} (hc : c ∈ tx.consumes) :
    ∃ n ∈ tx.notes, ∃ k ∈ tx.keys,
      n.cm = c ∧ n.ownedBy k ∧ n.nf k ∈ tx.spends ∧ st.fresh (n.nf k) := by
  cases h with
  | deposit hg => exact False.elim (List.not_mem_nil hc)
  | @transfer d hg =>
      obtain ⟨_, ho1, ho2, _, _, hf1, hf2, _⟩ := hg
      simp only [Tx.consumes, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · exact ⟨d.in1, List.mem_cons_self, d.key, List.mem_cons_self,
          hc.symm, ho1, List.mem_cons_self, hf1⟩
      · exact ⟨d.in2, List.mem_cons_of_mem _ List.mem_cons_self,
          d.key, List.mem_cons_self, hc.symm, ho2,
          List.mem_cons_of_mem _ List.mem_cons_self, hf2⟩
  | @withdraw d hg =>
      simp only [Tx.consumes, List.mem_singleton] at hc
      exact ⟨d.note, List.mem_cons_self, d.key, List.mem_cons_self,
        hc.symm, hg.2.2.1, List.mem_cons_self, hg.2.2.2.1⟩

theorem Run.spentCms_witness {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (h : Run sup txs st)
    {c : P.Commitment} (hc : c ∈ st.spentCms) :
    ∃ n ∈ runNotes txs, ∃ k ∈ runKeys txs,
      n.cm = c ∧ n.ownedBy k ∧ n.nf k ∈ st.nullifiers := by
  induction h with
  | empty => exact False.elim (List.not_mem_nil hc)
  | @step txs st st' tx hr hs ih =>
      have hm := hs.spentCms_perm.mem_iff.mpr hc
      simp only [List.mem_append] at hm
      simp only [runNotes, runKeys, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append, hs.nullifiers_eq]
      rcases hm with hold | hnew
      · obtain ⟨n, hn, k, hk, hcm, ho, hnf⟩ := ih hold
        exact ⟨n, Or.inl hn, k, Or.inl hk, hcm, ho, Or.inr hnf⟩
      · obtain ⟨n, hn, k, hk, hcm, ho, hnf, _⟩ := hs.consumes_witness hnew
        exact ⟨n, Or.inr hn, k, Or.inr hk, hcm, ho, Or.inl hnf⟩

theorem Step.consumes_nodup {st st' : St P} {tx : Tx P}
    (h : Step st tx st')
    (hinj : ∀ n ∈ tx.notes, ∀ n' ∈ tx.notes, n.cm = n'.cm → n = n') :
    tx.consumes.Nodup := by
  cases h with
  | deposit hg => exact List.nodup_nil
  | @transfer d hg =>
      have hne := hg.2.2.2.2.2.2.2.1
      apply List.nodup_cons.mpr
      refine ⟨?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton]
      intro hcm
      have heq := hinj d.in1 List.mem_cons_self d.in2
        (List.mem_cons_of_mem _ List.mem_cons_self) hcm
      exact hne (congrArg (fun n => n.nf d.key) heq)
  | withdraw hg => exact List.nodup_singleton _

theorem Run.spentCms_nodup {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (hr : Run sup txs st) :
    CryptoHyp P txs → st.spentCms.Nodup := by
  induction hr with
  | empty => intro _; exact List.nodup_nil
  | @step txs st st' tx hr hs ih =>
      intro hcrypto
      have hnotes : runNotes (txs ++ [tx]) = runNotes txs ++ tx.notes := by
        simp only [runNotes, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      have hkeys : runKeys (txs ++ [tx]) = runKeys txs ++ tx.keys := by
        simp only [runKeys, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      have oldNotes : runNotes txs ⊆ runNotes (txs ++ [tx]) := by
        rw [hnotes]
        exact List.subset_append_left _ _
      have newNotes : tx.notes ⊆ runNotes (txs ++ [tx]) := by
        rw [hnotes]
        exact List.subset_append_right _ _
      have oldKeys : runKeys txs ⊆ runKeys (txs ++ [tx]) := by
        rw [hkeys]
        exact List.subset_append_left _ _
      have newKeys : tx.keys ⊆ runKeys (txs ++ [tx]) := by
        rw [hkeys]
        exact List.subset_append_right _ _
      have hprefix : CryptoHyp P txs :=
        ⟨fun n hn n' hn' hw hw' =>
            hcrypto.commit_inj n (oldNotes hn) n' (oldNotes hn') hw hw',
          fun k hk k' hk' => hcrypto.derivePub_inj k (oldKeys hk) k' (oldKeys hk')⟩
      have hfresh : ∀ c ∈ tx.consumes, c ∉ st.spentCms := by
        intro c hc hold
        obtain ⟨n, hn, k, hk, hcm, ho, _, hf⟩ := hs.consumes_witness hc
        obtain ⟨n', hn', k', hk', hcm', ho', hnf⟩ := hr.spentCms_witness hold
        have heq := hcrypto.commit_inj n (newNotes hn) n' (oldNotes hn')
          (hs.notes_wf n hn) (hr.runNotes_wf n' hn') (hcm.trans hcm'.symm)
        have hpub : P.derivePub k = P.derivePub k' :=
          ho.trans ((congrArg Note.ownerPubkey heq).trans ho'.symm)
        have hkey := hcrypto.derivePub_inj k (newKeys hk) k' (oldKeys hk') hpub
        apply hf
        rw [heq, hkey]
        exact hnf
      apply hs.spentCms_perm.nodup_iff.mp
      apply List.nodup_append.mpr
      refine ⟨ih hprefix, hs.consumes_nodup ?_, ?_⟩
      · exact fun n hn n' hn' =>
          hcrypto.commit_inj n (newNotes hn) n' (newNotes hn')
            (hs.notes_wf n hn) (hs.notes_wf n' hn')
      · intro a ha b hb heq
        exact hfresh b hb (heq ▸ ha)

theorem noDoubleSpend_proof (P : PrimSpec) : noDoubleSpend P := by
  intro sup txs st hr hcrypto
  exact hr.spentCommitments_perm.nodup_iff.mpr (hr.spentCms_nodup hcrypto)

end LeanShieldedPool
