import LeanShieldedPool.Proofs.NoDoubleSpend

namespace LeanShieldedPool

open Classical

variable {P : PrimSpec}

private theorem runNotes_append (txs : List (Tx P)) (tx : Tx P) :
    runNotes (txs ++ [tx]) = runNotes txs ++ tx.notes := by
  simp only [runNotes, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

private theorem crypto_prefix {txs : List (Tx P)} {tx : Tx P}
    (hc : CryptoHyp P (txs ++ [tx])) : CryptoHyp P txs := by
  have hn : runNotes txs ⊆ runNotes (txs ++ [tx]) := by
    rw [runNotes_append]
    exact List.subset_append_left _ _
  have hk : runKeys txs ⊆ runKeys (txs ++ [tx]) := by
    simp only [runKeys, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    exact List.subset_append_left _ _
  exact ⟨fun n h n' h' hw hw' => hc.commit_inj n (hn h) n' (hn h') hw hw',
    fun k h k' h' => hc.derivePub_inj k (hk h) k' (hk h')⟩

private theorem Step.leaves_subset {st st' : St P} {tx : Tx P}
    (hs : Step st tx st') : st.leaves ⊆ st'.leaves := by
  cases hs with
  | deposit hg =>
      simp only [St.leaves, DepositData.post, List.map_append]
      exact List.subset_append_left _ _
  | transfer hg =>
      simp only [St.leaves, TransferData.post, List.map_append]
      exact List.subset_append_left _ _
  | withdraw hg => exact List.Subset.refl _

private theorem Step.consumes_covered {st st' : St P} {tx : Tx P}
    (hs : Step st tx st') {c : P.Commitment} (hc : c ∈ tx.consumes) :
    ∃ n ∈ tx.notes, n.cm = c ∧ (n.amount = 0 ∨ c ∈ st.leaves) := by
  cases hs with
  | deposit hg => exact False.elim (List.not_mem_nil hc)
  | @transfer d hg =>
      obtain ⟨_, _, _, h1, h2, _⟩ := hg
      simp only [Tx.consumes, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · exact ⟨d.in1, List.mem_cons_self, hc.symm,
          Or.inr (hc ▸ List.mem_of_mem_take h1)⟩
      · refine ⟨d.in2, List.mem_cons_of_mem _ List.mem_cons_self, hc.symm, ?_⟩
        rcases h2 with hz | hm
        · exact Or.inl hz
        · exact Or.inr (hc ▸ List.mem_of_mem_take hm)
  | @withdraw d hg =>
      simp only [Tx.consumes, List.mem_singleton] at hc
      exact ⟨d.note, List.mem_cons_self, hc.symm,
        Or.inr (hc ▸ List.mem_of_mem_take hg.2.1)⟩

private theorem Run.spentCms_covered {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (hr : Run sup txs st)
    {c : P.Commitment} (hc : c ∈ st.spentCms) :
    ∃ n ∈ runNotes txs, n.cm = c ∧ (n.amount = 0 ∨ c ∈ st.leaves) := by
  induction hr with
  | empty => exact False.elim (List.not_mem_nil hc)
  | @step txs st st' tx hr hs ih =>
      rw [runNotes_append]
      rcases List.mem_append.mp (hs.spentCms_perm.mem_iff.mpr hc) with hold | hnew
      · obtain ⟨n, hn, heq, hz | hm⟩ := ih hold
        · exact ⟨n, List.mem_append_left _ hn, heq, Or.inl hz⟩
        · exact ⟨n, List.mem_append_left _ hn, heq, Or.inr (hs.leaves_subset hm)⟩
      · obtain ⟨n, hn, heq, hz | hm⟩ := hs.consumes_covered hnew
        · exact ⟨n, List.mem_append_right _ hn, heq, Or.inl hz⟩
        · exact ⟨n, List.mem_append_right _ hn, heq, Or.inr (hs.leaves_subset hm)⟩

private noncomputable def tokenValue (t : P.Token) (n : Note P) : Nat :=
  if n.token = t then n.amount else 0

private noncomputable def liveSum (ns : List (Note P))
    (spent : List P.Commitment) (t : P.Token) : Nat :=
  (ns.map fun n => if n.token = t ∧ n.cm ∉ spent then n.amount else 0).sum

private theorem liveValue_eq_liveSum (st : St P) (t : P.Token) :
    liveValue st t = liveSum st.minted st.spentCms t := by
  unfold liveValue liveSum
  congr 1
  apply List.map_congr_left
  intro n _
  unfold noteValue St.spent
  by_cases h : n.token = t ∧ n.cm ∉ st.spentCms
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

private theorem liveSum_absent (ns : List (Note P)) (spent : List P.Commitment)
    (t : P.Token) (c : P.Commitment) (hc : c ∉ ns.map Note.cm) :
    liveSum ns (c :: spent) t = liveSum ns spent t := by
  unfold liveSum
  congr 1
  apply List.map_congr_left
  intro n hn
  have hne : n.cm ≠ c := by
    intro heq
    exact hc (List.mem_map.mpr ⟨n, hn, heq⟩)
  simp only [List.mem_cons, hne, false_or]

private theorem liveSum_cons_spent (ns : List (Note P)) (spent : List P.Commitment)
    (t : P.Token) (n : Note P) (hd : (ns.map Note.cm).Nodup)
    (hi : ∀ m ∈ ns, m.cm = n.cm → m = n)
    (hf : n.cm ∉ spent) (hm : n.amount = 0 ∨ n ∈ ns) :
    liveSum ns spent t = tokenValue t n + liveSum ns (n.cm :: spent) t := by
  induction ns with
  | nil =>
      have hz : n.amount = 0 := hm.resolve_right List.not_mem_nil
      simp only [liveSum, List.map_nil, List.sum_nil, tokenValue, hz, ite_self,
        Nat.zero_add]
  | cons m ms ih =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hd
      by_cases heq : m.cm = n.cm
      · have hmn := hi m List.mem_cons_self heq
        subst m
        have hsame := liveSum_absent ms spent t n.cm hnot
        change (if n.token = t ∧ n.cm ∉ spent then n.amount else 0) +
          liveSum ms spent t = tokenValue t n +
            ((if n.token = t ∧ n.cm ∉ n.cm :: spent then n.amount else 0) +
              liveSum ms (n.cm :: spent) t)
        rw [hsame]
        simp only [hf, not_false_eq_true, and_true, List.mem_cons_self,
          not_true_eq_false, and_false, if_false, Nat.zero_add, tokenValue]
      · have hsame :
            (if m.token = t ∧ m.cm ∉ n.cm :: spent then m.amount else 0) =
              (if m.token = t ∧ m.cm ∉ spent then m.amount else 0) := by
          simp only [List.mem_cons, heq, false_or]
        have hmem : n.amount = 0 ∨ n ∈ ms := by
          rcases hm with hz | hm
          · exact Or.inl hz
          · rcases List.mem_cons.mp hm with hnm | hn
            · exact False.elim (heq (congrArg Note.cm hnm.symm))
            · exact Or.inr hn
        have hrec := ih htail (fun m hm => hi m (List.mem_cons_of_mem _ hm)) hmem
        simp only [liveSum, List.map_cons, List.sum_cons] at hrec ⊢
        rw [hsame]
        omega

private theorem liveSum_append (ns ms : List (Note P)) (spent : List P.Commitment)
    (t : P.Token) :
    liveSum (ns ++ ms) spent t = liveSum ns spent t + liveSum ms spent t := by
  simp only [liveSum, List.map_append, List.sum_append]

private theorem fresh_output_value {sup : P.Token → Prop}
    {txs : List (Tx P)} {st st' : St P} {tx : Tx P}
    (hr : Run sup txs st) (hs : Step st tx st')
    (hc : CryptoHyp P (txs ++ [tx])) {n : Note P}
    (hn : n ∈ tx.notes) (hf : n.cm ∉ st.leaves) (t : P.Token) :
    (if n.token = t ∧ n.cm ∉ st'.spentCms then n.amount else 0) = tokenValue t n := by
  have hz : n.cm ∈ st'.spentCms → n.amount = 0 := by
    intro hm
    have hcovered : ∃ m ∈ runNotes (txs ++ [tx]),
        m.cm = n.cm ∧ (m.amount = 0 ∨ n.cm ∈ st.leaves) := by
      rw [runNotes_append]
      rcases List.mem_append.mp (hs.spentCms_perm.mem_iff.mpr hm) with hold | hnew
      · obtain ⟨m, hm, heq, h⟩ := hr.spentCms_covered hold
        exact ⟨m, List.mem_append_left _ hm, heq, h⟩
      · obtain ⟨m, hm, heq, h⟩ := hs.consumes_covered hnew
        exact ⟨m, List.mem_append_right _ hm, heq, h⟩
    obtain ⟨m, hm, heq, h⟩ := hcovered
    have hn' : n ∈ runNotes (txs ++ [tx]) := by
      rw [runNotes_append]
      exact List.mem_append_right _ hn
    have hmn := hc.commit_inj m hm n hn'
      ((hr.step hs).runNotes_wf m hm) (hs.notes_wf n hn) heq
    subst m
    exact h.resolve_right hf
  by_cases hm : n.cm ∈ st'.spentCms
  · simp only [hm, not_true_eq_false, and_false, tokenValue, hz hm, ite_self]
  · simp only [hm, not_false_eq_true, and_true, tokenValue]

private theorem input_present {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} {tx : Tx P}
    (hr : Run sup txs st) (hc : CryptoHyp P (txs ++ [tx]))
    {n : Note P} (hn : n ∈ tx.notes) (hwf : n.wf)
    (hm : n.amount = 0 ∨ n.cm ∈ st.leaves) :
    n.amount = 0 ∨ n ∈ st.minted := by
  rcases hm with hz | hm
  · exact Or.inl hz
  · obtain ⟨m, hm, heq⟩ := List.mem_map.mp hm
    have hmn : m = n := hc.commit_inj m (by
        rw [runNotes_append]
        exact List.mem_append_left _ (hr.minted_mem_runNotes hm)) n (by
        rw [runNotes_append]
        exact List.mem_append_right _ hn)
      (hr.runNotes_wf m (hr.minted_mem_runNotes hm)) hwf heq
    exact Or.inr (hmn ▸ hm)

theorem valueConservation_proof (P : PrimSpec) : valueConservation P := by
  intro sup txs st hr
  induction hr with
  | empty =>
      intro _ t
      rfl
  | @step txs st st' tx hr hs ih =>
      intro hc t
      have hold := ih (crypto_prefix hc) t
      have hi : ∀ n ∈ tx.notes, ∀ m ∈ st.minted, m.cm = n.cm → m = n := by
        intro n hn m hm heq
        apply hc.commit_inj m _ n _
          (hr.runNotes_wf m (hr.minted_mem_runNotes hm)) (hs.notes_wf n hn) heq
        · rw [runNotes_append]
          exact List.mem_append_left _ (hr.minted_mem_runNotes hm)
        · rw [runNotes_append]
          exact List.mem_append_right _ hn
      cases hs with
      | @deposit d hg =>
          have hout := fresh_output_value hr (Step.deposit hg) hc
            List.mem_cons_self hg.2.2.2 t
          have hlive : liveValue (d.post st) t = liveValue st t + tokenValue t d.note := by
            rw [liveValue_eq_liveSum, liveValue_eq_liveSum]
            change liveSum (st.minted ++ [d.note]) st.spentCms t =
              liveSum st.minted st.spentCms t + tokenValue t d.note
            rw [liveSum_append]
            change liveSum st.minted st.spentCms t +
              ((if d.note.token = t ∧ d.note.cm ∉ st.spentCms then d.note.amount else 0) + 0) = _
            rw [show (if d.note.token = t ∧ d.note.cm ∉ st.spentCms
              then d.note.amount else 0) = tokenValue t d.note from hout]
            exact congrArg _ (Nat.add_zero _)
          change bump st.deposited d.note.token d.note.amount t =
            st.withdrawn t + liveValue (d.post st) t
          rw [hlive]
          unfold bump tokenValue
          by_cases ht : t = d.note.token
          · subst t
            simp only [ite_true]
            omega
          · simp only [ht, Ne.symm ht, if_false, Nat.add_zero]
            exact hold
      | @transfer d hg =>
          have hs := Step.transfer hg
          obtain ⟨_, _, _, hm1, hm2, _, _, _, ht2, hto1, hto2,
            hu1, hu2, _, _, hvalue, ho1, ho2, _⟩ := hg
          have hn1 : d.in1 ∈ (Tx.transfer d).notes := List.mem_cons_self
          have hn2 : d.in2 ∈ (Tx.transfer d).notes :=
            List.mem_cons_of_mem _ List.mem_cons_self
          have hno1 : d.out1 ∈ (Tx.transfer d).notes :=
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
          have hno2 : d.out2 ∈ (Tx.transfer d).notes :=
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))
          have hp1 := input_present hr hc hn1 hu1
            (Or.inr (List.mem_of_mem_take hm1))
          have hp2 := input_present hr hc hn2 hu2
            (hm2.imp id (fun h => List.mem_of_mem_take h))
          have hspent := (hr.step hs).spentCms_nodup hc
          obtain ⟨hf1, hrest⟩ := List.nodup_cons.mp hspent
          obtain ⟨hf2, _⟩ := List.nodup_cons.mp hrest
          have hremove2 := liveSum_cons_spent st.minted st.spentCms t d.in2
            hr.leaves_nodup (hi d.in2 hn2) hf2 hp2
          have hremove1 := liveSum_cons_spent st.minted (d.in2.cm :: st.spentCms) t d.in1
            hr.leaves_nodup (hi d.in1 hn1) hf1 hp1
          have hv1 := fresh_output_value hr hs hc hno1 ho1 t
          have hv2 := fresh_output_value hr hs hc hno2 ho2 t
          have hpost : liveValue (d.post st) t =
              liveSum st.minted (d.post st).spentCms t +
                (tokenValue t d.out1 + tokenValue t d.out2) := by
            rw [liveValue_eq_liveSum]
            change liveSum (st.minted ++ [d.out1, d.out2]) (d.post st).spentCms t = _
            rw [liveSum_append]
            change liveSum st.minted (d.post st).spentCms t +
              ((if d.out1.token = t ∧ d.out1.cm ∉ (d.post st).spentCms
                then d.out1.amount else 0) +
              ((if d.out2.token = t ∧ d.out2.cm ∉ (d.post st).spentCms
                then d.out2.amount else 0) + 0)) = _
            rw [hv1, hv2, Nat.add_zero]
          have htokens : tokenValue t d.in1 + tokenValue t d.in2 =
              tokenValue t d.out1 + tokenValue t d.out2 := by
            unfold tokenValue
            rw [ht2, hto1, hto2]
            by_cases ht : d.in1.token = t
            · simp only [ht, if_true]
              exact hvalue
            · simp only [ht, if_false]
          change st.deposited t = st.withdrawn t + liveValue (d.post st) t
          rw [liveValue_eq_liveSum] at hold
          change liveSum st.minted (d.in2.cm :: st.spentCms) t =
            tokenValue t d.in1 + liveSum st.minted (d.post st).spentCms t at hremove1
          omega
      | @withdraw d hg =>
          have hn : d.note ∈ (Tx.withdraw d).notes := List.mem_cons_self
          have hp := input_present hr hc hn hg.2.2.2.2.2.1
            (Or.inr (List.mem_of_mem_take hg.2.1))
          have hf := (List.nodup_cons.mp
            ((hr.step (Step.withdraw hg)).spentCms_nodup hc)).1
          have hremove := liveSum_cons_spent st.minted st.spentCms t d.note
            hr.leaves_nodup (hi d.note hn) hf hp
          change st.deposited t = bump st.withdrawn d.note.token d.note.amount t +
            liveValue (d.post st) t
          rw [liveValue_eq_liveSum]
          change st.deposited t = bump st.withdrawn d.note.token d.note.amount t +
            liveSum st.minted (d.note.cm :: st.spentCms) t
          rw [liveValue_eq_liveSum] at hold
          unfold bump
          unfold tokenValue at hremove
          by_cases ht : t = d.note.token
          · subst t
            simp only [ite_true] at hremove ⊢
            omega
          · simp only [ht, Ne.symm ht, if_false, Nat.zero_add] at hremove ⊢
            omega

end LeanShieldedPool
