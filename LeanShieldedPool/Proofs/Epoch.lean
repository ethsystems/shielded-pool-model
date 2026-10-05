import LeanShieldedPool.Proofs.EpochBase

/-!
Semantic L5 proofs. Recorded consumption retains its epoch and owner key through
rollovers. The proofs use finite-run binding, without epoch distinctness.
-/

namespace LeanShieldedPool.Epoch

open Candidates

variable {P : PrimSpec}

/-- A consumed witness still has a nullifier in its spending epoch's list. -/
def Recorded (st : St P) (n : Note P) (key : P.SpendKey) : Prop :=
  ∃ e, n.epochCreated ≤ e ∧ e ≤ st.currentEpoch ∧
    (if e = st.currentEpoch then n.nfE key e ∈ st.active
     else n.nfE key e ∈ st.frozen e)

theorem Step.epoch_mono {st st' : St P} {tx : Tx P} (h : Step st tx st') :
    st.currentEpoch ≤ st'.currentEpoch := by
  cases h <;> first | exact Nat.le_refl _ | exact Nat.le_succ _

theorem Step.frozen_preserved {st st' : St P} {tx : Tx P}
    (h : Step st tx st') {e : Nat} (he : e < st.currentEpoch) :
    st'.frozen e = st.frozen e := by
  cases h with
  | deposit _ => rfl
  | transfer _ => rfl
  | withdraw _ => rfl
  | rollover =>
      exact if_neg (Nat.ne_of_lt he)

theorem Step.recorded_preserved {st st' : St P} {tx : Tx P}
    (h : Step st tx st') {n : Note P} {key : P.SpendKey}
    (hr : Recorded st n key) : Recorded st' n key := by
  obtain ⟨e, hc, he, hm⟩ := hr
  refine ⟨e, hc, he.trans h.epoch_mono, ?_⟩
  cases h with
  | deposit _ => exact hm
  | transfer _ =>
      change if e = st.currentEpoch then _ ∈ st.active ++ _ else _ ∈ st.frozen e
      split_ifs with eq
      · rw [if_pos eq] at hm
        exact List.mem_append_left _ hm
      · rw [if_neg eq] at hm
        exact hm
  | withdraw _ =>
      change if e = st.currentEpoch then _ ∈ st.active ++ _ else _ ∈ st.frozen e
      split_ifs with eq
      · rw [if_pos eq] at hm
        exact List.mem_append_left _ hm
      · rw [if_neg eq] at hm
        exact hm
  | rollover =>
      have hn : e ≠ st.currentEpoch + 1 := by omega
      change if e = st.currentEpoch + 1 then _ ∈ []
        else _ ∈ (if e = st.currentEpoch then st.active else st.frozen e)
      rw [if_neg hn]
      by_cases eq : e = st.currentEpoch
      · rw [if_pos eq]; rw [if_pos eq] at hm; exact hm
      · rw [if_neg eq]; rw [if_neg eq] at hm; exact hm

theorem SpendGuard.not_recorded {st : St P} {n : Note P} {key : P.SpendKey}
    (h : SpendGuard st n key) : ¬ Recorded st n key := by
  rintro ⟨e, hc, he, hm⟩
  by_cases eq : e = st.currentEpoch
  · subst e
    exact h.2.1.1 (by simpa only [ite_true, eq_self_iff_true] using hm)
  · exact h.1.2 e hc (by omega) (by simpa only [if_neg eq] using hm)

/-- Both transfer slots yield the full history guard, including ballast. -/
theorem Step.consumes_witness {st st' : St P} {tx : Tx P}
    (h : Step st tx st') {c : P.Commitment} (hc : c ∈ tx.consumes) :
    ∃ n ∈ notes tx, ∃ key ∈ (inputs tx).map Prod.snd,
      n.cm = c ∧ n.ownedBy key ∧ SpendGuard st n key ∧ Recorded st' n key := by
  cases h with
  | deposit _ => exact False.elim (List.not_mem_nil hc)
  | rollover => exact False.elim (List.not_mem_nil hc)
  | @transfer d hg =>
      obtain ⟨_, ho1, ho2, _, _, hchain1, hchain2, hins, _⟩ := hg
      have hf1 := hins.1.1
      have hf2 : d.in2.nfE d.key st.currentEpoch ∉ st.active := by
        intro hm
        exact hins.1.2.1 (List.mem_append_left _ hm)
      simp only [Tx.consumes, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · refine ⟨d.in1, List.mem_cons_self, d.key, ?_, hc.symm, ho1,
          ⟨hchain1, ⟨⟨hf1, trivial⟩, rfl⟩⟩, ?_⟩
        · exact List.mem_cons_self
        · refine ⟨st.currentEpoch, hchain1.1, Nat.le_refl _, ?_⟩
          simp only [TransferData.post, ite_true, TransferData.nullifiers,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          exact Or.inr (Or.inl trivial)
      · refine ⟨d.in2, List.mem_cons_of_mem _ List.mem_cons_self, d.key, ?_,
          hc.symm, ho2, ⟨hchain2, ⟨⟨hf2, trivial⟩, rfl⟩⟩, ?_⟩
        · exact List.mem_cons_self
        · refine ⟨st.currentEpoch, hchain2.1, Nat.le_refl _, ?_⟩
          simp only [TransferData.post, ite_true, TransferData.nullifiers,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          exact Or.inr (Or.inr trivial)
  | @withdraw d hg =>
      have hg' := hg.2.2.2.1
      simp only [Tx.consumes, List.mem_singleton] at hc
      refine ⟨d.note, List.mem_cons_self, d.key, List.mem_cons_self,
        hc.symm, hg.2.2.1, hg', st.currentEpoch, hg'.1.1, Nat.le_refl _, ?_⟩
      simp only [WithdrawData.post, WithdrawData.nf, ite_true, List.mem_append,
        List.mem_singleton]
      exact Or.inr trivial

theorem Step.consumes_nodup {st st' : St P} {tx : Tx P}
    (h : Step st tx st') : tx.consumes.Nodup := by
  cases h with
  | deposit _ => exact List.nodup_nil
  | rollover => exact List.nodup_nil
  | withdraw _ => exact List.nodup_singleton _
  | @transfer d hg =>
      have hf := hg.2.2.2.2.2.2.2.1.1.2.1
      apply List.nodup_cons.mpr
      refine ⟨?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton]
      intro heq
      apply hf
      apply List.mem_append_right
      simp only [List.mem_singleton, Note.nfE, heq]

theorem runNotes_append (txs : List (Tx P)) (tx : Tx P) :
    Candidates.runNotes (txs ++ [tx]) = Candidates.runNotes txs ++ notes tx := by
  simp only [Candidates.runNotes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem runKeys_append (txs : List (Tx P)) (tx : Tx P) :
    Candidates.runKeys (txs ++ [tx]) = Candidates.runKeys txs ++ (inputs tx).map Prod.snd := by
  simp only [Candidates.runKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_append]

/-- This invariant records every consumption in the complete transaction log. -/
theorem Run.consumed_recorded {sup : P.Token → Prop} {txs : List (Tx P)}
    {st : St P} (h : Run sup txs st) {c : P.Commitment}
    (hc : c ∈ txs.flatMap Tx.consumes) :
    ∃ n ∈ Candidates.runNotes txs, ∃ key ∈ Candidates.runKeys txs,
      n.cm = c ∧ n.ownedBy key ∧ Recorded st n key := by
  induction h with
  | empty => exact False.elim (List.not_mem_nil hc)
  | @step txs st st' tx hr hs ih =>
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_append] at hc
      rw [runNotes_append, runKeys_append]
      rcases hc with hc | hc
      · obtain ⟨n, hn, key, hk, hcm, ho, hm⟩ := ih hc
        exact ⟨n, List.mem_append_left _ hn, key, List.mem_append_left _ hk,
          hcm, ho, hs.recorded_preserved hm⟩
      · obtain ⟨n, hn, key, hk, hcm, ho, _, hm⟩ := hs.consumes_witness hc
        exact ⟨n, List.mem_append_right _ hn, key, List.mem_append_right _ hk,
          hcm, ho, hm⟩

theorem crossEpochNoDoubleSpend_proof (P : PrimSpec) : crossEpochNoDoubleSpend P := by
  intro sup txs st hr
  induction hr with
  | empty => intro _; exact List.nodup_nil
  | @step txs st st' tx hr hs ih =>
      intro hcrypto
      have oldNotes : Candidates.runNotes txs ⊆ Candidates.runNotes (txs ++ [tx]) := by
        rw [runNotes_append]; exact List.subset_append_left _ _
      have newNotes : notes tx ⊆ Candidates.runNotes (txs ++ [tx]) := by
        rw [runNotes_append]; exact List.subset_append_right _ _
      have oldKeys : Candidates.runKeys txs ⊆ Candidates.runKeys (txs ++ [tx]) := by
        rw [runKeys_append]; exact List.subset_append_left _ _
      have newKeys : (inputs tx).map Prod.snd ⊆ Candidates.runKeys (txs ++ [tx]) := by
        rw [runKeys_append]; exact List.subset_append_right _ _
      have hp : Candidates.CryptoHyp P txs :=
        ⟨fun n hn n' hn' => hcrypto.commit_inj n (oldNotes hn) n' (oldNotes hn'),
         fun k hk k' hk' => hcrypto.derivePub_inj k (oldKeys hk) k' (oldKeys hk')⟩
      change ((txs ++ [tx]).flatMap Tx.consumes).Nodup
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      apply List.nodup_append.mpr
      refine ⟨ih hp, hs.consumes_nodup, ?_⟩
      intro c hc c' hc' heq
      obtain ⟨n, hn, k, hk, hcm, ho, hm⟩ := hr.consumed_recorded hc
      obtain ⟨n', hn', k', hk', hcm', ho', hg, _⟩ := hs.consumes_witness hc'
      have hnEq := hcrypto.commit_inj n (oldNotes hn) n' (newNotes hn')
        (hcm.trans (heq.trans hcm'.symm))
      have hpub : P.derivePub k = P.derivePub k' :=
        ho.trans ((congrArg (fun n : Note P => n.ownerPubkey) hnEq).trans ho'.symm)
      have hkEq := hcrypto.derivePub_inj k (oldKeys hk) k' (newKeys hk') hpub
      exact hg.not_recorded (hnEq ▸ hkEq ▸ hm)

theorem Candidates.Steps.epoch_mono {before after : St P} {txs : List (Tx P)}
    (h : Steps before txs after) : before.currentEpoch ≤ after.currentEpoch := by
  induction h with
  | nil _ => exact Nat.le_refl _
  | cons hs _ ih => exact hs.epoch_mono.trans ih

theorem Candidates.Steps.frozen_preserved {before after : St P} {txs : List (Tx P)}
    (h : Steps before txs after) {e : Nat} (he : e < before.currentEpoch) :
    after.frozen e = before.frozen e := by
  induction h with
  | nil _ => rfl
  | cons hs _ ih =>
      exact (ih (Nat.lt_of_lt_of_le he hs.epoch_mono)).trans (hs.frozen_preserved he)

theorem frozenRootImmutability_proof (P : PrimSpec) : frozenRootImmutability P := by
  intro sup before after suffix _ hs
  constructor
  · calc
      after.frozen before.currentEpoch = before.rollover.frozen before.currentEpoch :=
        hs.frozen_preserved (Nat.lt_succ_self _)
      _ = before.active := if_pos rfl
  · intro e he
    calc
      after.frozen e = before.rollover.frozen e :=
        hs.frozen_preserved (Nat.lt_trans he (Nat.lt_succ_self _))
      _ = before.frozen e := if_neg (Nat.ne_of_lt he)

theorem AppendFresh.append {before xs ys : List P.Nullifier}
    (hx : AppendFresh (P := P) before xs)
    (hy : AppendFresh (P := P) (before ++ xs) ys) :
    AppendFresh (P := P) before (xs ++ ys) := by
  induction xs generalizing before with
  | nil => simpa only [List.append_nil, List.nil_append] using hy
  | cons x xs ih =>
      refine ⟨hx.1, ih hx.2 ?_⟩
      simpa only [List.append_assoc, List.singleton_append] using hy

theorem InsertionFacts.trans {before middle after xs ys : List P.Nullifier}
    (hx : InsertionFacts (P := P) before xs middle)
    (hy : InsertionFacts (P := P) middle ys after) :
    InsertionFacts (P := P) before (xs ++ ys) after := by
  obtain ⟨hx, rfl⟩ := hx
  exact ⟨hx.append hy.1, hy.2.trans (List.append_assoc _ _ _)⟩

theorem Step.canonical_append {before after : St P} {tx : Tx P}
    (hs : Step before tx after) (hne : tx ≠ .rollover) :
    after.currentEpoch = before.currentEpoch ∧
    InsertionFacts (P := P) before.active (tx.spends before.currentEpoch) after.active := by
  cases hs with
  | deposit _ => exact ⟨rfl, trivial, (List.append_nil _).symm⟩
  | transfer hg => exact ⟨rfl, hg.2.2.2.2.2.2.2.1⟩
  | withdraw hg => exact ⟨rfl, hg.2.2.2.1.2⟩
  | rollover => exact False.elim (hne rfl)

theorem canonicalAppend_proof (P : PrimSpec) : canonicalAppend P := by
  refine ⟨fun _ _ _ hs hne => hs.canonical_append hne, ?_⟩
  intro before after txs hs
  induction hs with
  | nil st => intro _; exact ⟨trivial, (List.append_nil _).symm⟩
  | @cons before middle after tx txs hs ht ih =>
      intro he
      have hm : middle.currentEpoch = before.currentEpoch := by
        have h1 := hs.epoch_mono
        have h2 := ht.epoch_mono
        omega
      have hn : tx ≠ .rollover := by
        intro hx
        subst tx
        cases hs
        change before.currentEpoch + 1 = before.currentEpoch at hm
        omega
      have hfirst := (hs.canonical_append hn).2
      have hrest := ih (he.trans hm.symm)
      rw [hm] at hrest
      exact hfirst.trans hrest

theorem Step.input_owned {before after : St P} {tx : Tx P}
    (hs : Step before tx after) {input : Note P × P.SpendKey}
    (hi : input ∈ inputs tx) : input.1.ownedBy input.2 := by
  cases hs with
  | deposit _ => exact False.elim (List.not_mem_nil hi)
  | rollover => exact False.elim (List.not_mem_nil hi)
  | transfer hg =>
      simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hg.2.1
      · exact hg.2.2.1
  | withdraw hg =>
      simp only [inputs, List.mem_singleton] at hi
      subst input
      exact hg.2.2.1

theorem Run.input_owned {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) {tx : Tx P} (ht : tx ∈ txs)
    {input : Note P × P.SpendKey} (hi : input ∈ inputs tx) :
    input.1.ownedBy input.2 := by
  induction hr with
  | empty => exact False.elim (List.not_mem_nil ht)
  | step _ hs ih =>
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact ih ht
      · exact hs.input_owned hi

theorem input_mem_notes {tx : Tx P} {input : Note P × P.SpendKey}
    (hi : input ∈ inputs tx) : input.1 ∈ notes tx := by
  cases tx <;>
    simp only [inputs, notes, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
  · rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact congrArg Prod.fst hi

theorem chainKeyBinding_proof (P : PrimSpec) : chainKeyBinding P := by
  intro sup txs st hr hcrypto n hn hc
  obtain ⟨w, hw, key, hk, hcm, ho, _⟩ := hr.consumed_recorded hc
  have hwEq := hcrypto.commit_inj w hw n hn hcm
  subst w
  refine ⟨key, hk, ho, ?_⟩
  intro tx ht input hi heq
  have hiNotes : input.1 ∈ Candidates.runNotes txs :=
    List.mem_flatMap.mpr ⟨tx, ht, input_mem_notes hi⟩
  have hiKeys : input.2 ∈ Candidates.runKeys txs :=
    List.mem_map.mpr ⟨input, List.mem_flatMap.mpr ⟨tx, ht, hi⟩, rfl⟩
  have hnEq := hcrypto.commit_inj input.1 hiNotes n hn heq
  have howned := hr.input_owned ht hi
  have hpub : P.derivePub input.2 = P.derivePub key :=
    howned.trans ((congrArg (fun n : Note P => n.ownerPubkey) hnEq).trans ho.symm)
  have hkEq := hcrypto.derivePub_inj input.2 hiKeys key hk hpub
  refine ⟨hnEq, hkEq, ?_⟩
  intro e _ _
  rw [hnEq, hkEq]

end LeanShieldedPool.Epoch
