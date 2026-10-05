import LeanShieldedPool.Statements.L5

/-!
Simulation of a run without rollover in the parent pool at epoch zero.
The translation preserves witnesses, accounting, and the consumption log.
Nullifier lists agree by permutation because the parent prepends spend batches.
-/

namespace LeanShieldedPool.Epoch

open Candidates

variable {P : PrimSpec}

theorem Step.notes_zero {before after : St P} {tx : Tx P}
    (hs : Step before tx after) (he : before.currentEpoch = 0)
    (hne : tx ≠ .rollover) :
    after.currentEpoch = 0 ∧ ∀ n ∈ notes tx, n.epochCreated = 0 := by
  cases hs with
  | deposit hg =>
      refine ⟨he, ?_⟩
      intro n hn
      simp only [notes, List.mem_singleton] at hn
      subst n
      exact hg.2.2.2.2.trans he
  | transfer hg =>
      obtain ⟨_, _, _, _, _, hc1, hc2, _, _, _, _, _, _, _, _, _, _, _, _, ho1, ho2⟩ := hg
      refine ⟨he, ?_⟩
      intro n hn
      simp only [notes, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · have h := hc1.1; omega
      · have h := hc2.1; omega
      · exact ho1.trans he
      · exact ho2.trans he
  | withdraw hg =>
      refine ⟨he, ?_⟩
      intro n hn
      simp only [notes, List.mem_singleton] at hn
      subst n
      have h := hg.2.2.2.1.1.1
      omega
  | rollover => exact False.elim (hne rfl)

theorem Step.minted_zero {before after : St P} {tx : Tx P}
    (hs : Step before tx after)
    (hb : ∀ n ∈ before.minted, n.epochCreated = 0)
    (ht : ∀ n ∈ notes tx, n.epochCreated = 0) :
    ∀ n ∈ after.minted, n.epochCreated = 0 := by
  cases hs with
  | deposit _ =>
      intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hb n hn
      · exact ht n hn
  | transfer _ =>
      intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hb n hn
      · exact ht n (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn))
  | withdraw _ => exact hb
  | rollover => exact hb

theorem Run.zero_epoch {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) (hn : ∀ tx ∈ txs, tx ≠ .rollover) :
    st.currentEpoch = 0 ∧
    (∀ n ∈ Candidates.runNotes txs, n.epochCreated = 0) ∧
    (∀ n ∈ st.minted, n.epochCreated = 0) := by
  induction hr with
  | empty => exact ⟨rfl, fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h)⟩
  | @step txs st st' tx hr hs ih =>
      obtain ⟨he, hnotes, hm⟩ := ih (fun t ht => hn t (List.mem_append_left _ ht))
      obtain ⟨he', ht⟩ := hs.notes_zero he (hn tx (List.mem_append_right _ List.mem_cons_self))
      refine ⟨he', ?_, hs.minted_zero hm ht⟩
      intro n hm
      simp only [Candidates.runNotes, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append] at hm
      rcases hm with hm | hm
      · exact hnotes n hm
      · exact ht n hm

theorem baseNote_cm {n : Note P} (hn : n.epochCreated = 0) :
    (baseNote n).cm = n.cm := by
  change P.commitE n.token n.amount n.ownerPubkey n.salt 0 =
    P.commitE n.token n.amount n.ownerPubkey n.salt n.epochCreated
  rw [hn]

theorem baseNote_nf {n : Note P} (hn : n.epochCreated = 0) (key : P.SpendKey) :
    (baseNote n).nf key = n.nfE key 0 := by
  change P.nfE (baseNote n).cm key 0 = P.nfE n.cm key 0
  rw [baseNote_cm hn]

theorem BaseStateMatches.leaves {st : St P} {base : LeanShieldedPool.St (basePrim P)}
    (hm : BaseStateMatches st base) (hz : ∀ n ∈ st.minted, n.epochCreated = 0) :
    base.leaves = st.leaves := by
  change base.minted.map LeanShieldedPool.Note.cm = st.minted.map Note.cm
  rw [hm.2.2.1, List.map_map]
  exact List.map_congr_left (fun n hn => baseNote_cm (hz n hn))

/-- Translate one accepted step, retaining the parent's prepend convention. -/
theorem Step.base_simulation {st st' : St P} {tx : Tx P}
    (hs : Step st tx st') (hne : tx ≠ .rollover)
    {base : LeanShieldedPool.St (basePrim P)} (hm : BaseStateMatches st base)
    (hz : ∀ n ∈ st.minted, n.epochCreated = 0) :
    ∃ btx after, baseTxs tx = [btx] ∧
      LeanShieldedPool.Step base btx after ∧ BaseStateMatches st' after := by
  have hnotes := (hs.notes_zero hm.1 hne).2
  have hl := BaseStateMatches.leaves hm hz
  obtain ⟨he, hf, hmint, hspent, hwin, hperm, hbal, hsup, hdep, hwith⟩ := hm
  cases hs with
  | @deposit d hg =>
      have hn := hnotes d.note List.mem_cons_self
      let bd : LeanShieldedPool.DepositData (basePrim P) :=
        { note := baseNote d.note, funding := d.funding }
      refine ⟨.deposit bd, bd.post base, rfl, .deposit ?_, ?_⟩
      · change base.supported d.note.token ∧ d.note.amount ≠ 0 ∧
          U128 d.note.amount ∧ (baseNote d.note).cm ∉ base.leaves
        rw [hsup, hl, baseNote_cm hn]
        exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩
      · refine ⟨he, hf, ?_, hspent, ?_, hperm, ?_, hsup, ?_, hwith⟩
        · change base.minted ++ [baseNote d.note] = (st.minted ++ [d.note]).map baseNote
          simp only [hmint, List.map_append, List.map_cons, List.map_nil]
        · change LeanShieldedPool.St.pushWindow base.window (base.minted.length + 1) =
            LeanShieldedPool.St.pushWindow st.window (st.minted.length + 1)
          rw [hwin, hmint, List.length_map]
        · change bump base.balance d.note.token d.note.amount = bump st.balance d.note.token d.note.amount
          rw [hbal]
          rfl
        · change bump base.deposited d.note.token d.note.amount = bump st.deposited d.note.token d.note.amount
          rw [hdep]
          rfl
  | @transfer d hg =>
      have h1 := hnotes d.in1 List.mem_cons_self
      have h2 := hnotes d.in2 (List.mem_cons_of_mem _ List.mem_cons_self)
      have ho1 := hnotes d.out1
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have ho2 := hnotes d.out2
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      obtain ⟨hr, hk1, hk2, ht1, ht2, _, _, hins, htok1, htok2, htok3,
        hw1, hw2, hw3, hw4, hsum, hf1, hf2, hout, _, _⟩ := hg
      let bd : LeanShieldedPool.TransferData (basePrim P) :=
        { key := d.key, in1 := baseNote d.in1, in2 := baseNote d.in2,
          out1 := baseNote d.out1, out2 := baseNote d.out2, snapshot := d.snapshot }
      have hnf1 : bd.nf1 = d.in1.nfE d.key 0 := baseNote_nf h1 _
      have hnf2 : bd.nf2 = d.in2.nfE d.key 0 := baseNote_nf h2 _
      have fresh1 : bd.nf1 ∉ base.nullifiers := by
        rw [hnf1]
        intro h
        apply hins.1.1
        rw [he]
        exact hperm.mem_iff.mp h
      have fresh2 : bd.nf2 ∉ base.nullifiers := by
        rw [hnf2]
        intro h
        apply hins.1.2.1
        apply List.mem_append_left
        rw [he]
        exact hperm.mem_iff.mp h
      have distinct : bd.nf1 ≠ bd.nf2 := by
        rw [hnf1, hnf2]
        intro h
        apply hins.1.2.1
        apply List.mem_append_right
        simp only [List.mem_singleton, he]
        exact h.symm
      refine ⟨.transfer bd, bd.post base, rfl, .transfer ?_, ?_⟩
      · change base.rootInWindow d.snapshot ∧ (baseNote d.in1).ownedBy d.key ∧
          (baseNote d.in2).ownedBy d.key ∧
          base.inTreeAt d.snapshot (baseNote d.in1).cm ∧
          ((baseNote d.in2).isBallast ∨ base.inTreeAt d.snapshot (baseNote d.in2).cm) ∧ _
        refine ⟨?_, hk1, hk2, ?_, ?_, fresh1, fresh2, distinct,
          htok1, htok2, htok3, hw1, hw2, hw3, hw4, hsum, ?_, ?_, ?_⟩
        · simpa only [LeanShieldedPool.St.rootInWindow, St.rootInWindow, hwin] using hr
        · change (baseNote d.in1).cm ∈ base.leaves.take d.snapshot
          rw [hl, baseNote_cm h1]
          exact ht1
        · change d.in2.isBallast ∨ (baseNote d.in2).cm ∈ base.leaves.take d.snapshot
          rw [hl, baseNote_cm h2]
          exact ht2
        · change (baseNote d.out1).cm ∉ base.leaves
          rw [hl, baseNote_cm ho1]; exact hf1
        · change (baseNote d.out2).cm ∉ base.leaves
          rw [hl, baseNote_cm ho2]; exact hf2
        · change (baseNote d.out1).cm ≠ (baseNote d.out2).cm
          rw [baseNote_cm ho1, baseNote_cm ho2]; exact hout
      · change st.currentEpoch = 0 ∧ (∀ e, st.frozen e = []) ∧
          base.minted ++ [baseNote d.out1, baseNote d.out2] =
            (st.minted ++ [d.out1, d.out2]).map baseNote ∧
          (baseNote d.in1).cm :: (baseNote d.in2).cm :: base.spentCms =
            d.in1.cm :: d.in2.cm :: st.spentCms ∧
          LeanShieldedPool.St.pushWindow base.window (base.minted.length + 2) =
            LeanShieldedPool.St.pushWindow st.window (st.minted.length + 2) ∧
          (bd.nf1 :: bd.nf2 :: base.nullifiers).Perm (st.active ++ d.nullifiers st.currentEpoch) ∧
          base.balance = st.balance ∧ base.supported = st.supported ∧
          base.deposited = st.deposited ∧ base.withdrawn = st.withdrawn
        refine ⟨he, hf, ?_, ?_, ?_, ?_, hbal, hsup, hdep, hwith⟩
        · simp only [List.map_append, List.map_cons, List.map_nil, hmint]
        · rw [baseNote_cm h1, baseNote_cm h2, hspent]
          rfl
        · rw [hwin, hmint, List.length_map]
        · rw [hnf1, hnf2, he]
          exact (hperm.cons _ |>.cons _).trans (List.perm_append_comm (l₁ := d.nullifiers 0) (l₂ := st.active))
  | @withdraw d hg =>
      have hn := hnotes d.note List.mem_cons_self
      let bd : LeanShieldedPool.WithdrawData (basePrim P) :=
        { key := d.key, note := baseNote d.note, recipient := d.recipient, snapshot := d.snapshot }
      have hnf : bd.nf = d.note.nfE d.key 0 := baseNote_nf hn _
      refine ⟨.withdraw bd, bd.post base, rfl, .withdraw ?_, ?_⟩
      · change base.rootInWindow d.snapshot ∧ base.inTreeAt d.snapshot (baseNote d.note).cm ∧
          (baseNote d.note).ownedBy d.key ∧ bd.nf ∉ base.nullifiers ∧
          d.note.amount ≠ 0 ∧ U128 d.note.amount ∧ d.note.amount ≤ base.balance d.note.token
        refine ⟨?_, ?_, hg.2.2.1, ?_, hg.2.2.2.2.1, hg.2.2.2.2.2.1, ?_⟩
        · simpa only [LeanShieldedPool.St.rootInWindow, St.rootInWindow, hwin] using hg.1
        · change (baseNote d.note).cm ∈ base.leaves.take d.snapshot
          rw [hl, baseNote_cm hn]
          exact hg.2.1
        · rw [hnf]
          intro h
          apply hg.2.2.2.1.2.1.1
          rw [he]
          exact hperm.mem_iff.mp h
        · rw [hbal]; exact hg.2.2.2.2.2.2
      · change st.currentEpoch = 0 ∧ (∀ e, st.frozen e = []) ∧
          base.minted = st.minted.map baseNote ∧
          (baseNote d.note).cm :: base.spentCms = d.note.cm :: st.spentCms ∧
          base.window = st.window ∧
          (bd.nf :: base.nullifiers).Perm (st.active ++ [d.nf st.currentEpoch]) ∧ _
        refine ⟨he, hf, hmint, ?_, hwin, ?_, ?_, hsup, hdep, ?_⟩
        · rw [baseNote_cm hn, hspent]
          rfl
        · rw [hnf, he]
          exact (hperm.cons _).trans (List.perm_append_comm (l₁ := [d.nf 0]) (l₂ := st.active))
        · change drop base.balance d.note.token d.note.amount = drop st.balance d.note.token d.note.amount
          rw [hbal]
          rfl
        · change bump base.withdrawn d.note.token d.note.amount = bump st.withdrawn d.note.token d.note.amount
          rw [hwith]
          rfl
  | rollover => exact False.elim (hne rfl)

theorem Run.base_simulation {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) (hn : ∀ tx ∈ txs, tx ≠ .rollover) :
    ∃ base, LeanShieldedPool.Run (P := basePrim P) sup (txs.flatMap baseTxs) base ∧ BaseStateMatches st base := by
  induction hr with
  | empty =>
      exact ⟨LeanShieldedPool.St.empty (basePrim P) sup, .empty,
        rfl, fun _ => rfl, rfl, rfl, rfl, List.Perm.refl _, rfl, rfl, rfl, rfl⟩
  | @step txs st st' tx hr hs ih =>
      have hp := fun t ht => hn t (List.mem_append_left [tx] ht)
      obtain ⟨base, hb, hm⟩ := ih hp
      obtain ⟨btx, after, ht, hs', hm'⟩ := hs.base_simulation
        (hn tx (List.mem_append_right _ List.mem_cons_self)) hm (hr.zero_epoch hp).2.2
      refine ⟨after, ?_, hm'⟩
      simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, ht] using LeanShieldedPool.Run.step hb hs'

theorem baseTxs_notes (tx : Tx P) :
    (baseTxs tx).flatMap LeanShieldedPool.Tx.notes = (notes tx).map baseNote := by
  cases tx <;> rfl

theorem base_runNotes (txs : List (Tx P)) :
    LeanShieldedPool.runNotes (txs.flatMap baseTxs) =
      (Candidates.runNotes txs).map baseNote := by
  simp only [LeanShieldedPool.runNotes, Candidates.runNotes, List.flatMap_assoc,
    List.map_flatMap, baseTxs_notes]

theorem baseTxs_keys {tx : Tx P} {key : P.SpendKey}
    (hk : key ∈ (baseTxs tx).flatMap LeanShieldedPool.Tx.keys) :
    key ∈ (inputs tx).map Prod.snd := by
  cases tx with
  | deposit _ => exact False.elim (List.not_mem_nil hk)
  | rollover => exact False.elim (List.not_mem_nil hk)
  | transfer d => exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hk))
  | withdraw _ => exact hk

theorem base_runKeys {txs : List (Tx P)} {key : P.SpendKey}
    (hk : key ∈ LeanShieldedPool.runKeys (txs.flatMap baseTxs)) :
    key ∈ Candidates.runKeys txs := by
  rw [LeanShieldedPool.runKeys, List.flatMap_assoc] at hk
  obtain ⟨tx, ht, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨input, hi, heq⟩ := List.mem_map.mp (baseTxs_keys hk)
  exact List.mem_map.mpr ⟨input, List.mem_flatMap.mpr ⟨tx, ht, hi⟩, heq⟩

theorem base_crypto {txs : List (Tx P)}
    (hc : Candidates.CryptoHyp P txs)
    (hz : ∀ n ∈ Candidates.runNotes txs, n.epochCreated = 0) :
    LeanShieldedPool.CryptoHyp (basePrim P) (txs.flatMap baseTxs) := by
  constructor
  · intro n hn n' hn' _ _ heq
    rw [base_runNotes] at hn hn'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hn'
    rw [baseNote_cm (hz w hw), baseNote_cm (hz w' hw')] at heq
    exact congrArg baseNote (hc.commit_inj w hw w' hw' heq)
  · intro k hk k' hk' heq
    exact hc.derivePub_inj k (base_runKeys hk) k' (base_runKeys hk') heq

theorem baseTxs_consumes {tx : Tx P} (hz : ∀ n ∈ notes tx, n.epochCreated = 0) :
    (baseTxs tx).flatMap LeanShieldedPool.Tx.consumes = tx.consumes := by
  cases tx with
  | deposit _ => rfl
  | rollover => rfl
  | transfer d =>
      have h1 := hz d.in1 List.mem_cons_self
      have h2 := hz d.in2 (List.mem_cons_of_mem _ List.mem_cons_self)
      change [(baseNote d.in1).cm, (baseNote d.in2).cm] = [d.in1.cm, d.in2.cm]
      rw [baseNote_cm h1, baseNote_cm h2]
      rfl
  | withdraw d =>
      change [(baseNote d.note).cm] = [d.note.cm]
      rw [baseNote_cm (hz d.note List.mem_cons_self)]
      rfl

theorem base_consumes {txs : List (Tx P)}
    (hz : ∀ n ∈ Candidates.runNotes txs, n.epochCreated = 0) :
    (txs.flatMap baseTxs).flatMap LeanShieldedPool.Tx.consumes = txs.flatMap Tx.consumes := by
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro tx ht
  exact baseTxs_consumes (fun n hn => hz n (List.mem_flatMap.mpr ⟨tx, ht, hn⟩))

theorem baseCaseSoundness_proof (P : PrimSpec) : baseCaseSoundness P := by
  intro sup txs st hr hn hc
  obtain ⟨base, hb, hm⟩ := hr.base_simulation hn
  have hz := (hr.zero_epoch hn).2.1
  have hcrypto := base_crypto hc hz
  have hconsumes := base_consumes hz
  refine ⟨⟨base, hb, hm, hcrypto, hconsumes⟩, ?_⟩
  intro hl3
  have hnodup := hl3 sup (txs.flatMap baseTxs) base hb hcrypto
  change ((txs.flatMap baseTxs).flatMap LeanShieldedPool.Tx.consumes).Nodup at hnodup
  rw [hconsumes] at hnodup
  exact hnodup

end LeanShieldedPool.Epoch
