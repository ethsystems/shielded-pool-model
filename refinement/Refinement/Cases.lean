import Refinement.Compose
import LeanShieldedPool.Proofs.NoDoubleSpend
import LeanShieldedPool.Proofs.TierAConditional

/-!
# The transfer and withdraw cases, the withdraw balance lemma, and `refine_run`

`refine_run` composes every case by induction over accepted histories, failed calls included.
All contract premises are used only on reachable states of the pinned deployment. A2 enters as
the per-history `ExtractedWitnesses`; `extractedWitnesses_of_ideal` derives it from the global
idealised form and the `verified` post fields, through `reach_verifier`. The token-binding lemmas
tie each deposit's and withdraw's token call to the extracted witness.
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

theorem windowRoots_append_of_le' (H : Nat → Nat → Nat) {L : List Nat} (M : List Nat)
    {w : List Nat} (hw : ∀ n ∈ w, n ≤ L.length) : windowRoots H (L ++ M) w = windowRoots H L w := by
  unfold windowRoots
  apply List.map_congr_left
  intro n hn
  rw [List.take_append_of_le_length (hw n hn)]

/-- **Record step.** After any storage change that inserts the leaves `M` (tree, `leaves`
mapping, `nullifiers` as the new model state says) and leaves the ring and supported map alone,
one `_recordRoot` restores `Rep` for the model state whose window pushed the new count. -/
theorem record_rep {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop}
    {L M : List Nat} {σ σ₁ : Storage} {st st' : St P} (hR : Rep H E sup L σ st)
    (hleaves : st'.leaves.map E.cm = L ++ M)
    (htree : σ₁.imt = imtOf H (L ++ M))
    (hli : ∀ w, σ₁.leafIndex w ≠ 0 ↔ w ∈ L ++ M)
    (hnul : ∀ w, σ₁.nullifiers w = true ↔ w ∈ st'.nullifiers.map E.nf)
    (hsup : σ₁.supportedTokens = σ.supportedTokens) (hsupp : st'.supported = st.supported)
    (hring : σ₁.ring = σ.ring) (hri : σ₁.ringIndex = σ.ringIndex)
    (hval : σ₁.validRoots = σ.validRoots)
    (hwin : st'.window = St.pushWindow st.window (L ++ M).length)
    (hZ : rootOf H (L ++ M) ≠ 0) :
    Rep H E sup (L ++ M) σ₁.recordRoot st' := by
  have hi := hR.ringIndex_lt
  have hcur : σ₁.currentRoot = rootOf H (L ++ M) := by
    show σ₁.imt.root = (imtOf H (L ++ M)).root
    rw [htree]
  exact {
    leaves := hleaves
    tree := htree
    leafIndex := hli
    nullifiers := hnul
    supported := fun t ht => hR.supported t (by rw [← hsup]; exact ht)
    supported_eq := hsupp.trans hR.supported_eq
    ringIndex_lt := Nat.mod_lt _ (by omega)
    ring := fun j hj => by
      show Function.update σ₁.ring σ₁.ringIndex σ₁.currentRoot
          (((σ₁.ringIndex + 1) % 100 + 99 - j) % 100) = (windowRoots H (L ++ M) st'.window).getD j 0
      rw [hwin, hring, hri]
      unfold St.pushWindow rootWindow
      rw [windowRoots_getD_take H _ _ j hj]
      rcases j with _ | k
      · have hp : ((σ.ringIndex + 1) % 100 + 99 - 0) % 100 = σ.ringIndex := by omega
        rw [hp, Function.update_self, hcur]
        show rootOf H (L ++ M) = rootOf H ((L ++ M).take (L ++ M).length)
        rw [List.take_of_length_le (Nat.le_refl _)]
      · have hp : ((σ.ringIndex + 1) % 100 + 99 - (k + 1)) % 100 =
            (σ.ringIndex + 99 - k) % 100 := by omega
        have hne : (σ.ringIndex + 99 - k) % 100 ≠ σ.ringIndex := by omega
        rw [hp, Function.update_of_ne hne]
        show ringAt σ k = (windowRoots H (L ++ M) st.window).getD k 0
        rw [windowRoots_append_of_le' H M hR.window_le]
        exact hR.ring k (by omega)
    head := by
      rw [hwin]
      rfl
    window_le := fun n hn => by
      rw [hwin] at hn
      have hn' : n ∈ (L ++ M).length :: st.window := List.mem_of_mem_take hn
      rcases List.mem_cons.1 hn' with rfl | h'
      · exact Nat.le_refl _
      · rw [List.length_append]
        exact Nat.le_add_right_of_le (hR.window_le n h')
    valid := fun r hr => by
      have hr' : (if r = σ₁.currentRoot then true
          else if σ₁.ring σ₁.ringIndex ≠ 0 ∧ r = σ₁.ring σ₁.ringIndex then false
          else σ₁.validRoots r) = true := hr
      rw [hring, hri, hval] at hr'
      by_cases h1 : r = σ₁.currentRoot
      · refine ⟨?_, σ₁.ringIndex, by rw [hri]; exact hi, ?_⟩
        · rw [h1, hcur]
          exact hZ
        · show Function.update σ₁.ring σ₁.ringIndex σ₁.currentRoot σ₁.ringIndex = r
          rw [Function.update_self, h1]
      · rw [if_neg h1] at hr'
        by_cases h2 : σ.ring σ.ringIndex ≠ 0 ∧ r = σ.ring σ.ringIndex
        · rw [if_pos h2] at hr'
          exact absurd hr' Bool.false_ne_true
        · rw [if_neg h2] at hr'
          obtain ⟨hr0, p, hp, hpr⟩ := hR.valid r hr'
          refine ⟨hr0, p, hp, ?_⟩
          have hpi : p ≠ σ.ringIndex := by
            rintro rfl
            exact h2 ⟨by rw [hpr]; exact hr0, hpr.symm⟩
          show Function.update σ₁.ring σ₁.ringIndex σ₁.currentRoot p = r
          rw [hring, hri, Function.update_of_ne hpi, hpr] }

/-- A model commitment whose word is in a window prefix of the leaves is in the model tree at
that snapshot. Uses injective commitment encoding. -/
theorem inTree_of_mem {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop} {L : List Nat}
    {σ : Storage} {st : St P} (hR : Rep H E sup L σ st) (hinj : Function.Injective E.cm)
    {n : Nat} {c : P.Commitment} (hm : E.cm c ∈ L.take n) : st.inTreeAt n c := by
  rw [← hR.leaves, ← List.map_take] at hm
  obtain ⟨c', hc', he⟩ := List.mem_map.1 hm
  rw [hinj he] at hc'
  exact hc'

/-- **Transfer case of the induction.** From the extracted witness, `CircuitFacts`, the tree
membership for this call's extracted input words, and the contract facts of `TransferPost` on a
reachable state. -/
theorem transfer_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
    {Incl : Nat → Nat → Prop} {sup : P.Token → Prop} (hC : CircuitFacts E C Incl)
    (hinj : Function.Injective E.cm)
    {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {n0 n1 c0 c1 root pay : Nat}
    (hd : (Call.transfer n0 n1 c0 c1 root pay).extractOK C ext)
    (hmemb : ∀ L w, L <+: ghostLeaves h →
      w ∈ inputWords E ext (h ++ [.transfer n0 n1 c0 c1 root pay]) → Incl w (rootOf H L) → w ∈ L)
    (hdist : n0 ≠ n1) (hun : σ.nullifiers n0 = false ∧ σ.nullifiers n1 = false)
    (hkr : σ.isKnownRoot root) (hfo : σ.leafIndex c0 = 0 ∧ σ.leafIndex c1 = 0 ∧ c0 ≠ c1)
    (hpost : σ' = transferStorage H σ n0 n1 c0 c1)
    (hz : rootOf H (ghostLeaves (h ++ [.transfer n0 n1 c0 c1 root pay])) ≠ 0)
    (hI : Inv H E ext sup h σ txs st) :
    ∃ txs' st', Inv H E ext sup (h ++ [.transfer n0 n1 c0 c1 root pay]) σ' txs' st' := by
  let d := ext.transfer [n0, n1, c0, c1, root, pay]
  have hd' : C.transfer [n0, n1, c0, c1, root, pay] d := hd
  obtain ⟨ho1, ho2⟩ := hC.t_owner _ _ hd'
  obtain ⟨hm1, hm2⟩ := hC.t_member _ _ hd'
  obtain ⟨hn0, hn1⟩ := hC.t_nullifiers _ _ hd'
  obtain ⟨htk1, htk2, htk3⟩ := hC.t_tokens _ _ hd'
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hC.t_ranges _ _ hd'
  have hcons := hC.t_conservation _ _ hd'
  obtain ⟨hc0, hc1⟩ := hC.t_outputs _ _ hd'
  have en0 : n0 = E.nf d.nf1 := hn0
  have en1 : n1 = E.nf d.nf2 := hn1
  have ec0 : c0 = E.cm d.out1.cm := hc0
  have ec1 : c1 = E.cm d.out2.cm := hc1
  have hm1' : Incl (E.cm d.in1.cm) root := hm1
  have hm2' : d.in2.isBallast ∨ Incl (E.cm d.in2.cm) root := hm2
  have hG : ghostLeaves (h ++ [.transfer n0 n1 c0 c1 root pay]) = ghostLeaves h ++ [c0, c1] :=
    ghostLeaves_snoc _ _
  by_cases hcr0 : CryptoHyp P txs
  swap
  · refine ⟨txs ++ [.transfer d], st, ?_, fun hcr => absurd (CryptoHyp.of_snoc hcr) hcr0⟩
    rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  obtain ⟨hrun, hR⟩ := hI.2 hcr0
  obtain ⟨n, hnw, hroot⟩ := hR.known_root_in_window hkr
  have hmem : ∀ nt : Note P, nt.cm ∈ (eraseSnap (Tx.transfer d)).consumes →
      Incl (E.cm nt.cm) root → st.inTreeAt n nt.cm := by
    intro nt hnt hi
    have hi' : Incl (E.cm nt.cm) (rootOf H ((ghostLeaves h).take n)) := hroot ▸ hi
    have hw : E.cm nt.cm ∈ inputWords E ext (h ++ [.transfer n0 n1 c0 c1 root pay]) :=
      mem_inputWords_snoc (List.mem_singleton_self _) hnt
    exact inTree_of_mem hR hinj (hmemb _ _ (List.take_prefix _ _) hw hi')
  have hin1 : d.in1.cm ∈ (eraseSnap (Tx.transfer d)).consumes := List.mem_cons_self
  have hin2 : d.in2.cm ∈ (eraseSnap (Tx.transfer d)).consumes :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have fresh1 : d.nf1 ∉ st.nullifiers := by
    intro hm
    have h1 := (hR.nullifiers n0).2 (by rw [en0]; exact List.mem_map.2 ⟨_, hm, rfl⟩)
    rw [hun.1] at h1
    exact Bool.false_ne_true h1
  have fresh2 : d.nf2 ∉ st.nullifiers := by
    intro hm
    have h1 := (hR.nullifiers n1).2 (by rw [en1]; exact List.mem_map.2 ⟨_, hm, rfl⟩)
    rw [hun.2] at h1
    exact Bool.false_ne_true h1
  have hne : d.nf1 ≠ d.nf2 := fun he => hdist (by rw [en0, en1, he])
  have out1 : d.out1.cm ∉ st.leaves := fun hm =>
    (hR.leafIndex c0).2 (by rw [ec0, ← hR.leaves]; exact List.mem_map.2 ⟨_, hm, rfl⟩) hfo.1
  have out2 : d.out2.cm ∉ st.leaves := fun hm =>
    (hR.leafIndex c1).2 (by rw [ec1, ← hR.leaves]; exact List.mem_map.2 ⟨_, hm, rfl⟩) hfo.2.1
  have outne : d.out1.cm ≠ d.out2.cm := fun he => hfo.2.2 (by rw [ec0, ec1, he])
  let d' : TransferData P := { d with snapshot := n }
  have hguard : d'.guard st :=
    ⟨hnw, ho1, ho2, hmem _ hin1 hm1', hm2'.imp_right (hmem _ hin2), fresh1, fresh2,
      hne, htk1, htk2, htk3, hr1, hr2, hr3, hr4, hcons, out1, out2, outne⟩
  refine ⟨txs ++ [.transfer d'], d'.post st, ?_, fun _ => ⟨Run.step hrun (Step.transfer hguard), ?_⟩⟩
  · rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  have hlen : st.minted.length = (ghostLeaves h).length := by
    rw [← hR.leaves]
    simp only [St.leaves, List.length_map]
  rw [hG] at hz
  rw [hG, hpost]
  show Rep H E sup (ghostLeaves h ++ [c0, c1])
    ((((σ.markSpent n0).markSpent n1).insertLeaf H c0).insertLeaf H c1).recordRoot (d'.post st)
  refine record_rep hR ?_ ?_ ?_ ?_ rfl rfl rfl rfl rfl ?_ hz
  · show ((st.minted ++ [d.out1, d.out2]).map Note.cm).map E.cm = ghostLeaves h ++ [c0, c1]
    rw [← hR.leaves, ec0, ec1]
    simp only [St.leaves, List.map_append, List.map_cons, List.map_nil]
  · show imtInsert H (imtInsert H σ.imt c0) c1 = imtOf H (ghostLeaves h ++ [c0, c1])
    rw [show ghostLeaves h ++ [c0, c1] = (ghostLeaves h ++ [c0]) ++ [c1] by
      simp only [List.append_assoc, List.cons_append, List.nil_append],
      imtOf_append, imtOf_append, hR.tree]
  · intro w
    show Function.update (Function.update σ.leafIndex c0 (σ.size + 1)) c1
        ((imtInsert H σ.imt c0).size + 1) w ≠ 0 ↔ w ∈ ghostLeaves h ++ [c0, c1]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    by_cases hw1 : w = c1
    · rw [hw1, Function.update_self]
      exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => Nat.succ_ne_zero _⟩
    · rw [Function.update_of_ne hw1]
      by_cases hw0 : w = c0
      · rw [hw0, Function.update_self]
        exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => Nat.succ_ne_zero _⟩
      · rw [Function.update_of_ne hw0, hR.leafIndex w]
        exact ⟨Or.inl, fun h' => (h'.resolve_right (fun h'' => h''.elim hw0 hw1))⟩
  · intro w
    show Function.update (Function.update σ.nullifiers n0 true) n1 true w = true ↔
      w ∈ (d.nf1 :: d.nf2 :: st.nullifiers).map E.nf
    simp only [List.map_cons, List.mem_cons]
    by_cases hw1 : w = n1
    · rw [hw1, Function.update_self, en1]
      exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => rfl⟩
    · rw [Function.update_of_ne hw1]
      by_cases hw0 : w = n0
      · rw [hw0, Function.update_self, en0]
        exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
      · rw [Function.update_of_ne hw0, hR.nullifiers w, ← en0, ← en1]
        exact ⟨fun h' => Or.inr (Or.inr h'),
          fun h' => (h'.resolve_left hw0).resolve_left hw1⟩
  · show St.pushWindow st.window (st.minted.length + 2) =
      St.pushWindow st.window (ghostLeaves h ++ [c0, c1]).length
    rw [hlen, List.length_append]
    rfl

theorem nat_le_sum_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left_of_le (ih h')

/-- **Withdraw balance, W9 redundancy (model only).** In a run whose extension by the withdraw satisfies
`CryptoHyp`, a well-formed note that is in the tree, owned by the withdraw key and has a fresh
nullifier is minted and unspent, so the pool balance covers it. `wf` is needed because
`CryptoHyp.commit_inj` covers only `wf` notes; the withdraw circuit supplies it (W8). Uses
`balanceIsLiveValue_proof` (`poolSolvency` and `valueConservation`). -/
theorem withdraw_balance {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) (d : WithdrawData P) (hc : CryptoHyp P (txs ++ [.withdraw d]))
    (hin : d.note.cm ∈ st.leaves) (ho : d.note.ownedBy d.key) (hf : st.fresh d.nf)
    (hwf : d.note.wf) :
    d.note.amount ≤ st.balance d.note.token := by
  have hn : runNotes txs ⊆ runNotes (txs ++ [.withdraw d]) := by
    simp only [runNotes, List.flatMap_append]
    exact List.subset_append_left _ _
  have hk : runKeys txs ⊆ runKeys (txs ++ [.withdraw d]) := by
    simp only [runKeys, List.flatMap_append]
    exact List.subset_append_left _ _
  have hdn : d.note ∈ runNotes (txs ++ [.withdraw d]) := by
    simp only [runNotes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append]
    exact Or.inr List.mem_cons_self
  have hdk : d.key ∈ runKeys (txs ++ [.withdraw d]) := by
    simp only [runKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append]
    exact Or.inr List.mem_cons_self
  obtain ⟨m, hm, hmc⟩ := List.mem_map.1 hin
  have hmd : m = d.note := hc.commit_inj m (hn (hr.minted_mem_runNotes hm)) d.note hdn
    (hr.runNotes_wf m (hr.minted_mem_runNotes hm)) hwf hmc
  rw [hmd] at hm
  have hns : ¬ st.spent d.note := by
    intro hsp
    obtain ⟨n', hn', k', hk', hcm', ho', hnf'⟩ := hr.spentCms_witness hsp
    have hnd : n' = d.note := hc.commit_inj n' (hn hn') d.note hdn (hr.runNotes_wf n' hn') hwf hcm'
    rw [hnd] at ho' hnf'
    have hkd : k' = d.key :=
      hc.derivePub_inj k' (hk hk') d.key hdk (ho'.trans ho.symm)
    rw [hkd] at hnf'
    exact hf hnf'
  rw [balanceIsLiveValue_proof P sup txs st hr (CryptoHyp.of_snoc hc) d.note.token]
  have hv : noteValue st d.note.token d.note = d.note.amount := by
    unfold noteValue
    rw [if_pos ⟨rfl, hns⟩]
  rw [← hv]
  exact nat_le_sum_of_mem (List.mem_map.2 ⟨d.note, hm, rfl⟩)

/-- **Withdraw case of the induction.** From the extracted witness, `CircuitFacts`, tree
membership, `withdraw_balance`, and the contract facts of `WithdrawPost` on a reachable state. -/
theorem withdraw_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
    {Incl : Nat → Nat → Prop} {sup : P.Token → Prop} (hC : CircuitFacts E C Incl)
    (hinj : Function.Injective E.cm)
    {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {nf tok amt rcpt root : Nat}
    (hd : (Call.withdraw nf tok amt rcpt root).extractOK C ext)
    (hmemb : ∀ L w, L <+: ghostLeaves h →
      w ∈ inputWords E ext (h ++ [.withdraw nf tok amt rcpt root]) → Incl w (rootOf H L) → w ∈ L)
    (hamt : amt ≠ 0) (hun : σ.nullifiers nf = false) (hkr : σ.isKnownRoot root)
    (hpost : σ' = withdrawStorage σ nf) (hI : Inv H E ext sup h σ txs st) :
    ∃ txs' st', Inv H E ext sup (h ++ [.withdraw nf tok amt rcpt root]) σ' txs' st' := by
  let d := ext.withdraw [nf, tok, amt, rcpt, root]
  have hd' : C.withdraw [nf, tok, amt, rcpt, root] d := hd
  have hm : Incl (E.cm d.note.cm) root := hC.w_member _ _ hd'
  have ho := hC.w_owner _ _ hd'
  have enf : nf = E.nf d.nf := hC.w_nullifier _ _ hd'
  have ea : amt = d.note.amount := (hC.w_public _ _ hd').2
  have hu := hC.w_amount _ _ hd'
  have hG : ghostLeaves (h ++ [.withdraw nf tok amt rcpt root]) = ghostLeaves h :=
    ghostLeaves_snoc_nil _ _ rfl
  by_cases hcr0 : CryptoHyp P txs
  swap
  · refine ⟨txs ++ [.withdraw d], st, ?_, fun hcr => absurd (CryptoHyp.of_snoc hcr) hcr0⟩
    rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  obtain ⟨hrun, hR⟩ := hI.2 hcr0
  obtain ⟨n, hnw, hroot⟩ := hR.known_root_in_window hkr
  have hmem : st.inTreeAt n d.note.cm := by
    have hi' : Incl (E.cm d.note.cm) (rootOf H ((ghostLeaves h).take n)) := hroot ▸ hm
    have hnt : d.note.cm ∈ (eraseSnap (Tx.withdraw d)).consumes := List.mem_cons_self
    have hw : E.cm d.note.cm ∈ inputWords E ext (h ++ [.withdraw nf tok amt rcpt root]) :=
      mem_inputWords_snoc (List.mem_singleton_self _) hnt
    exact inTree_of_mem hR hinj (hmemb _ _ (List.take_prefix _ _) hw hi')
  have hfresh : d.nf ∉ st.nullifiers := by
    intro hmn
    have h1 := (hR.nullifiers nf).2 (by rw [enf]; exact List.mem_map.2 ⟨_, hmn, rfl⟩)
    rw [hun] at h1
    exact Bool.false_ne_true h1
  let d' : WithdrawData P := { d with snapshot := n }
  refine ⟨txs ++ [.withdraw d'], d'.post st, ?_, fun hcr => ?_⟩
  · rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  have hbal := withdraw_balance hrun d' hcr (List.mem_of_mem_take hmem) ho hfresh hu
  have hguard : d'.guard st :=
    ⟨hnw, hmem, ho, hfresh, by rw [← ea]; exact hamt, hu, hbal⟩
  refine ⟨Run.step hrun (Step.withdraw hguard), ?_⟩
  rw [hG, hpost]
  exact {
    leaves := hR.leaves
    tree := hR.tree
    leafIndex := hR.leafIndex
    nullifiers := fun w => by
      show Function.update σ.nullifiers nf true w = true ↔ w ∈ (d.nf :: st.nullifiers).map E.nf
      rw [List.map_cons, List.mem_cons]
      by_cases hw : w = nf
      · rw [hw, Function.update_self, enf]
        exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
      · rw [Function.update_of_ne hw, hR.nullifiers w, ← enf]
        exact ⟨Or.inr, fun h' => h'.resolve_left hw⟩
    supported := hR.supported
    supported_eq := hR.supported_eq
    ringIndex_lt := hR.ringIndex_lt
    ring := hR.ring
    head := hR.head
    window_le := hR.window_le
    valid := hR.valid }

/-- With the environment premise, the reentrancy guard leaves no nested call in the trace. -/
theorem no_nested {X : Contract} (hEnv : OwnerCallbackFree X) {σ σ' : Storage} {c : Call}
    {tr : List Ext} (hr : Reach X σ) (hx : X.Exec σ c tr σ')
    (hg : ∀ c', Ext.nested c' ∈ tr → c'.isOwner = true) : ∀ c', Ext.nested c' ∉ tr := by
  intro c' hc'
  have h1 := hEnv hr hx c' hc'
  rw [hg c' hc'] at h1
  cases h1

theorem no_nested_of_nil {tr : List Ext} (h : tr = []) : ∀ c', Ext.nested c' ∉ tr := by
  intro c' hc'
  rw [h] at hc'
  exact List.not_mem_nil hc'

/-- The induction behind `refine_run`, over every accepted prefix `h` of the final history
`hf`. All scoped premises are about `hf`. -/
theorem refine_inv {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {Incl : Nat → Nat → Prop} {Coll : List Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hinj : Function.Injective E.cm)
    {hf : List Call} (hC1 : NoSetVerifier hf) (hEx : ExtractedWitnesses C ext hf)
    (hTL : TreeLink H Incl Coll (ghostLeaves hf) (inputWords E ext hf))
    (hTH : TreeHyp Coll (ghostLeaves hf) (inputWords E ext hf)) (hZ : RootsNonzero H hf)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) :
    h <+: hf → ∃ txs st, Inv H E ext (supOf E hf) h σ txs st := by
  induction hacc with
  | nil =>
    intro _
    obtain ⟨reg, o, e⟩ := hG0
    refine ⟨[], St.empty P (supOf E hf), rfl, fun _ => ⟨Run.empty, ?_⟩⟩
    rw [e]
    exact rep_genesis H E (supOf E hf) X.pinnedVerifier reg o
  | @fail h0 σ0 σ1 c hacc0 hfl ih =>
    intro hp
    obtain ⟨txs, st, hI⟩ := ih hp
    have hreach : Reach X σ0 := ⟨h0, hacc0, fun c' hc' => hC1 c' (hp.subset hc')⟩
    obtain rfl := hRB hreach hfl
    exact ⟨txs, st, hI⟩
  | @snoc h0 σ0 σ1 c tr hacc0 hx ih =>
    intro hp
    have hp0 : h0 <+: hf := (List.prefix_append h0 [c]).trans hp
    obtain ⟨txs, st, hI⟩ := ih hp0
    have hcmem : c ∈ hf := hp.subset (List.mem_append_right _ (List.mem_singleton_self _))
    have hreach : Reach X σ0 := ⟨h0, hacc0, fun c' hc' => hC1 c' (hp0.subset hc')⟩
    have hmemb : ∀ L w, L <+: ghostLeaves h0 → w ∈ inputWords E ext (h0 ++ [c]) →
        Incl w (rootOf H L) → w ∈ L := fun L w hL hw hi =>
      tree_member hTL hTH (hL.trans (ghostLeaves_prefix hp0)) (inputWords_prefix hp hw) hi
    cases c with
    | deposit s cm tok amt fund att pay =>
      exact deposit_step hC (hEx _ hcmem) (hD.supported hreach hx) (hD.amount_ne_zero hreach hx)
        (hD.fresh_leaf hreach hx)
        (hD.post hreach hx (no_nested hEnv hreach hx (hD.guarded hreach hx)))
        (hZ.at hp (List.cons_ne_nil _ _)) hI
    | transfer n0 n1 c0 c1 root pay =>
      exact transfer_step hC hinj (hEx _ hcmem) hmemb (hTP.distinct hreach hx)
        (hTP.unspent hreach hx) (hTP.known_root hreach hx) (hTP.fresh_outputs hreach hx)
        (hTP.post hreach hx (no_nested_of_nil (hTP.no_effects hreach hx)))
        (hZ.at hp (List.cons_ne_nil _ _)) hI
    | withdraw nf tok amt rcpt root =>
      exact withdraw_step hC hinj (hEx _ hcmem) hmemb (hWP.amount_ne_zero hreach hx)
        (hWP.unspent hreach hx) (hWP.known_root hreach hx)
        (hWP.post hreach hx (no_nested hEnv hreach hx (hWP.guarded hreach hx))) hI
    | setVerifier v => exact absurd rfl (hC1 _ hcmem v)
    | addSupportedToken tok =>
      refine ⟨txs, st, stutter_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.add hreach hx]
      refine hR.frame rfl rfl rfl rfl rfl rfl (fun t ht => ?_)
      have ht' : Function.update σ0.supportedTokens tok true (E.tok t) = true := ht
      by_cases he : E.tok t = tok
      · show Call.addSupportedToken (E.tok t) ∈ hf
        rw [he]
        exact hcmem
      · rw [Function.update_of_ne he] at ht'
        exact hR.supported t ht'
    | removeSupportedToken tok =>
      refine ⟨txs, st, stutter_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.remove hreach hx]
      refine hR.frame rfl rfl rfl rfl rfl rfl (fun t ht => ?_)
      have ht' : Function.update σ0.supportedTokens tok false (E.tok t) = true := ht
      by_cases he : E.tok t = tok
      · rw [he, Function.update_self] at ht'
        exact absurd ht' Bool.false_ne_true
      · rw [Function.update_of_ne he] at ht'
        exact hR.supported t ht'
    | setAttestationRegistry reg =>
      refine ⟨txs, st, stutter_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.registry hreach hx]
      exact hR.frame rfl rfl rfl rfl rfl rfl hR.supported
    | transferOwnership o =>
      refine ⟨txs, st, stutter_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.owner hreach hx]
      exact hR.frame rfl rfl rfl rfl rfl rfl hR.supported

/-- **`refine_run`.** For every accepted history `h` of the pinned deployment
(reverted calls included, no successful `setVerifier` call), every extractor `ext`, and `sup`
the tokens `h` added: if the premises hold, the extracted operations `txsOf ext h` (up to the
model snapshots) form a model run from the empty pool to a state that `Rep` relates to the
storage.

Contract premises (universal over reachable states): `ConstructorPost`, `Rollback`,
`DepositPost`, `TransferPost`, `WithdrawPost`, `AdminStutter`. Environment:
`OwnerCallbackFree`. Circuit: `CircuitFacts`, encoding `hinj`. Per history: A2
`ExtractedWitnesses`, A9a and A9b `TreeLink` and `TreeHyp`, `RootsNonzero`, A1 `CryptoHyp`. This is a
conditional storage-to-model composition; token movement (A10), event correspondence and the
bounds of the existing checks stay outside it. -/
theorem refine_run {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {Incl : Nat → Nat → Prop} {Coll : List Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hinj : Function.Injective E.cm)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h)
    (hEx : ExtractedWitnesses C ext h)
    (hTL : TreeLink H Incl Coll (ghostLeaves h) (inputWords E ext h))
    (hTH : TreeHyp Coll (ghostLeaves h) (inputWords E ext h)) (hZ : RootsNonzero H h)
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ txs st, txs.map eraseSnap = txsOf ext h ∧
      Run (supOf E h) txs st ∧ Rep H E (supOf E h) (ghostLeaves h) σ st := by
  obtain ⟨txs, st, hE, hI⟩ :=
    refine_inv hG0 hRB hEnv hD hTP hWP hA hC hinj hC1 hEx hTL hTH hZ hacc (List.prefix_refl h)
  exact ⟨txs, st, hE, hI (cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr))⟩

/-- **Pinned verifier.** In every reachable state the stored verifier is the pinned one. -/
theorem reach_verifier {H : Nat → Nat → Nat} {X : Contract}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) :
    NoSetVerifier h → σ.verifier = X.pinnedVerifier := by
  induction hacc with
  | nil =>
    intro _
    obtain ⟨reg, o, e⟩ := hG0
    rw [e]
    rfl
  | @fail h0 σ0 σ1 c hacc0 hfl ih =>
    intro hC1
    rw [hRB ⟨h0, hacc0, hC1⟩ hfl]
    exact ih hC1
  | @snoc h0 σ0 σ1 c tr hacc0 hx ih =>
    intro hC1
    have hC0 : NoSetVerifier h0 := fun c' hc' => hC1 c' (List.mem_append_left _ hc')
    have hreach : Reach X σ0 := ⟨h0, hacc0, hC0⟩
    have iv := ih hC0
    cases c with
    | deposit s cm tok amt fund att pay =>
      rw [hD.post hreach hx (no_nested hEnv hreach hx (hD.guarded hreach hx))]
      exact iv
    | transfer n0 n1 c0 c1 root pay =>
      rw [hTP.post hreach hx (no_nested_of_nil (hTP.no_effects hreach hx))]
      exact iv
    | withdraw nf tok amt rcpt root =>
      rw [hWP.post hreach hx (no_nested hEnv hreach hx (hWP.guarded hreach hx))]
      exact iv
    | addSupportedToken tok =>
      rw [hA.add hreach hx]
      exact iv
    | removeSupportedToken tok =>
      rw [hA.remove hreach hx]
      exact iv
    | setAttestationRegistry reg =>
      rw [hA.registry hreach hx]
      exact iv
    | transferOwnership o =>
      rw [hA.owner hreach hx]
      exact iv
    | setVerifier v =>
      exact absurd rfl (hC1 _ (List.mem_append_right _ (List.mem_singleton_self _)) v)

/-- **A2 bridge.** The per-history witness property follows from global ideal extraction for
the pinned verifier and the `verified` post fields (S1, S2), through `reach_verifier`. -/
theorem extractedWitnesses_of_ideal {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P}
    {ext : Extractor P}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hI : IdealExtraction X C ext) {h : List Call} {σ : Storage} (hacc : Accepted X h σ) :
    NoSetVerifier h → ExtractedWitnesses C ext h := by
  induction hacc with
  | nil => intro _ c hc; exact (List.not_mem_nil hc).elim
  | @fail h0 σ0 σ1 c hacc0 hfl ih => exact ih
  | @snoc h0 σ0 σ1 c tr hacc0 hx ih =>
    intro hC1 c' hc'
    have hC0 : NoSetVerifier h0 := fun c'' hc'' => hC1 c'' (List.mem_append_left _ hc'')
    have hreach : Reach X σ0 := ⟨h0, hacc0, hC0⟩
    rcases List.mem_append.1 hc' with hold | hnew
    · exact ih hC0 c' hold
    · rw [List.mem_singleton.1 hnew]
      have hv := reach_verifier hG0 hRB hEnv hD hTP hWP hA hacc0 hC0
      cases c with
      | deposit s cm tok amt fund att pay =>
        obtain ⟨hver, hcan⟩ := hD.verified hreach hx
        rw [hv] at hver
        exact hI.deposit _ hver hcan
      | transfer n0 n1 c0 c1 root pay =>
        obtain ⟨hver, hcan⟩ := hTP.verified hreach hx
        rw [hv] at hver
        exact hI.transfer _ hver hcan
      | withdraw nf tok amt rcpt root =>
        obtain ⟨hver, hcan⟩ := hWP.verified hreach hx
        rw [hv] at hver
        exact hI.withdraw _ hver hcan
      | addSupportedToken tok => trivial
      | removeSupportedToken tok => trivial
      | setAttestationRegistry reg => trivial
      | transferOwnership o => trivial
      | setVerifier v => trivial

/-- **Deposit token binding (D6, X2).** A successful deposit on a reachable state makes exactly
one token call: `transferFrom` of the extracted note's token and amount, from the extracted
funding address, to the pool. -/
theorem deposit_token_binding {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {Incl : Nat → Nat → Prop} (hD : DepositPost H X)
    (hC : CircuitFacts E C Incl) {σ σ' : Storage} {s c tok amt fund att pay : Nat}
    {tr : List Ext} (hr : Reach X σ) (hx : X.Exec σ (.deposit s c tok amt fund att pay) tr σ')
    (hd : (Call.deposit s c tok amt fund att pay).extractOK C ext) :
    tokenCalls tr = [.transferFrom (E.tok (ext.deposit [c, tok, amt, fund, att, pay]).note.token)
      (E.addr (ext.deposit [c, tok, amt, fund, att, pay]).funding) X.self
      (ext.deposit [c, tok, amt, fund, att, pay]).note.amount] := by
  have hd' : C.deposit [c, tok, amt, fund, att, pay] (ext.deposit [c, tok, amt, fund, att, pay]) :=
    hd
  obtain ⟨_, h1, h2⟩ := hC.d_commitment _ _ hd'
  have ht : tok = E.tok (ext.deposit [c, tok, amt, fund, att, pay]).note.token := h1
  have ha : amt = (ext.deposit [c, tok, amt, fund, att, pay]).note.amount := h2
  have hf : fund = E.addr (ext.deposit [c, tok, amt, fund, att, pay]).funding :=
    hC.d_funding _ _ hd'
  rw [hD.token_calls hr hx, ← ht, ← ha, ← hf]

/-- **Withdraw token binding (W10).** A successful withdraw on a reachable state makes exactly
one token call: `transfer` of the extracted note's token and amount to the extracted
recipient. -/
theorem withdraw_token_binding {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {Incl : Nat → Nat → Prop} (hWP : WithdrawPost X)
    (hC : CircuitFacts E C Incl) {σ σ' : Storage} {nf tok amt rcpt root : Nat}
    {tr : List Ext} (hr : Reach X σ) (hx : X.Exec σ (.withdraw nf tok amt rcpt root) tr σ')
    (hd : (Call.withdraw nf tok amt rcpt root).extractOK C ext) :
    tokenCalls tr = [.transfer (E.tok (ext.withdraw [nf, tok, amt, rcpt, root]).note.token)
      (E.addr (ext.withdraw [nf, tok, amt, rcpt, root]).recipient)
      (ext.withdraw [nf, tok, amt, rcpt, root]).note.amount] := by
  have hd' : C.withdraw [nf, tok, amt, rcpt, root] (ext.withdraw [nf, tok, amt, rcpt, root]) := hd
  obtain ⟨h1, h2⟩ := hC.w_public _ _ hd'
  have ht : tok = E.tok (ext.withdraw [nf, tok, amt, rcpt, root]).note.token := h1
  have ha : amt = (ext.withdraw [nf, tok, amt, rcpt, root]).note.amount := h2
  have hrc : rcpt = E.addr (ext.withdraw [nf, tok, amt, rcpt, root]).recipient :=
    hC.w_recipient _ _ hd'
  rw [hWP.token_calls hr hx, ← ht, ← ha, ← hrc]

end LeanShieldedPool.Refine
