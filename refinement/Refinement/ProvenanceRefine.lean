import Refinement.Provenance
import Refinement.ProvenanceModel

/-!
# Root provenance, part 3: `refine_run` into `Step'` without `RootsNonzero`

`RepP` is `Rep` with the ring, window and nonzero-root fields replaced by provenance
(`RepP.valid`: every valid root is a prefix root). `refineP_run` is `refine_run` with the
conclusion `Run'` (the `Step'` model) and `RepP`, and with the `RootsNonzero` premise removed.
Every other premise is unchanged. `Rep.toRepP`: `Rep` implies `RepP`.

The proof is that of `refine_run`, case by case; the changes are the root guard
(`Prov.known_root` gives a leaf count of the current tree, not a window entry), the valid-roots
field (`prov_step`), and the withdraw balance lemma (`withdraw_balance` through `Run'.to_run`).
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

/-- **The representation relation with provenance.** `Rep` without the ring and window fields, with provenance for the
valid roots. -/
structure RepP (H : Nat → Nat → Nat) (E : Enc P) (sup : P.Token → Prop) (L : List Nat)
    (σ : Storage) (st : St P) : Prop where
  leaves : st.leaves.map E.cm = L
  tree : σ.imt = imtOf H L
  leafIndex : ∀ w, σ.leafIndex w ≠ 0 ↔ w ∈ L
  nullifiers : ∀ w, σ.nullifiers w = true ↔ w ∈ st.nullifiers.map E.nf
  supported : ∀ t, σ.supportedTokens (E.tok t) = true → sup t
  supported_eq : st.supported = sup
  valid : ∀ r, σ.validRoots r = true → PrefixRoot H L r

theorem RepP.prov {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop} {L : List Nat}
    {σ : Storage} {st : St P} (hR : RepP H E sup L σ st) : Prov H L σ := ⟨hR.tree, hR.valid⟩

/-- `Rep` implies `RepP`: the window inclusion gives provenance. -/
theorem Rep.toRepP {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop} {L : List Nat}
    {σ : Storage} {st : St P} (hR : Rep H E sup L σ st) : RepP H E sup L σ st where
  leaves := hR.leaves
  tree := hR.tree
  leafIndex := hR.leafIndex
  nullifiers := hR.nullifiers
  supported := hR.supported
  supported_eq := hR.supported_eq
  valid := fun r hr => by
    obtain ⟨n, hn, he⟩ := hR.known_root_in_window (Or.inr hr)
    have hlen : st.minted.length = L.length := by
      rw [← hR.leaves]
      simp only [St.leaves, List.length_map]
    exact ⟨n, hlen ▸ (hR.window_le n hn), he⟩

theorem repP_genesis (H : Nat → Nat → Nat) (E : Enc P) (sup : P.Token → Prop) (v reg o : Nat) :
    RepP H E sup [] (Storage.genesis v reg o) (St.empty P sup) :=
  (rep_genesis H E sup v reg o).toRepP

theorem RepP.frame {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop}
    {L : List Nat} {σ σ' : Storage} {st : St P} (hR : RepP H E sup L σ st)
    (himt : σ'.imt = σ.imt) (hli : σ'.leafIndex = σ.leafIndex)
    (hv : σ'.validRoots = σ.validRoots) (hn : σ'.nullifiers = σ.nullifiers)
    (hs : ∀ t, σ'.supportedTokens (E.tok t) = true → sup t) : RepP H E sup L σ' st where
  leaves := hR.leaves
  tree := himt.trans hR.tree
  leafIndex := fun w => by rw [hli]; exact hR.leafIndex w
  nullifiers := fun w => by rw [hn]; exact hR.nullifiers w
  supported := hs
  supported_eq := hR.supported_eq
  valid := fun r h => by rw [hv] at h; exact hR.valid r h

theorem RepP.minted_length {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop}
    {L : List Nat} {σ : Storage} {st : St P} (hR : RepP H E sup L σ st) :
    st.minted.length = L.length := by
  rw [← hR.leaves]
  simp only [St.leaves, List.length_map]

/-- The induction invariant with `Step'` and `RepP`. -/
def InvP (H : Nat → Nat → Nat) (E : Enc P) (ext : Extractor P) (sup : P.Token → Prop)
    (h : List Call) (σ : Storage) (txs : List (Tx P)) (st : St P) : Prop :=
  txs.map eraseSnap = txsOf ext h ∧
    (CryptoHyp P txs → Run' sup txs st ∧ RepP H E sup (ghostLeaves h) σ st)

theorem inTree_of_memP {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop} {L : List Nat}
    {σ : Storage} {st : St P} (hR : RepP H E sup L σ st) (hinj : Function.Injective E.cm)
    {n : Nat} {c : P.Commitment} (hm : E.cm c ∈ L.take n) : st.inTreeAt n c := by
  rw [← hR.leaves, ← List.map_take] at hm
  obtain ⟨c', hc', he⟩ := List.mem_map.1 hm
  rw [hinj he] at hc'
  exact hc'

/-! ## Deposit -/

theorem depositP_rep {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop} {L : List Nat}
    {σ : Storage} {st : St P} (hR : RepP H E sup L σ st) (d : DepositData P) {c : Nat}
    (hc : c = E.cm d.note.cm) :
    RepP H E sup (L ++ [c]) (depositStorage H σ c) (d.post st) where
  leaves := by
    show ((st.minted ++ [d.note]).map Note.cm).map E.cm = L ++ [c]
    rw [← hR.leaves]
    simp only [St.leaves, List.map_append, List.map_cons, List.map_nil, hc]
  tree := by
    show (imtInsert H σ.imt c) = imtOf H (L ++ [c])
    rw [imtOf_append, hR.tree]
  leafIndex := fun w => by
    show Function.update σ.leafIndex c (σ.size + 1) w ≠ 0 ↔ w ∈ L ++ [c]
    rw [List.mem_append, List.mem_singleton]
    by_cases hw : w = c
    · rw [hw, Function.update_self]
      exact ⟨fun _ => Or.inr rfl, fun _ => Nat.succ_ne_zero _⟩
    · rw [Function.update_of_ne hw, hR.leafIndex w]
      exact ⟨Or.inl, fun h' => h'.resolve_right hw⟩
  nullifiers := hR.nullifiers
  supported := hR.supported
  supported_eq := hR.supported_eq
  valid := (prov_step (M := [c]) hR.prov rfl (depositStorage_fresh H σ c)).valid

theorem depositP_guard {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop}
    {L : List Nat} {σ : Storage} {st : St P} {c tok amt : Nat} (d : DepositData P)
    (hR : RepP H E sup L σ st) (hc : c = E.cm d.note.cm) (ht : tok = E.tok d.note.token)
    (ha : amt = d.note.amount) (hlt : d.note.amount < 2 ^ 128)
    (hsupp : σ.supportedTokens tok = true) (hamt : amt ≠ 0) (hfresh : σ.leafIndex c = 0) :
    d.guard st := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hR.supported_eq]
    exact hR.supported d.note.token (by rw [← ht]; exact hsupp)
  · rw [← ha]
    exact hamt
  · show d.note.amount ≤ 2 ^ 128 - 1
    exact Nat.le_sub_one_of_lt hlt
  · intro hm
    have hmem : E.cm d.note.cm ∈ L := by
      rw [← hR.leaves]
      exact List.mem_map.2 ⟨d.note.cm, hm, rfl⟩
    have h1 := (hR.leafIndex _).2 hmem
    rw [← hc] at h1
    exact h1 hfresh

/-- **Deposit case**, with no nonzero-root premise. -/
theorem depositP_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
    {Incl : Nat → Nat → Prop} {sup : P.Token → Prop} (hC : CircuitFacts E C Incl)
    {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {s c tok amt fund att pay : Nat}
    (hd : (Call.deposit s c tok amt fund att pay).extractOK C ext)
    (hsupp : σ.supportedTokens tok = true) (hamt : amt ≠ 0) (hfresh : σ.leafIndex c = 0)
    (hpost : σ' = depositStorage H σ c) (hI : InvP H E ext sup h σ txs st) :
    ∃ txs' st', InvP H E ext sup (h ++ [.deposit s c tok amt fund att pay]) σ' txs' st' := by
  let d := ext.deposit [c, tok, amt, fund, att, pay]
  have hd' : C.deposit [c, tok, amt, fund, att, pay] d := hd
  obtain ⟨h0, h1, h2⟩ := hC.d_commitment _ _ hd'
  have hc : c = E.cm d.note.cm := h0
  have ht : tok = E.tok d.note.token := h1
  have ha : amt = d.note.amount := h2
  have hlt := hC.d_amount _ _ hd'
  have hG : ghostLeaves (h ++ [.deposit s c tok amt fund att pay]) = ghostLeaves h ++ [c] :=
    ghostLeaves_snoc _ _
  refine ⟨txs ++ [.deposit d], d.post st, ?_, fun hcr => ?_⟩
  · rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  obtain ⟨hrun, hR⟩ := hI.2 (CryptoHyp.of_snoc hcr)
  refine ⟨Run'.step hrun (Step'.deposit (depositP_guard d hR hc ht ha hlt hsupp hamt hfresh)), ?_⟩
  rw [hG, hpost]
  exact depositP_rep hR d hc

/-! ## Transfer -/

/-- **Transfer case**, with the provenance root guard and no nonzero-root premise. -/
theorem transferP_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
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
    (hI : InvP H E ext sup h σ txs st) :
    ∃ txs' st', InvP H E ext sup (h ++ [.transfer n0 n1 c0 c1 root pay]) σ' txs' st' := by
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
  obtain ⟨n, hn, hroot⟩ := hR.prov.known_root hkr
  have hmem : ∀ nt : Note P, nt.cm ∈ (eraseSnap (Tx.transfer d)).consumes →
      Incl (E.cm nt.cm) root → st.inTreeAt n nt.cm := by
    intro nt hnt hi
    have hi' : Incl (E.cm nt.cm) (rootOf H ((ghostLeaves h).take n)) := hroot ▸ hi
    have hw : E.cm nt.cm ∈ inputWords E ext (h ++ [.transfer n0 n1 c0 c1 root pay]) :=
      mem_inputWords_snoc (List.mem_singleton_self _) hnt
    exact inTree_of_memP hR hinj (hmemb _ _ (List.take_prefix _ _) hw hi')
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
  have hlen := hR.minted_length
  let d' : TransferData P := { d with snapshot := n }
  have hguard : transferGuard' d' st :=
    ⟨hlen ▸ hn, ho1, ho2, hmem _ hin1 hm1', hm2'.imp_right (hmem _ hin2), fresh1,
      fresh2, hne, htk1, htk2, htk3, hr1, hr2, hr3, hr4, hcons, out1, out2, outne⟩
  refine ⟨txs ++ [.transfer d'], d'.post st, ?_,
    fun _ => ⟨Run'.step hrun (Step'.transfer hguard), ?_⟩⟩
  · rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  rw [hG, hpost]
  exact {
    leaves := by
      show ((st.minted ++ [d.out1, d.out2]).map Note.cm).map E.cm = ghostLeaves h ++ [c0, c1]
      rw [← hR.leaves, ec0, ec1]
      simp only [St.leaves, List.map_append, List.map_cons, List.map_nil]
    tree := by
      show imtInsert H (imtInsert H σ.imt c0) c1 = imtOf H (ghostLeaves h ++ [c0, c1])
      rw [show ghostLeaves h ++ [c0, c1] = (ghostLeaves h ++ [c0]) ++ [c1] by
        simp only [List.append_assoc, List.cons_append, List.nil_append],
        imtOf_append, imtOf_append, hR.tree]
    leafIndex := fun w => by
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
    nullifiers := fun w => by
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
    supported := hR.supported
    supported_eq := hR.supported_eq
    valid := (prov_step (M := [c0, c1]) hR.prov rfl
      (transferStorage_fresh H σ n0 n1 c0 c1)).valid }

/-! ## Withdraw -/

/-- `withdraw_balance` for `Step'` runs, through the simulation `Run'.to_run`. -/
theorem withdraw_balanceP {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run' sup txs st) (d : WithdrawData P) (hc : CryptoHyp P (txs ++ [.withdraw d]))
    (hin : d.note.cm ∈ st.leaves) (ho : d.note.ownedBy d.key) (hf : st.fresh d.nf)
    (hwf : d.note.wf) :
    d.note.amount ≤ st.balance d.note.token := by
  obtain ⟨txs₀, hr₀, he⟩ := hr.to_run
  have hc₀ : CryptoHyp P (txs₀ ++ [.withdraw d]) :=
    cryptoHyp_of_eraseSnap_eq (by rw [List.map_append, List.map_append, he]) hc
  exact withdraw_balance hr₀ d hc₀ hin ho hf hwf

/-- **Withdraw case**, with the provenance root guard. -/
theorem withdrawP_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
    {Incl : Nat → Nat → Prop} {sup : P.Token → Prop} (hC : CircuitFacts E C Incl)
    (hinj : Function.Injective E.cm)
    {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {nf tok amt rcpt root : Nat}
    (hd : (Call.withdraw nf tok amt rcpt root).extractOK C ext)
    (hmemb : ∀ L w, L <+: ghostLeaves h →
      w ∈ inputWords E ext (h ++ [.withdraw nf tok amt rcpt root]) → Incl w (rootOf H L) → w ∈ L)
    (hamt : amt ≠ 0) (hun : σ.nullifiers nf = false) (hkr : σ.isKnownRoot root)
    (hpost : σ' = withdrawStorage σ nf) (hI : InvP H E ext sup h σ txs st) :
    ∃ txs' st', InvP H E ext sup (h ++ [.withdraw nf tok amt rcpt root]) σ' txs' st' := by
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
  obtain ⟨n, hn, hroot⟩ := hR.prov.known_root hkr
  have hmem : st.inTreeAt n d.note.cm := by
    have hi' : Incl (E.cm d.note.cm) (rootOf H ((ghostLeaves h).take n)) := hroot ▸ hm
    have hnt : d.note.cm ∈ (eraseSnap (Tx.withdraw d)).consumes := List.mem_cons_self
    have hw : E.cm d.note.cm ∈ inputWords E ext (h ++ [.withdraw nf tok amt rcpt root]) :=
      mem_inputWords_snoc (List.mem_singleton_self _) hnt
    exact inTree_of_memP hR hinj (hmemb _ _ (List.take_prefix _ _) hw hi')
  have hfresh : d.nf ∉ st.nullifiers := by
    intro hmn
    have h1 := (hR.nullifiers nf).2 (by rw [enf]; exact List.mem_map.2 ⟨_, hmn, rfl⟩)
    rw [hun] at h1
    exact Bool.false_ne_true h1
  have hlen := hR.minted_length
  let d' : WithdrawData P := { d with snapshot := n }
  refine ⟨txs ++ [.withdraw d'], d'.post st, ?_, fun hcr => ?_⟩
  · rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  have hbal := withdraw_balanceP hrun d' hcr (List.mem_of_mem_take hmem) ho hfresh hu
  have hguard : withdrawGuard' d' st :=
    ⟨hlen ▸ hn, hmem, ho, hfresh, by rw [← ea]; exact hamt, hu, hbal⟩
  refine ⟨Run'.step hrun (Step'.withdraw hguard), ?_⟩
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
    valid := hR.valid }

/-! ## Composition -/

theorem stutterP_inv {H : Nat → Nat → Nat} {E : Enc P} {ext : Extractor P}
    {sup : P.Token → Prop} {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {c : Call} (hc : c.inserts = []) (hct : c.txs ext = [])
    (hrep : ∀ L, RepP H E sup L σ st → RepP H E sup L σ' st) (hI : InvP H E ext sup h σ txs st) :
    InvP H E ext sup (h ++ [c]) σ' txs st := by
  refine ⟨by rw [hI.1, txsOf_snoc, hct, List.map_nil, List.append_nil], fun hcr => ?_⟩
  obtain ⟨hrun, hR⟩ := hI.2 hcr
  exact ⟨hrun, by rw [ghostLeaves_snoc_nil h c hc]; exact hrep _ hR⟩

/-- The induction behind `refineP_run`. Same premises as `refine_inv` without
`RootsNonzero`. -/
theorem refineP_inv {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {Incl : Nat → Nat → Prop} {Coll : List Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hinj : Function.Injective E.cm)
    {hf : List Call} (hC1 : NoSetVerifier hf) (hEx : ExtractedWitnesses C ext hf)
    (hTL : TreeLink H Incl Coll (ghostLeaves hf) (inputWords E ext hf))
    (hTH : TreeHyp Coll (ghostLeaves hf) (inputWords E ext hf))
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) :
    h <+: hf → ∃ txs st, InvP H E ext (supOf E hf) h σ txs st := by
  induction hacc with
  | nil =>
    intro _
    obtain ⟨reg, o, e⟩ := hG0
    refine ⟨[], St.empty P (supOf E hf), rfl, fun _ => ⟨Run'.empty, ?_⟩⟩
    rw [e]
    exact repP_genesis H E (supOf E hf) X.pinnedVerifier reg o
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
      exact depositP_step hC (hEx _ hcmem) (hD.supported hreach hx) (hD.amount_ne_zero hreach hx)
        (hD.fresh_leaf hreach hx)
        (hD.post hreach hx (no_nested hEnv hreach hx (hD.guarded hreach hx))) hI
    | transfer n0 n1 c0 c1 root pay =>
      exact transferP_step hC hinj (hEx _ hcmem) hmemb (hTP.distinct hreach hx)
        (hTP.unspent hreach hx) (hTP.known_root hreach hx) (hTP.fresh_outputs hreach hx)
        (hTP.post hreach hx (no_nested_of_nil (hTP.no_effects hreach hx))) hI
    | withdraw nf tok amt rcpt root =>
      exact withdrawP_step hC hinj (hEx _ hcmem) hmemb (hWP.amount_ne_zero hreach hx)
        (hWP.unspent hreach hx) (hWP.known_root hreach hx)
        (hWP.post hreach hx (no_nested hEnv hreach hx (hWP.guarded hreach hx))) hI
    | setVerifier v => exact absurd rfl (hC1 _ hcmem v)
    | addSupportedToken tok =>
      refine ⟨txs, st, stutterP_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.add hreach hx]
      refine hR.frame rfl rfl rfl rfl (fun t ht => ?_)
      have ht' : Function.update σ0.supportedTokens tok true (E.tok t) = true := ht
      by_cases he : E.tok t = tok
      · show Call.addSupportedToken (E.tok t) ∈ hf
        rw [he]
        exact hcmem
      · rw [Function.update_of_ne he] at ht'
        exact hR.supported t ht'
    | removeSupportedToken tok =>
      refine ⟨txs, st, stutterP_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.remove hreach hx]
      refine hR.frame rfl rfl rfl rfl (fun t ht => ?_)
      have ht' : Function.update σ0.supportedTokens tok false (E.tok t) = true := ht
      by_cases he : E.tok t = tok
      · rw [he, Function.update_self] at ht'
        exact absurd ht' Bool.false_ne_true
      · rw [Function.update_of_ne he] at ht'
        exact hR.supported t ht'
    | setAttestationRegistry reg =>
      refine ⟨txs, st, stutterP_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.registry hreach hx]
      exact hR.frame rfl rfl rfl rfl hR.supported
    | transferOwnership o =>
      refine ⟨txs, st, stutterP_inv rfl rfl (fun L hR => ?_) hI⟩
      rw [hA.owner hreach hx]
      exact hR.frame rfl rfl rfl rfl hR.supported

/-- **`refine_run` into `Step'`, without `RootsNonzero`.** The premises of `refine_run` minus `RootsNonzero`;
conclusion: the extracted operations form a `Step'` run whose state `RepP` relates to the
storage. With `Run'.to_run` the money theorems apply to that run (`*_prov`). -/
theorem refineP_run {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {Incl : Nat → Nat → Prop} {Coll : List Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hinj : Function.Injective E.cm)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h)
    (hEx : ExtractedWitnesses C ext h)
    (hTL : TreeLink H Incl Coll (ghostLeaves h) (inputWords E ext h))
    (hTH : TreeHyp Coll (ghostLeaves h) (inputWords E ext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ txs st, txs.map eraseSnap = txsOf ext h ∧
      Run' (supOf E h) txs st ∧ RepP H E (supOf E h) (ghostLeaves h) σ st := by
  obtain ⟨txs, st, hE, hI⟩ :=
    refineP_inv hG0 hRB hEnv hD hTP hWP hA hC hinj hC1 hEx hTL hTH hacc (List.prefix_refl h)
  exact ⟨txs, st, hE, hI (cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr))⟩

/-- Money on the refined run: value conservation for the `Step'` run `refineP_run` returns. -/
theorem refineP_valueConservation {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P}
    {E : Enc P} {ext : Extractor P} {Incl : Nat → Nat → Prop} {Coll : List Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hinj : Function.Injective E.cm)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h)
    (hEx : ExtractedWitnesses C ext h)
    (hTL : TreeLink H Incl Coll (ghostLeaves h) (inputWords E ext h))
    (hTH : TreeHyp Coll (ghostLeaves h) (inputWords E ext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ (txs : List (Tx P)) (st : St P), txs.map eraseSnap = txsOf ext h ∧
      RepP H E (supOf E h) (ghostLeaves h) σ st ∧
      ∀ t, st.deposited t = st.withdrawn t + liveValue st t := by
  obtain ⟨txs, st, hE, hr, hR⟩ :=
    refineP_run hG0 hRB hEnv hD hTP hWP hA hC hinj hacc hC1 hEx hTL hTH hcr
  exact ⟨txs, st, hE, hR, valueConservation_prov _ txs st hr
    (cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr))⟩

end LeanShieldedPool.Refine
