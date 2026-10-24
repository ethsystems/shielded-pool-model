import Refinement.Post

/-!
# Composition lemmas and the deposit and admin cases of the refinement

`Inv` is the induction invariant: the model operations are the extracted ones up to snapshots,
and under `CryptoHyp` they form a model run whose state `Rep` relates to the storage. The step
lemmas take the contract, circuit and tree facts they need as plain hypotheses; `refine_run`
(`Refinement/Cases.lean`) supplies them from the premise structures on reachable states.
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

theorem txsOf_snoc (ext : Extractor P) (h : List Call) (c : Call) :
    txsOf ext (h ++ [c]) = txsOf ext h ++ (c.txs ext).map eraseSnap := by
  simp only [txsOf, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append]

theorem runNotes_eraseSnap (txs : List (Tx P)) : runNotes (txs.map eraseSnap) = runNotes txs := by
  induction txs with
  | nil => rfl
  | cons tx txs ih =>
    simp only [runNotes, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases tx <;> rfl

theorem runKeys_eraseSnap (txs : List (Tx P)) : runKeys (txs.map eraseSnap) = runKeys txs := by
  induction txs with
  | nil => rfl
  | cons tx txs ih =>
    simp only [runKeys, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases tx <;> rfl

theorem cryptoHyp_of_eraseSnap {txs : List (Tx P)} (hc : CryptoHyp P (txs.map eraseSnap)) :
    CryptoHyp P txs := by
  have hn := runNotes_eraseSnap txs
  have hk := runKeys_eraseSnap txs
  exact ⟨fun n h1 n' h2 => hc.commit_inj n (by rw [hn]; exact h1) n' (by rw [hn]; exact h2),
    fun k h1 k' h2 => hc.derivePub_inj k (by rw [hk]; exact h1) k' (by rw [hk]; exact h2)⟩

theorem CryptoHyp.of_snoc {txs : List (Tx P)} {tx : Tx P} (hc : CryptoHyp P (txs ++ [tx])) :
    CryptoHyp P txs := by
  have hn : runNotes txs ⊆ runNotes (txs ++ [tx]) := by
    simp only [runNotes, List.flatMap_append]
    exact List.subset_append_left _ _
  have hk : runKeys txs ⊆ runKeys (txs ++ [tx]) := by
    simp only [runKeys, List.flatMap_append]
    exact List.subset_append_left _ _
  exact ⟨fun n h1 n' h2 => hc.commit_inj n (hn h1) n' (hn h2),
    fun k h1 k' h2 => hc.derivePub_inj k (hk h1) k' (hk h2)⟩

theorem ghostLeaves_snoc_nil (h : List Call) (c : Call) (hc : c.inserts = []) :
    ghostLeaves (h ++ [c]) = ghostLeaves h := by
  rw [ghostLeaves_snoc, hc, List.append_nil]

theorem ghostLeaves_prefix {h₁ h₂ : List Call} (hp : h₁ <+: h₂) :
    ghostLeaves h₁ <+: ghostLeaves h₂ := by
  obtain ⟨t, rfl⟩ := hp
  unfold ghostLeaves
  rw [List.flatMap_append]
  exact List.prefix_append _ _

theorem inputWords_prefix {E : Enc P} {ext : Extractor P} {h₁ h₂ : List Call} (hp : h₁ <+: h₂) :
    inputWords E ext h₁ ⊆ inputWords E ext h₂ := by
  obtain ⟨t, rfl⟩ := hp
  unfold inputWords txsOf
  rw [List.flatMap_append, List.map_append, List.flatMap_append]
  exact List.subset_append_left _ _

theorem mem_inputWords_snoc {E : Enc P} {ext : Extractor P} {h : List Call} {c : Call}
    {tx : Tx P} (htx : tx ∈ c.txs ext) {cm : P.Commitment} (hcm : cm ∈ (eraseSnap tx).consumes) :
    E.cm cm ∈ inputWords E ext (h ++ [c]) := by
  unfold inputWords
  rw [txsOf_snoc]
  exact List.mem_flatMap.2 ⟨eraseSnap tx, List.mem_append_right _ (List.mem_map.2 ⟨tx, htx, rfl⟩),
    List.mem_map.2 ⟨cm, hcm, rfl⟩⟩

/-- The induction invariant for a history prefix: `txs` are the extracted operations, and under
`CryptoHyp` they form a model run whose state `Rep` relates to the storage. -/
def Inv (H : Nat → Nat → Nat) (E : Enc P) (ext : Extractor P) (sup : P.Token → Prop)
    (h : List Call) (σ : Storage) (txs : List (Tx P)) (st : St P) : Prop :=
  txs.map eraseSnap = txsOf ext h ∧
    (CryptoHyp P txs → Run sup txs st ∧ Rep H E sup (ghostLeaves h) σ st)

/-- **Nonzero recorded roots.** After every successful deposit or transfer of the history, the
LeanIMT root of the leaf list at that point is nonzero. These are exactly the roots
`_recordRoot` records; transfer's intermediate root after its first insert is not included.
`_recordRoot` evicts a ring entry only if it is nonzero, so a zero recorded root would stay
valid after it left the window. Scoped to the history, like `CryptoHyp`. No board row states it; it is a tree-type
obligation like A9a and A9b. `refineP_run` does not need it. -/
def RootsNonzero (H : Nat → Nat → Nat) (h : List Call) : Prop :=
  ∀ h₁ c h₂, h = h₁ ++ c :: h₂ → c.inserts ≠ [] → rootOf H (ghostLeaves (h₁ ++ [c])) ≠ 0

theorem RootsNonzero.at {H : Nat → Nat → Nat} {hf h0 : List Call} {c : Call}
    (hZ : RootsNonzero H hf) (hp : h0 ++ [c] <+: hf) (hc : c.inserts ≠ []) :
    rootOf H (ghostLeaves (h0 ++ [c])) ≠ 0 := by
  obtain ⟨t, ht⟩ := hp
  exact hZ h0 c t (by rw [← ht, List.append_assoc, List.singleton_append]) hc

/-- The supported set of a history: every token some `addSupportedToken` call added. -/
def supOf (E : Enc P) (h : List Call) (t : P.Token) : Prop := Call.addSupportedToken (E.tok t) ∈ h

theorem windowRoots_append_of_le (H : Nat → Nat → Nat) {L : List Nat} (c : Nat) {w : List Nat}
    (hw : ∀ n ∈ w, n ≤ L.length) : windowRoots H (L ++ [c]) w = windowRoots H L w := by
  unfold windowRoots
  apply List.map_congr_left
  intro n hn
  rw [List.take_append_of_le_length (hw n hn)]

theorem windowRoots_getD_take (H : Nat → Nat → Nat) (L w : List Nat) (j : Nat) (hj : j < 100) :
    (windowRoots H L (w.take 100)).getD j 0 = (windowRoots H L w).getD j 0 := by
  simp only [windowRoots, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, hj,
    ↓reduceIte]

/-- **Deposit case, representation.** One deposit of `c` preserves `Rep`. -/
theorem deposit_rep {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop} {L : List Nat}
    {σ : Storage} {st : St P} (hR : Rep H E sup L σ st) (d : DepositData P) {c : Nat}
    (hc : c = E.cm d.note.cm) (hZ : rootOf H (L ++ [c]) ≠ 0) :
    Rep H E sup (L ++ [c]) (depositStorage H σ c) (d.post st) := by
  have hlen : st.minted.length = L.length := by
    rw [← hR.leaves]
    simp only [St.leaves, List.length_map]
  have hi := hR.ringIndex_lt
  have hcur : (σ.insertLeaf H c).currentRoot = rootOf H (L ++ [c]) := by
    show (imtInsert H σ.imt c).root = (imtOf H (L ++ [c])).root
    rw [imtOf_append, hR.tree]
  exact {
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
    ringIndex_lt := Nat.mod_lt _ (by omega)
    ring := fun j hj => by
      show Function.update σ.ring σ.ringIndex (σ.insertLeaf H c).currentRoot
          (((σ.ringIndex + 1) % 100 + 99 - j) % 100) =
        (windowRoots H (L ++ [c]) (((st.minted.length + 1) :: st.window).take 100)).getD j 0
      rw [windowRoots_getD_take H _ _ j hj]
      rcases j with _ | k
      · have hp : ((σ.ringIndex + 1) % 100 + 99 - 0) % 100 = σ.ringIndex := by omega
        rw [hp, Function.update_self, hcur]
        show rootOf H (L ++ [c]) = rootOf H ((L ++ [c]).take (st.minted.length + 1))
        rw [hlen, List.take_of_length_le
          (Nat.le_of_eq (by simp only [List.length_append, List.length_singleton]))]
      · have hp : ((σ.ringIndex + 1) % 100 + 99 - (k + 1)) % 100 =
            (σ.ringIndex + 99 - k) % 100 := by omega
        have hne : (σ.ringIndex + 99 - k) % 100 ≠ σ.ringIndex := by omega
        rw [hp, Function.update_of_ne hne]
        show ringAt σ k = (windowRoots H (L ++ [c]) st.window).getD k 0
        rw [windowRoots_append_of_le H c hR.window_le]
        exact hR.ring k (by omega)
    head := by
      show some (st.minted.length + 1) = some (L ++ [c]).length
      rw [hlen, List.length_append, List.length_singleton]
    window_le := fun n hn => by
      have hn' : n ∈ (st.minted.length + 1) :: st.window := List.mem_of_mem_take hn
      rw [List.length_append, List.length_singleton]
      rcases List.mem_cons.1 hn' with rfl | h'
      · exact Nat.le_of_eq (congrArg (· + 1) hlen)
      · exact Nat.le_succ_of_le (hR.window_le n h')
    valid := fun r hr => by
      have hr' : (if r = (σ.insertLeaf H c).currentRoot then true
          else if σ.ring σ.ringIndex ≠ 0 ∧ r = σ.ring σ.ringIndex then false
          else σ.validRoots r) = true := hr
      by_cases h1 : r = (σ.insertLeaf H c).currentRoot
      · refine ⟨?_, σ.ringIndex, hi, ?_⟩
        · rw [h1, hcur]
          exact hZ
        · show Function.update σ.ring σ.ringIndex (σ.insertLeaf H c).currentRoot σ.ringIndex = r
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
          show Function.update σ.ring σ.ringIndex (σ.insertLeaf H c).currentRoot p = r
          rw [Function.update_of_ne hpi, hpr] }

/-- **Deposit case, guard.** The contract's deposit checks and the circuit facts give the model
guard. The `U128` bound comes from the circuit (the board's deposit amount row, `d_amount`). -/
theorem deposit_guard {H : Nat → Nat → Nat} {E : Enc P} {sup : P.Token → Prop}
    {L : List Nat} {σ : Storage} {st : St P} {c tok amt : Nat} (d : DepositData P)
    (hR : Rep H E sup L σ st) (hc : c = E.cm d.note.cm) (ht : tok = E.tok d.note.token)
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

/-- **Deposit case of the induction.** From the extracted witness (A2 per history),
`CircuitFacts` (the deposit amount row and D4) and the contract facts of `DepositPost` on a reachable state. -/
theorem deposit_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
    {Incl : Nat → Nat → Prop} {sup : P.Token → Prop} (hC : CircuitFacts E C Incl)
    {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {s c tok amt fund att pay : Nat}
    (hd : (Call.deposit s c tok amt fund att pay).extractOK C ext)
    (hsupp : σ.supportedTokens tok = true) (hamt : amt ≠ 0) (hfresh : σ.leafIndex c = 0)
    (hpost : σ' = depositStorage H σ c)
    (hz : rootOf H (ghostLeaves (h ++ [.deposit s c tok amt fund att pay])) ≠ 0)
    (hI : Inv H E ext sup h σ txs st) :
    ∃ txs' st', Inv H E ext sup (h ++ [.deposit s c tok amt fund att pay]) σ' txs' st' := by
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
  refine ⟨Run.step hrun (Step.deposit (deposit_guard d hR hc ht ha hlt hsupp hamt hfresh)), ?_⟩
  rw [hG, hpost]
  rw [hG] at hz
  exact deposit_rep hR d hc hz

/-- **Stutter step.** A call that inserts nothing and extracts nothing keeps `txs` and the model
state; only `Rep` must move to the new storage. Used for admin calls. -/
theorem stutter_inv {H : Nat → Nat → Nat} {E : Enc P} {ext : Extractor P}
    {sup : P.Token → Prop} {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {c : Call} (hc : c.inserts = []) (hct : c.txs ext = [])
    (hrep : ∀ L, Rep H E sup L σ st → Rep H E sup L σ' st) (hI : Inv H E ext sup h σ txs st) :
    Inv H E ext sup (h ++ [c]) σ' txs st := by
  refine ⟨by rw [hI.1, txsOf_snoc, hct, List.map_nil, List.append_nil], fun hcr => ?_⟩
  obtain ⟨hrun, hR⟩ := hI.2 hcr
  exact ⟨hrun, by rw [ghostLeaves_snoc_nil h c hc]; exact hrep _ hR⟩

end LeanShieldedPool.Refine
