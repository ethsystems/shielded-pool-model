import Refinement.ProvenanceRefine
import Tree.LeanImt

/-!
# Path-local tree premise and membership-checked inputs

`refinePL_run` is `refineP_run` with `TreeLink` and `TreeHyp` replaced by premises on the
paths the history supplies:

* The extracted witness keeps the circuit's Merkle path of each membership-checked input
  (`PathExt`): `(proof_length, indices, path)` of `verify_merkle_proof<32>`.
* `PathFacts` is the circuit's fold equation for that retained path (the form the fold bridge
  composes with the LeanIMT module: `commitment_root = merkleRoot hash2v C proof_length indices
  path`). It replaces the
  existential `Incl` of `CircuitFacts.t_member` and `CircuitFacts.w_member`, which are not used.
* `PathTreeHyp` asks, for each membership-checked input `(w, p)`, that `w ≠ 0` and that
  `LeanImt.Bad` does not occur on `p` at any prefix of the history's leaves whose root `p` folds `w` to.
  Paths nobody supplied are not constrained. `TreeLink` is not a premise:
  `LeanImt.binding_mem_or_bad` proves the reduction for the real fold.
* Membership-checked inputs (`Call.checked`): input 0 of every transfer, zero amount included;
  input 1 only when its amount is nonzero; the note of every withdrawal. Ballast input 1 carries
  no obligation.

The deposit and admin cases are those of `refineP_run`.
-/

namespace LeanShieldedPool.Refine

open LeanImt

variable {P : PrimSpec}

/-! ## Retained paths -/

/-- A circuit Merkle path in the shape of `verify_merkle_proof<32>`: `proof_length`,
`indices`, `path`. -/
structure MPath where
  len : Nat
  idx : List.Vector Bool 32
  sib : List.Vector Nat 32

/-- The circuit fold of `leaf` along the path (`LeanImt.merkleRoot`, the extracted
`binary_merkle_root<32>`). -/
def MPath.fold (H : Nat → Nat → Nat) (p : MPath) (leaf : Nat) : Nat :=
  merkleRoot H leaf p.len p.idx p.sib

/-- The (bit, sibling) pairs the fold uses (`LeanImt.activePath`). -/
def MPath.active (p : MPath) : List (Bool × Nat) :=
  activePath p.len p.idx.toList p.sib.toList 32

/-- The path part of the extracted witness, one per public-input vector like `Extractor`: the
paths of transfer inputs 0 and 1, and the withdrawn note's path. -/
structure PathExt where
  transfer : List Nat → MPath × MPath
  withdraw : List Nat → MPath

/-- **Circuit membership facts on the retained path (T3, W2).** The extracted path folds the
extracted input commitment to the public root (public input 4). This is the circuit's fold equation
(`Transfer.Root.accepting_main_transfer_root`, `Withdraw.Root.accepting_main_withdraw_root` of
`circuits-lampe/`) for the extracted witness; `FoldBridge.merkleRoot_val` (`fold-bridge/`) turns
its value into this `Nat` fold with `H := Hn hash2v`. Discharged by
citation, like `CircuitFacts`. -/
structure PathFacts (H : Nat → Nat → Nat) (E : Enc P) (C : Circuits P) (ext : Extractor P)
    (pext : PathExt) : Prop where
  /-- T3, input 0: always, zero amount included. -/
  t_path0 : ∀ x, C.transfer x (ext.transfer x) →
    (pext.transfer x).1.fold H (E.cm (ext.transfer x).in1.cm) = x.getD 4 0
  /-- T3, input 1: only when its amount is nonzero. -/
  t_path1 : ∀ x, C.transfer x (ext.transfer x) → (ext.transfer x).in2.amount ≠ 0 →
    (pext.transfer x).2.fold H (E.cm (ext.transfer x).in2.cm) = x.getD 4 0
  /-- W2. -/
  w_path : ∀ x, C.withdraw x (ext.withdraw x) →
    (pext.withdraw x).fold H (E.cm (ext.withdraw x).note.cm) = x.getD 4 0

/-! ## Membership-checked inputs (A12 scope) -/

/-- The membership-checked inputs of a transfer with public inputs `x`: input 0 always, input 1
only when its amount is nonzero. Each is (commitment word, retained path). -/
def checkedT (E : Enc P) (ext : Extractor P) (pext : PathExt) (x : List Nat) :
    List (Nat × MPath) :=
  (E.cm (ext.transfer x).in1.cm, (pext.transfer x).1) ::
    if (ext.transfer x).in2.amount = 0 then []
    else [(E.cm (ext.transfer x).in2.cm, (pext.transfer x).2)]

/-- The membership-checked input of a withdrawal: its note. -/
def checkedW (E : Enc P) (ext : Extractor P) (pext : PathExt) (x : List Nat) :
    List (Nat × MPath) :=
  [(E.cm (ext.withdraw x).note.cm, pext.withdraw x)]

/-- The membership-checked inputs of a call; none for a deposit or an admin call. -/
def Call.checked (E : Enc P) (ext : Extractor P) (pext : PathExt) : Call → List (Nat × MPath)
  | .transfer n0 n1 c0 c1 root pay => checkedT E ext pext [n0, n1, c0, c1, root, pay]
  | .withdraw nf tok amt rcpt root => checkedW E ext pext [nf, tok, amt, rcpt, root]
  | _ => []

/-- The membership-checked inputs of a history. -/
def checkedInputs (E : Enc P) (ext : Extractor P) (pext : PathExt) (h : List Call) :
    List (Nat × MPath) :=
  h.flatMap (Call.checked E ext pext)

/-- Input 0 is always checked, zero amount included. -/
theorem checkedT_in1 (E : Enc P) (ext : Extractor P) (pext : PathExt) (x : List Nat) :
    (E.cm (ext.transfer x).in1.cm, (pext.transfer x).1) ∈ checkedT E ext pext x :=
  List.mem_cons_self

/-- Input 1 is checked when its amount is nonzero. -/
theorem checkedT_in2 (E : Enc P) (ext : Extractor P) (pext : PathExt) (x : List Nat)
    (ha : (ext.transfer x).in2.amount ≠ 0) :
    (E.cm (ext.transfer x).in2.cm, (pext.transfer x).2) ∈ checkedT E ext pext x := by
  unfold checkedT
  rw [if_neg ha]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- Ballast input 1 is not checked. -/
theorem checkedT_ballast (E : Enc P) (ext : Extractor P) (pext : PathExt) (x : List Nat)
    (ha : (ext.transfer x).in2.amount = 0) :
    checkedT E ext pext x = [(E.cm (ext.transfer x).in1.cm, (pext.transfer x).1)] := by
  unfold checkedT
  rw [if_pos ha]

/-! ## The per-path premise -/

/-- **A9b and A12 per path (replaces `TreeHyp`; idealised crypto premise, scoped to the
history).** For each membership-checked input `(w, p)` of the history: `w ≠ 0` (A12), and at
every prefix `L` of the history's leaves whose LeanIMT root `p` folds `w` to, the bad event `LeanImt.Bad`
(an `H` collision against a tree node, a leaf equal to an internal node, or a fold output equal
to a leaf) does not occur on `p` (A9b). Other paths are not constrained. Board rows A9b, A12. -/
structure PathTreeHyp (H : Nat → Nat → Nat) (G : List Nat) (Q : List (Nat × MPath)) : Prop where
  nonzero : ∀ q ∈ Q, q.1 ≠ 0
  no_bad : ∀ L, L <+: G → ∀ q ∈ Q, q.2.fold H q.1 = rootOf H L →
    ¬ Bad H (imtOf H L).depth L q.1 q.2.active

/-! ## Withdraw (the adapter case) -/

/-- **Withdraw case on the per-path premises.** `withdrawP_step` with its global
membership hypothesis replaced: `LeanImt.binding_mem_or_bad` on the retained path gives membership
or `Bad` on that path, and `PathTreeHyp.no_bad` excludes `Bad` for that path only. -/
theorem withdrawPL_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
    {pext : PathExt} {Incl : Nat → Nat → Prop} {sup : P.Token → Prop}
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm) {G : List Nat} {Q : List (Nat × MPath)}
    (hPT : PathTreeHyp H G Q)
    {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {nf tok amt rcpt root : Nat}
    (hd : (Call.withdraw nf tok amt rcpt root).extractOK C ext)
    (hG : ghostLeaves h <+: G) (hQ : (Call.withdraw nf tok amt rcpt root).checked E ext pext ⊆ Q)
    (hamt : amt ≠ 0) (hun : σ.nullifiers nf = false) (hkr : σ.isKnownRoot root)
    (hpost : σ' = withdrawStorage σ nf) (hI : InvP H E ext sup h σ txs st) :
    ∃ txs' st', InvP H E ext sup (h ++ [.withdraw nf tok amt rcpt root]) σ' txs' st' := by
  let d := ext.withdraw [nf, tok, amt, rcpt, root]
  let p := pext.withdraw [nf, tok, amt, rcpt, root]
  have hd' : C.withdraw [nf, tok, amt, rcpt, root] d := hd
  have hfold : p.fold H (E.cm d.note.cm) = root := hPF.w_path _ hd'
  have hq : (E.cm d.note.cm, p) ∈ Q := hQ (List.mem_singleton_self _)
  have ho := hC.w_owner _ _ hd'
  have enf : nf = E.nf d.nf := hC.w_nullifier _ _ hd'
  have ea : amt = d.note.amount := (hC.w_public _ _ hd').2
  have hu := hC.w_amount _ _ hd'
  have hG' : ghostLeaves (h ++ [.withdraw nf tok amt rcpt root]) = ghostLeaves h :=
    ghostLeaves_snoc_nil _ _ rfl
  by_cases hcr0 : CryptoHyp P txs
  swap
  · refine ⟨txs ++ [.withdraw d], st, ?_, fun hcr => absurd (CryptoHyp.of_snoc hcr) hcr0⟩
    rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  obtain ⟨hrun, hR⟩ := hI.2 hcr0
  obtain ⟨n, hn, hroot⟩ := hR.prov.known_root hkr
  have hmem : st.inTreeAt n d.note.cm := by
    have hL : (ghostLeaves h).take n <+: G := (List.take_prefix _ _).trans hG
    have hf : p.fold H (E.cm d.note.cm) = rootOf H ((ghostLeaves h).take n) := hfold.trans hroot
    have hw : E.cm d.note.cm ∈ (ghostLeaves h).take n :=
      (binding_mem_or_bad H _ _ p.len p.idx p.sib (hPT.nonzero _ hq) hf).resolve_right
        (hPT.no_bad _ hL _ hq hf)
    exact inTree_of_memP hR hinj hw
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
  rw [hG', hpost]
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

/-- Membership from the per-path premise: a checked input whose retained path folds it to the
root of a prefix of the history's leaves is a leaf of that prefix. -/
theorem pathTree_member {H : Nat → Nat → Nat} {G : List Nat} {Q : List (Nat × MPath)}
    (hPT : PathTreeHyp H G Q) {L : List Nat} (hL : L <+: G) {w : Nat} {p : MPath}
    (hq : (w, p) ∈ Q) (hf : p.fold H w = rootOf H L) : w ∈ L :=
  (binding_mem_or_bad H L w p.len p.idx p.sib (hPT.nonzero _ hq) hf).resolve_right
    (hPT.no_bad L hL _ hq hf)

/-! ## Transfer -/

/-- **Transfer case on the per-path premises.** Input 0 is always checked; input 1 only when its
amount is nonzero, and otherwise it is ballast in the model guard. -/
theorem transferPL_step {H : Nat → Nat → Nat} {C : Circuits P} {E : Enc P} {ext : Extractor P}
    {pext : PathExt} {Incl : Nat → Nat → Prop} {sup : P.Token → Prop}
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm) {G : List Nat} {Q : List (Nat × MPath)}
    (hPT : PathTreeHyp H G Q)
    {h : List Call} {σ σ' : Storage} {txs : List (Tx P)} {st : St P}
    {n0 n1 c0 c1 root pay : Nat}
    (hd : (Call.transfer n0 n1 c0 c1 root pay).extractOK C ext)
    (hG : ghostLeaves h <+: G) (hQ : (Call.transfer n0 n1 c0 c1 root pay).checked E ext pext ⊆ Q)
    (hdist : n0 ≠ n1) (hun : σ.nullifiers n0 = false ∧ σ.nullifiers n1 = false)
    (hkr : σ.isKnownRoot root) (hfo : σ.leafIndex c0 = 0 ∧ σ.leafIndex c1 = 0 ∧ c0 ≠ c1)
    (hpost : σ' = transferStorage H σ n0 n1 c0 c1)
    (hI : InvP H E ext sup h σ txs st) :
    ∃ txs' st', InvP H E ext sup (h ++ [.transfer n0 n1 c0 c1 root pay]) σ' txs' st' := by
  let d := ext.transfer [n0, n1, c0, c1, root, pay]
  have hd' : C.transfer [n0, n1, c0, c1, root, pay] d := hd
  obtain ⟨ho1, ho2⟩ := hC.t_owner _ _ hd'
  obtain ⟨hn0, hn1⟩ := hC.t_nullifiers _ _ hd'
  obtain ⟨htk1, htk2, htk3⟩ := hC.t_tokens _ _ hd'
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hC.t_ranges _ _ hd'
  have hcons := hC.t_conservation _ _ hd'
  obtain ⟨hc0, hc1⟩ := hC.t_outputs _ _ hd'
  have en0 : n0 = E.nf d.nf1 := hn0
  have en1 : n1 = E.nf d.nf2 := hn1
  have ec0 : c0 = E.cm d.out1.cm := hc0
  have ec1 : c1 = E.cm d.out2.cm := hc1
  have hG' : ghostLeaves (h ++ [.transfer n0 n1 c0 c1 root pay]) = ghostLeaves h ++ [c0, c1] :=
    ghostLeaves_snoc _ _
  by_cases hcr0 : CryptoHyp P txs
  swap
  · refine ⟨txs ++ [.transfer d], st, ?_, fun hcr => absurd (CryptoHyp.of_snoc hcr) hcr0⟩
    rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  obtain ⟨hrun, hR⟩ := hI.2 hcr0
  obtain ⟨n, hn, hroot⟩ := hR.prov.known_root hkr
  have hL : (ghostLeaves h).take n <+: G := (List.take_prefix _ _).trans hG
  have hmem1 : st.inTreeAt n d.in1.cm :=
    inTree_of_memP hR hinj (pathTree_member hPT hL (hQ (checkedT_in1 E ext pext _))
      ((hPF.t_path0 _ hd').trans hroot))
  have hmem2 : d.in2.isBallast ∨ st.inTreeAt n d.in2.cm := by
    by_cases hb : d.in2.amount = 0
    · exact Or.inl hb
    · exact Or.inr (inTree_of_memP hR hinj (pathTree_member hPT hL
        (hQ (checkedT_in2 E ext pext _ hb)) ((hPF.t_path1 _ hd' hb).trans hroot)))
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
    ⟨hlen ▸ hn, ho1, ho2, hmem1, hmem2, fresh1,
      fresh2, hne, htk1, htk2, htk3, hr1, hr2, hr3, hr4, hcons, out1, out2, outne⟩
  refine ⟨txs ++ [.transfer d'], d'.post st, ?_,
    fun _ => ⟨Run'.step hrun (Step'.transfer hguard), ?_⟩⟩
  · rw [List.map_append, hI.1, txsOf_snoc]
    rfl
  rw [hG', hpost]
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

/-! ## Composition -/

/-- The induction behind `refinePL_run`: `refineP_inv` with `TreeLink` and `TreeHyp` replaced by
`PathFacts` and `PathTreeHyp` on the membership-checked inputs. -/
theorem refinePL_inv {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {pext : PathExt} {Incl : Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm)
    {hf : List Call} (hC1 : NoSetVerifier hf) (hEx : ExtractedWitnesses C ext hf)
    (hPT : PathTreeHyp H (ghostLeaves hf) (checkedInputs E ext pext hf))
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
    have hGp : ghostLeaves h0 <+: ghostLeaves hf := ghostLeaves_prefix hp0
    have hQ : c.checked E ext pext ⊆ checkedInputs E ext pext hf := fun q hq =>
      List.mem_flatMap.2 ⟨c, hcmem, hq⟩
    cases c with
    | deposit s cm tok amt fund att pay =>
      exact depositP_step hC (hEx _ hcmem) (hD.supported hreach hx) (hD.amount_ne_zero hreach hx)
        (hD.fresh_leaf hreach hx)
        (hD.post hreach hx (no_nested hEnv hreach hx (hD.guarded hreach hx))) hI
    | transfer n0 n1 c0 c1 root pay =>
      exact transferPL_step hC hPF hinj hPT (hEx _ hcmem) hGp hQ (hTP.distinct hreach hx)
        (hTP.unspent hreach hx) (hTP.known_root hreach hx) (hTP.fresh_outputs hreach hx)
        (hTP.post hreach hx (no_nested_of_nil (hTP.no_effects hreach hx))) hI
    | withdraw nf tok amt rcpt root =>
      exact withdrawPL_step hC hPF hinj hPT (hEx _ hcmem) hGp hQ (hWP.amount_ne_zero hreach hx)
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

/-- **`refineP_run` on the per-path premises.** The premises of `refineP_run` with `TreeLink`
and `TreeHyp` replaced by `PathFacts` (the circuit's fold equation on the retained path) and
`PathTreeHyp` (nonzero words and no `LeanImt.Bad` on the supplied paths of the
membership-checked inputs). The conclusion is
unchanged: the extracted operations form a `Step'` run whose state `RepP` relates to the
storage. -/
theorem refinePL_run {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {pext : PathExt} {Incl : Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h)
    (hEx : ExtractedWitnesses C ext h)
    (hPT : PathTreeHyp H (ghostLeaves h) (checkedInputs E ext pext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ txs st, txs.map eraseSnap = txsOf ext h ∧
      Run' (supOf E h) txs st ∧ RepP H E (supOf E h) (ghostLeaves h) σ st := by
  obtain ⟨txs, st, hE, hI⟩ :=
    refinePL_inv hG0 hRB hEnv hD hTP hWP hA hC hPF hinj hC1 hEx hPT hacc (List.prefix_refl h)
  exact ⟨txs, st, hE, hI (cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr))⟩

/-- Money on the refined run, per-path premises: value conservation. -/
theorem refinePL_valueConservation {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P}
    {E : Enc P} {ext : Extractor P} {pext : PathExt} {Incl : Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h)
    (hEx : ExtractedWitnesses C ext h)
    (hPT : PathTreeHyp H (ghostLeaves h) (checkedInputs E ext pext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ (txs : List (Tx P)) (st : St P), txs.map eraseSnap = txsOf ext h ∧
      RepP H E (supOf E h) (ghostLeaves h) σ st ∧
      ∀ t, st.deposited t = st.withdrawn t + liveValue st t := by
  obtain ⟨txs, st, hE, hr, hR⟩ :=
    refinePL_run hG0 hRB hEnv hD hTP hWP hA hC hPF hinj hacc hC1 hEx hPT hcr
  exact ⟨txs, st, hE, hR, valueConservation_prov _ txs st hr
    (cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr))⟩

/-! ## Relation to the global premise -/

/-- **The per-path premise is implied by the global one on the same words.** If every checked
word is among the words of a global `TreeHyp (CollC H)`, the per-path premise holds: a bad event
on a supplied path is one witness of `CollC`. -/
theorem PathTreeHyp.of_global {H : Nat → Nat → Nat} {G W : List Nat} {Q : List (Nat × MPath)}
    (hW : ∀ q ∈ Q, q.1 ∈ W) (hTH : TreeHyp (CollC H) G W) : PathTreeHyp H G Q where
  nonzero := fun q hq => hTH.nonzero _ (hW q hq)
  no_bad := fun L hL q hq hf hb => hTH.no_bad L hL _ (hW q hq) ⟨q.2.len, q.2.idx, q.2.sib, hf, hb⟩

end LeanShieldedPool.Refine
