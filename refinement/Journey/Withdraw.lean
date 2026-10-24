import Refinement.ProvenanceRefine
import Refinement.PathLocalNonVacuity
import LeanShieldedPool.Proofs.TierB

/-!
# One withdraw, composed across the hops that live in Lean

`withdraw_composed` chains, for one successful `withdraw` call, the hops that this package
states in Lean:

* the contract post (`WithdrawPost`: W6, W7, W10, S1/S2, X1, and the W1 lookup), on a reachable
  state, with the pinned verifier (C1);
* A2 for this call only: if the pinned verifier accepted the call's canonical vector, the
  extractor's witness satisfies the withdraw circuit relation;
* the withdraw circuit rows (`WithdrawRows`: W3, W4, W5, W8, W10) and W2 on the retained path
  (`PathFacts.w_path`: the circuit's fold equation for the extracted path);
* the tree hop on that path (the path-local premises): `LeanImt.binding_mem_or_bad` gives
  membership or the bad event `LeanImt.Bad` on the retained path, and `PathTreeHyp` (A9b, A12) excludes the bad event on that
  path only;
* the model pre-state: a `Run` and `RepP` (from `refinePL_inv` and `Run'.to_run`; X3, W1
  provenance, A9a);
* A1 (`CryptoHyp`) on the extended run.

It concludes that the extracted witness (snapshot set to the current leaf count) is bound to the
public words, that the proof's root is the root of a prefix of the leaves with the note in that
prefix, that the model guard of `Pool/Tx.lean:186` holds, that the storage after the call
represents the model post-state, that the one token call the contract issues is
`transfer(token(d), recipient(d), amount(d))` (movement of funds needs A10), and that the money
theorems hold for the extended run.

`withdraw_journey` adds the client and transport premise `hTransport` (one equation that fuses the
client's word order, the byte-to-word reading, ABI decoding and the wallet or relayer);
then the token call carries the user's intended token, amount and recipient words.
`withdraw_journey_of_history` obtains the pre-state for an accepted history from `refinePL_run`'s
premises. `JourneyToy.journey_toy` instantiates every premise on the toy pool of
`Refinement/NonVacuity.lean`, with the LeanIMT fold of `Tree/LeanImt.lean` on a depth-2 retained
path.

The non-Lean links are hypotheses; `ClientInputs` is a definition that only fixes the shape of the
client premise. Nothing here discharges a hypothesis.
-/

namespace LeanShieldedPool.Refine.Journey

open LeanShieldedPool LeanShieldedPool.Refine

variable {P : PrimSpec}

/-! ## Hypothesis shapes -/

/-- **Client words (shape of the client premise).** The five words of the withdraw public-input
array, read as `uint256` words through `E`: the nullifier argument, the token, the amount, the
recipient and the root argument, in this order.

The order is that of the client's withdraw public-input array (`public_inputs_as_array` of the
client's withdraw proof type), which is not in this repository; no theorem here links the
client's notes and byte words to `Note P` and `E`. The client takes the nullifier and root as
inputs, so `nfw` and `rootw` are free here. Only the token and amount of the note are read;
owner and salt are not. -/
def ClientInputs (E : Enc P) (n : Note P) (rcpt : P.Address) (nfw rootw : Nat) : List Nat :=
  [nfw, E.tok n.token, n.amount, E.addr rcpt, rootw]

/-- **The withdraw circuit rows other than membership**, on their own (withdraw fields of
`CircuitFacts`). Each is discharged by citation of a separate package (`circuits-lampe/`,
`circuits-acir/`), not by import. W2 enters through `PathFacts.w_path` on the retained path, so `CircuitFacts.w_member`
is not used. -/
structure WithdrawRows (E : Enc P) (C : Circuits P) : Prop where
  /-- W3 (patched Lampe, extractor trusted; binding via A1). Group: TOOLS, CRYPTO. -/
  w3_owner : ∀ x d, C.withdraw x d → d.note.ownedBy d.key
  /-- W4. Group: TOOLS. -/
  w4_nullifier : ∀ x d, C.withdraw x d → x.getD 0 0 = E.nf d.nf
  /-- W5 (binding to one note via A1). Group: TOOLS, CRYPTO. -/
  w5_public : ∀ x d, C.withdraw x d → x.getD 1 0 = E.tok d.note.token ∧ x.getD 2 0 = d.note.amount
  /-- W8, circuit half (over the compiled ACIR, ABI correspondence trusted).
  Group: TOOLS. -/
  w8_amount : ∀ x d, C.withdraw x d → U128 d.note.amount
  /-- W10, circuit side: the recipient is public input 3, unconstrained in-circuit and bound only
  by the proof (A2). Not a circuit row of the board; a source reading. Group: CRYPTO. -/
  w10_recipient : ∀ x d, C.withdraw x d → x.getD 3 0 = E.addr d.recipient

/-- The refinement premise `CircuitFacts` supplies the withdraw rows. -/
theorem WithdrawRows.of_circuitFacts {E : Enc P} {C : Circuits P} {Incl : Nat → Nat → Prop}
    (hC : CircuitFacts E C Incl) : WithdrawRows E C :=
  ⟨hC.w_owner, hC.w_nullifier, hC.w_public, hC.w_amount, hC.w_recipient⟩

/-- **The money theorems** of the model (CLAIMS.md rows 1 to 9: L3, L4, L4B), on one run. -/
structure Money (txs : List (Tx P)) (st : St P) : Prop where
  nullifierUnique : (txs.flatMap Tx.spends).Nodup
  noDoubleSpend : noteSpentAtMostOnce txs
  conservation : ∀ t, st.deposited t = st.withdrawn t + liveValue st t
  solvency : ∀ t, st.balance t + st.withdrawn t = st.deposited t
  noOverWithdrawal : ∀ t, st.withdrawn t ≤ st.deposited t
  noMinting : ∀ t, liveValue st t ≤ st.deposited t
  balanceLive : ∀ t, st.balance t = liveValue st t
  ownerKey : ∀ tx ∈ txs, ∀ n ∈ runNotes txs, n.cm ∈ tx.consumes → ∃ k ∈ tx.keys, n.ownedBy k

/-- The existing proofs give `Money` on every run under `CryptoHyp`. -/
theorem money_of_run {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) (hc : CryptoHyp P txs) : Money txs st where
  nullifierUnique := nullifierUniqueness_proof P sup txs st hr
  noDoubleSpend := noDoubleSpend_proof P sup txs st hr hc
  conservation := valueConservation_proof P sup txs st hr hc
  solvency := poolSolvency_proof P sup txs st hr
  noOverWithdrawal := noOverWithdrawal_proof P sup txs st hr
  noMinting := noMinting_proof P sup txs st hr hc
  balanceLive := balanceIsLiveValue_proof P sup txs st hr hc
  ownerKey := spendRequiresOwnerKey_proof P sup txs st hr hc

/-! ## The composed withdraw step -/

/-- **One withdraw, composed.** For a successful `withdraw nf tok amt rcpt root`
from a reachable storage `σ` that `RepP` relates to the end state `st` of a model run, the
extracted witness `d` (snapshot set to the current leaf count) is bound to the public words; the
proof's root is the LeanIMT root of a prefix of `L` that holds the note's commitment; `d` passes
the model guard; the storage after the call represents `d.post st`; the single token call the
contract issues is `transfer(token(d), recipient(d), amount(d))`; the model's `withdrawn` grows by
that amount (by the definition of `post`); and the extended run satisfies the money theorems.

The guard's window conjunct holds because the snapshot is the current leaf count, which every run
keeps in the window (`Run'.length_mem_window`); it is not the proof's historical root index. W1
enters as the prefix-root conjunct, which keeps that provenance. The theorem does not prove ERC-20
movement (A10), a nonzero recipient, or that the nullifier is marked before the payout call; it
credits only the stated parts of W6 and W10.

Premises, by hop:
* contract: `hWP` (W6 check and mark, W7, W10 payout call, S1/S2, X1, W1 lookup; the board's
  Kontrol and Halmos runs cover parts within their scopes; the whole-storage frame is unchecked;
  REF), `hEnv` (A13; DEPLOY),
  `hreach` (reachable without `setVerifier`: C1, DEPLOY; X3, REF), `hpin` (C1, DEPLOY);
* verifier: `hA2` (A2 for this call, idealised as perfect extraction; it also carries S3 and bb
  (A11): `C` must be the relation of the circuits the deployed verifier was built from; CRYPTO,
  TOOLS);
* circuits: `hW` (W3-W5, W8, W10), `hPF` (W2: the circuit's fold equation on the retained
  extracted path, cited; path extraction is part of A2, hash equality is A9b), `hinj`
  (commitment encoding injective; REF, no board row);
* tree: `hPT`, `hQ` (A9b, A12 per path; CRYPTO, REF): the note's word is nonzero and the bad
  event `LeanImt.Bad` does not occur on its retained path. `PathExt` selects that path by public-input vector;
  calling it the supplied path also needs the extraction correspondence. `hLG` is bookkeeping;
* model pre-state: `hrun`, `hR` (X3; `hR.valid` is W1 provenance, `Refinement/Provenance.lean`;
  `hR.tree` is A9a; REF, DEPLOY);
* `hcr` (A1 on the extended run; CRYPTO). -/
theorem withdraw_composed {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {pext : PathExt} {sup : P.Token → Prop}
    (hWP : WithdrawPost X) (hEnv : OwnerCallbackFree X)
    (hW : WithdrawRows E C) (hPF : PathFacts H E C ext pext) (hinj : Function.Injective E.cm)
    {σ σ' : Storage} {nf tok amt rcpt root : Nat} {tr : List Ext}
    (hreach : Reach X σ) (hpin : σ.verifier = X.pinnedVerifier)
    (hx : X.Exec σ (.withdraw nf tok amt rcpt root) tr σ')
    (hA2 : X.Verified X.pinnedVerifier .withdraw [nf, tok, amt, rcpt, root] →
      Canonical [nf, tok, amt, rcpt, root] →
      C.withdraw [nf, tok, amt, rcpt, root] (ext.withdraw [nf, tok, amt, rcpt, root]))
    {L : List Nat} {txs : List (Tx P)} {st : St P}
    (hrun : Run sup txs st) (hR : RepP H E sup L σ st)
    {G : List Nat} {Q : List (Nat × MPath)} (hPT : PathTreeHyp H G Q) (hLG : L <+: G)
    (hQ : (Call.withdraw nf tok amt rcpt root).checked E ext pext ⊆ Q)
    (hcr : CryptoHyp P (txs ++ [.withdraw (ext.withdraw [nf, tok, amt, rcpt, root])])) :
    ∃ d : WithdrawData P,
      d = { ext.withdraw [nf, tok, amt, rcpt, root] with snapshot := st.minted.length } ∧
      tok = E.tok d.note.token ∧ amt = d.note.amount ∧ rcpt = E.addr d.recipient ∧
      nf = E.nf d.nf ∧
      (∃ k ≤ L.length, root = rootOf H (L.take k) ∧ st.inTreeAt k d.note.cm) ∧
      d.guard st ∧
      Step st (.withdraw d) (d.post st) ∧
      RepP H E sup L σ' (d.post st) ∧
      tokenCalls tr = [.transfer (E.tok d.note.token) (E.addr d.recipient) d.note.amount] ∧
      (d.post st).withdrawn d.note.token = st.withdrawn d.note.token + d.note.amount ∧
      Run sup (txs ++ [.withdraw d]) (d.post st) ∧
      Money (txs ++ [.withdraw d]) (d.post st) := by
  let d0 := ext.withdraw [nf, tok, amt, rcpt, root]
  let p := pext.withdraw [nf, tok, amt, rcpt, root]
  -- verifier hop: the contract passed the five inputs in order (S2), all canonical (S1), to the
  -- pinned verifier, which accepted; A2 for this call gives the witness
  have hd0 : C.withdraw [nf, tok, amt, rcpt, root] d0 := by
    obtain ⟨hv, hcan⟩ := hWP.verified hreach hx
    rw [hpin] at hv
    exact hA2 hv hcan
  -- circuit hop
  have hf : p.fold H (E.cm d0.note.cm) = root := hPF.w_path _ hd0
  have ho : d0.note.ownedBy d0.key := hW.w3_owner _ _ hd0
  have enf : nf = E.nf d0.nf := hW.w4_nullifier _ _ hd0
  have et : tok = E.tok d0.note.token := (hW.w5_public _ _ hd0).1
  have ea : amt = d0.note.amount := (hW.w5_public _ _ hd0).2
  have hu : U128 d0.note.amount := hW.w8_amount _ _ hd0
  have er : rcpt = E.addr d0.recipient := hW.w10_recipient _ _ hd0
  -- contract hop
  have hamt : amt ≠ 0 := hWP.amount_ne_zero hreach hx
  have hun : σ.nullifiers nf = false := hWP.unspent hreach hx
  have hkr : σ.isKnownRoot root := hWP.known_root hreach hx
  have hpost : σ' = withdrawStorage σ nf :=
    hWP.post hreach hx (no_nested hEnv hreach hx (hWP.guarded hreach hx))
  -- tree hop: the root is a prefix root (root provenance); the retained path folds the note to
  -- it, so the LeanIMT binding gives membership unless its bad event holds on that path, which
  -- `hPT` excludes
  obtain ⟨k, hk, hroot⟩ := hR.prov.known_root hkr
  have hq : (E.cm d0.note.cm, p) ∈ Q := hQ (List.mem_singleton_self _)
  have hmemL : E.cm d0.note.cm ∈ L.take k :=
    pathTree_member hPT ((List.take_prefix k L).trans hLG) hq (hf.trans hroot)
  -- model hop
  have hmemk : st.inTreeAt k d0.note.cm := inTree_of_memP hR hinj hmemL
  have hmem : st.inTreeAt st.minted.length d0.note.cm := inTreeAt_current hmemk
  have hwin : st.rootInWindow st.minted.length := (run_to_run' hrun).length_mem_window
  have hfresh : st.fresh d0.nf := by
    intro hmn
    have h1 := (hR.nullifiers nf).2 (by rw [enf]; exact List.mem_map.2 ⟨_, hmn, rfl⟩)
    rw [hun] at h1
    exact Bool.false_ne_true h1
  let d : WithdrawData P := { d0 with snapshot := st.minted.length }
  have hcr' : CryptoHyp P (txs ++ [.withdraw d]) :=
    cryptoHyp_of_eraseSnap_eq (by rw [List.map_append, List.map_append]; try rfl) hcr
  have hbal : d.note.amount ≤ st.balance d.note.token :=
    withdraw_balance hrun d hcr' (List.mem_of_mem_take hmem) ho hfresh hu
  have hguard : d.guard st :=
    ⟨hwin, hmem, ho, hfresh, fun h0 => hamt (ea.trans h0), hu, hbal⟩
  have hrun' : Run sup (txs ++ [.withdraw d]) (d.post st) := Run.step hrun (Step.withdraw hguard)
  refine ⟨d, rfl, et, ea, er, enf, ⟨k, hk, hroot, hmemk⟩, hguard, Step.withdraw hguard, ?_, ?_, ?_,
    hrun', money_of_run hrun' hcr'⟩
  · rw [hpost]
    exact {
      leaves := hR.leaves
      tree := hR.tree
      leafIndex := hR.leafIndex
      nullifiers := fun w => by
        show Function.update σ.nullifiers nf true w = true ↔ w ∈ (d0.nf :: st.nullifiers).map E.nf
        rw [List.map_cons, List.mem_cons]
        by_cases hw : w = nf
        · rw [hw, Function.update_self, enf]
          exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
        · rw [Function.update_of_ne hw, hR.nullifiers w, ← enf]
          exact ⟨Or.inr, fun h' => h'.resolve_left hw⟩
      supported := hR.supported
      supported_eq := hR.supported_eq
      valid := hR.valid }
  · show tokenCalls tr = [.transfer (E.tok d0.note.token) (E.addr d0.recipient) d0.note.amount]
    rw [hWP.token_calls hreach hx, et, er, ea]
  · show bump st.withdrawn d0.note.token d0.note.amount d0.note.token =
      st.withdrawn d0.note.token + d0.note.amount
    unfold bump
    exact if_pos rfl

/-- **One withdraw, with the client and transport premise.** `withdraw_composed`, plus
`hTransport`: the submitted call's verifier-input vector (`Call.inputs`, the ABI order S2 names)
equals the client words for the intended note `n` and recipient `r` (`ClientInputs`).
`hTransport` fuses four links: the client's output order, the byte-to-word reading (TOOLS), ABI
decoding of the calldata, and the wallet or relayer. Client scope, outside claim 1. It does not execute the client, decode bytes, or compute the nullifier or root.

The token call carrying `n`'s token and amount words and `r`'s word follows from `hWP` and
`hTransport` alone. The circuit rows add that the witness note `d.note`, which the proof spends,
has the same token word and amount, and `d.recipient` the same word. Equalities are of words:
`E.tok` and `E.addr` are not assumed injective, and `d.note = n` is not concluded (owner and salt
are not read). -/
theorem withdraw_journey {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P} {E : Enc P}
    {ext : Extractor P} {pext : PathExt} {sup : P.Token → Prop}
    (hWP : WithdrawPost X) (hEnv : OwnerCallbackFree X)
    (hW : WithdrawRows E C) (hPF : PathFacts H E C ext pext) (hinj : Function.Injective E.cm)
    {σ σ' : Storage} {nf tok amt rcpt root : Nat} {tr : List Ext}
    (hreach : Reach X σ) (hpin : σ.verifier = X.pinnedVerifier)
    (hx : X.Exec σ (.withdraw nf tok amt rcpt root) tr σ')
    (hA2 : X.Verified X.pinnedVerifier .withdraw [nf, tok, amt, rcpt, root] →
      Canonical [nf, tok, amt, rcpt, root] →
      C.withdraw [nf, tok, amt, rcpt, root] (ext.withdraw [nf, tok, amt, rcpt, root]))
    {n : Note P} {r : P.Address} {nfw rootw : Nat}
    (hTransport : Call.inputs (.withdraw nf tok amt rcpt root) = ClientInputs E n r nfw rootw)
    {L : List Nat} {txs : List (Tx P)} {st : St P}
    (hrun : Run sup txs st) (hR : RepP H E sup L σ st)
    {G : List Nat} {Q : List (Nat × MPath)} (hPT : PathTreeHyp H G Q) (hLG : L <+: G)
    (hQ : (Call.withdraw nf tok amt rcpt root).checked E ext pext ⊆ Q)
    (hcr : CryptoHyp P (txs ++ [.withdraw (ext.withdraw [nf, tok, amt, rcpt, root])])) :
    ∃ d : WithdrawData P,
      d = { ext.withdraw [nf, tok, amt, rcpt, root] with snapshot := st.minted.length } ∧
      nf = E.nf d.nf ∧
      (∃ k ≤ L.length, root = rootOf H (L.take k) ∧ st.inTreeAt k d.note.cm) ∧
      d.guard st ∧
      Step st (.withdraw d) (d.post st) ∧
      RepP H E sup L σ' (d.post st) ∧
      tokenCalls tr = [.transfer (E.tok n.token) (E.addr r) n.amount] ∧
      E.tok d.note.token = E.tok n.token ∧ d.note.amount = n.amount ∧
      E.addr d.recipient = E.addr r ∧
      Run sup (txs ++ [.withdraw d]) (d.post st) ∧
      Money (txs ++ [.withdraw d]) (d.post st) := by
  have hT : [nf, tok, amt, rcpt, root] = [nfw, E.tok n.token, n.amount, E.addr r, rootw] :=
    hTransport
  have ht : tok = E.tok n.token := (List.cons.inj (List.cons.inj hT).2).1
  have ha : amt = n.amount := (List.cons.inj (List.cons.inj (List.cons.inj hT).2).2).1
  have hr : rcpt = E.addr r :=
    (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj hT).2).2).2).1
  obtain ⟨d, hdd, et, ea, er, enf, hprov, hg, hs, hRp, htc, -, hrun', hmoney⟩ :=
    withdraw_composed hWP hEnv hW hPF hinj hreach hpin hx hA2 hrun hR hPT hLG hQ hcr
  refine ⟨d, hdd, enf, hprov, hg, hs, hRp, ?_, et.symm.trans ht, ea.symm.trans ha,
    er.symm.trans hr, hrun', hmoney⟩
  rw [htc, ← et, ← ea, ← er, ht, ha, hr]

/-! ## From an accepted history (the refinement hop) -/

/-- **One withdraw at the end of an accepted history.** The premises are `refinePL_run`'s for the
history `h ++ [withdraw]` (`ConstructorPost`: C1; `Rollback`: A11, X3; `OwnerCallbackFree`: A13;
the four post structures: the D, T, W and G1 rows, REF; `CircuitFacts`: the circuit rows, its
membership fields unused; `PathFacts`: T3 and W2 on the retained paths; `hinj`: REF;
`NoSetVerifier`: C1; `ExtractedWitnesses`: A2 per history; `PathTreeHyp`: A9b, A12 on the
membership-checked inputs; `CryptoHyp`: A1), plus `hTransport` (client scope). `PathTreeHyp`
excludes the bad event at every prefix of the final history's leaves whose root a checked path
reaches, not only at the prefix current at the call. `refinePL_inv` supplies `Run'` and `RepP`
at `h`, `Run'.to_run` turns the `Run'` into a `Run` whose operations agree up to snapshots,
`reach_verifier` supplies the pinned verifier, and `withdraw_journey` does the rest. The
conclusion fixes the pre-run's operations to the extracted ones of `h`, up to snapshots. -/
theorem withdraw_journey_of_history {H : Nat → Nat → Nat} {X : Contract} {C : Circuits P}
    {E : Enc P} {ext : Extractor P} {pext : PathExt} {Incl : Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hPF : PathFacts H E C ext pext)
    (hinj : Function.Injective E.cm)
    {h : List Call} {σ σ' : Storage} {nf tok amt rcpt root : Nat} {tr : List Ext}
    (hacc : Accepted X h σ) (hx : X.Exec σ (.withdraw nf tok amt rcpt root) tr σ')
    (hC1 : NoSetVerifier (h ++ [.withdraw nf tok amt rcpt root]))
    (hEx : ExtractedWitnesses C ext (h ++ [.withdraw nf tok amt rcpt root]))
    (hPT : PathTreeHyp H (ghostLeaves (h ++ [.withdraw nf tok amt rcpt root]))
      (checkedInputs E ext pext (h ++ [.withdraw nf tok amt rcpt root])))
    (hcr : CryptoHyp P (txsOf ext (h ++ [.withdraw nf tok amt rcpt root])))
    {n : Note P} {r : P.Address} {nfw rootw : Nat}
    (hTransport : Call.inputs (.withdraw nf tok amt rcpt root) = ClientInputs E n r nfw rootw) :
    ∃ (txs : List (Tx P)) (st : St P) (d : WithdrawData P),
      txs.map eraseSnap = txsOf ext h ∧
      Run (supOf E (h ++ [.withdraw nf tok amt rcpt root])) txs st ∧
      RepP H E (supOf E (h ++ [.withdraw nf tok amt rcpt root])) (ghostLeaves h) σ st ∧
      d = { ext.withdraw [nf, tok, amt, rcpt, root] with snapshot := st.minted.length } ∧
      nf = E.nf d.nf ∧
      (∃ k ≤ (ghostLeaves h).length,
        root = rootOf H ((ghostLeaves h).take k) ∧ st.inTreeAt k d.note.cm) ∧
      d.guard st ∧
      RepP H E (supOf E (h ++ [.withdraw nf tok amt rcpt root])) (ghostLeaves h) σ' (d.post st) ∧
      tokenCalls tr = [.transfer (E.tok n.token) (E.addr r) n.amount] ∧
      E.tok d.note.token = E.tok n.token ∧ d.note.amount = n.amount ∧
      E.addr d.recipient = E.addr r ∧
      Run (supOf E (h ++ [.withdraw nf tok amt rcpt root])) (txs ++ [.withdraw d]) (d.post st) ∧
      Money (txs ++ [.withdraw d]) (d.post st) := by
  have hC0 : NoSetVerifier h := fun c hc => hC1 c (List.mem_append_left _ hc)
  have hreach : Reach X σ := ⟨h, hacc, hC0⟩
  have hpin := reach_verifier hG0 hRB hEnv hD hTP hWP hA hacc hC0
  have hA2 : X.Verified X.pinnedVerifier .withdraw [nf, tok, amt, rcpt, root] →
      Canonical [nf, tok, amt, rcpt, root] →
      C.withdraw [nf, tok, amt, rcpt, root] (ext.withdraw [nf, tok, amt, rcpt, root]) :=
    fun _ _ => hEx _ (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨txs', st, hE, hI⟩ :=
    refinePL_inv hG0 hRB hEnv hD hTP hWP hA hC hPF hinj hC1 hEx hPT hacc (List.prefix_append _ _)
  have hsnoc : txsOf ext (h ++ [.withdraw nf tok amt rcpt root]) =
      txsOf ext h ++ [eraseSnap (.withdraw (ext.withdraw [nf, tok, amt, rcpt, root]))] := by
    rw [txsOf_snoc]
    try rfl
  have hcr1 : CryptoHyp P
      (txsOf ext h ++ [eraseSnap (.withdraw (ext.withdraw [nf, tok, amt, rcpt, root]))]) := by
    rw [← hsnoc]
    exact hcr
  have hcr0 : CryptoHyp P txs' :=
    cryptoHyp_of_eraseSnap (by rw [hE]; exact CryptoHyp.of_snoc hcr1)
  obtain ⟨hrun'', hR⟩ := hI hcr0
  obtain ⟨txs, hrun, he⟩ := hrun''.to_run
  have hmap : (txs ++ [Tx.withdraw (ext.withdraw [nf, tok, amt, rcpt, root])]).map eraseSnap =
      txsOf ext h ++ [eraseSnap (.withdraw (ext.withdraw [nf, tok, amt, rcpt, root]))] := by
    rw [List.map_append, he, hE]
    try rfl
  have hcrx : CryptoHyp P (txs ++ [.withdraw (ext.withdraw [nf, tok, amt, rcpt, root])]) :=
    cryptoHyp_of_eraseSnap (by rw [hmap]; exact hcr1)
  have hLG : ghostLeaves h <+: ghostLeaves (h ++ [.withdraw nf tok amt rcpt root]) :=
    ghostLeaves_prefix (List.prefix_append _ _)
  have hQ : (Call.withdraw nf tok amt rcpt root).checked E ext pext ⊆
      checkedInputs E ext pext (h ++ [.withdraw nf tok amt rcpt root]) := fun q hq =>
    List.mem_flatMap.2 ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hq⟩
  obtain ⟨d, hdd, enf, hprov, hg, -, hRp, htc, ht, ha, hr, hrun', hmoney⟩ :=
    withdraw_journey hWP hEnv (WithdrawRows.of_circuitFacts hC) hPF hinj hreach hpin hx hA2
      hTransport hrun hR hPT hLG hQ hcrx
  exact ⟨txs, st, d, he.trans hE, hrun, hR, hdd, enf, hprov, hg, hRp, htc, ht, ha, hr, hrun',
    hmoney⟩

end LeanShieldedPool.Refine.Journey

/-! ## Non-vacuity on the toy pool -/

namespace LeanShieldedPool.Refine.JourneyToy

open LeanShieldedPool LeanShieldedPool.Refine LeanShieldedPool.Refine.ToyRun
  LeanShieldedPool.Refine.Journey

/-- The toy history before its withdraw: an admin call, a reverted `setVerifier`, a deposit and
a transfer. -/
def hist0 : List Call :=
  [.addSupportedToken 5, .deposit 7 9 5 3 7 0 0, .transfer 9 26 39 46 9 0]

theorem hist_eq : hist0 ++ [Call.withdraw 39 5 3 8 96] = hist := rfl

theorem hacc0 : Accepted X hist0 σ2 := by
  have e1 : X.Exec (Storage.genesis 1 2 3) (.addSupportedToken 5) [] σa := ⟨rfl, rfl⟩
  have e2 : X.Exec σa (.deposit 7 9 5 3 7 0 0) [.transferFrom 5 7 99 3] σ1 :=
    ⟨rfl, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, by decide⟩, by unfold Canonical; decide,
      rfl, rfl⟩
  have e3 : X.Exec σ1 (.transfer 9 26 39 46 9 0) [] σ2 :=
    ⟨by decide, rfl, rfl, Or.inl (by decide), by decide, by decide, by decide,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨1, by decide, by decide, by decide⟩, rfl, rfl, rfl,
        rfl, by show (3 : Nat) ≤ 2 ^ 128 - 1; decide, Nat.zero_le _,
        by show (3 : Nat) ≤ 2 ^ 128 - 1; decide, Nat.zero_le _, rfl⟩,
      by unfold Canonical; decide, rfl, rfl⟩
  have a1 : Accepted X ([] ++ [Call.addSupportedToken 5]) σa := Accepted.snoc Accepted.nil e1
  have a1' : Accepted X ([] ++ [Call.addSupportedToken 5]) σa :=
    Accepted.fail (c := .setVerifier 0) a1 rfl
  exact Accepted.snoc (Accepted.snoc a1' e2) e3

/-- The withdraw call itself: nullifier 39, token 5, amount 3, recipient 8, root 96. -/
theorem hx4 : X.Exec σ2 (.withdraw 39 5 3 8 96) [.transfer 5 8 3] σ3 :=
  ⟨by decide, by decide, Or.inl (by decide),
    ⟨rfl, rfl, rfl, rfl, rfl, ⟨3, by decide, by decide, by decide⟩, rfl,
      by show (3 : Nat) ≤ 2 ^ 128 - 1; decide⟩,
    by unfold Canonical; decide, rfl, rfl⟩

/-- The client words for the intended note (the transfer's first output: token 5, amount 3) and
recipient 8, with nullifier word 39 and root word 96, are the call's input vector. With `E = id`
this is `rfl`; the byte-to-word reading is not exercised. -/
theorem hTransport :
    Call.inputs (.withdraw 39 5 3 8 96) = ClientInputs Toy.E dT.out1 (8 : Nat) 39 96 := rfl

/-- **Non-vacuity.** Every premise of `withdraw_journey_of_history` holds on the toy pool (A2 as
the toy's per-history `hEx`; the tree hop through the path-local `PathToy.hPF` and `PathToy.hPT`), so its
conclusion holds outright: a model run, the extracted witness, the prefix root 96 holding the
note, the model withdraw guard, the represented post-state, witness words token 5, amount 3,
recipient 8, and the money theorems for the extended run. The withdrawal's retained path `PathToy.W2`
has length 2 and goes through the LeanIMT binding on the depth-2 tree `[9, 39, 46]`
(`PathToy.toy_positive_depth`). The toy `CircuitFacts` (`ToyRun.hC`) is still a premise; its relation
`InclT` already contains membership, but the journey does not use it. The hash is the toy
`a + b + 1`, not Poseidon, and `E = id`, so neither production hashes nor client bytes are
exercised. It says nothing about the deployed pool. -/
theorem journey_toy : ∃ (txs : List (Tx Toy.P)) (st : St Toy.P) (d : WithdrawData Toy.P),
    txs.map eraseSnap = txsOf ext hist0 ∧
    Run (supOf Toy.E hist) txs st ∧
    d = { ext.withdraw [39, 5, 3, 8, 96] with snapshot := st.minted.length } ∧
    (∃ k ≤ (ghostLeaves hist0).length,
      (96 : Nat) = rootOf Toy.H ((ghostLeaves hist0).take k) ∧ st.inTreeAt k d.note.cm) ∧
    d.guard st ∧
    RepP Toy.H Toy.E (supOf Toy.E hist) (ghostLeaves hist0) σ3 (d.post st) ∧
    Toy.E.tok d.note.token = 5 ∧ d.note.amount = 3 ∧ Toy.E.addr d.recipient = 8 ∧
    Run (supOf Toy.E hist) (txs ++ [.withdraw d]) (d.post st) ∧
    Money (txs ++ [.withdraw d]) (d.post st) := by
  obtain ⟨txs, st, d, he, hrun, -, hdd, -, hprov, hg, hRp, -, ht, ha, hr, hrun', hmoney⟩ :=
    withdraw_journey_of_history hG0 hRB hEnv hD hTP hWP hA hC PathToy.hPF hinj hacc0 hx4
      hC1 hEx PathToy.hPT hcr hTransport
  exact ⟨txs, st, d, he, hrun, hdd, hprov, hg, hRp, ht, ha, hr, hrun', hmoney⟩

/-- The toy guard has content: at the toy pre-state the pool balance of the note's token is at
least 3 and the note is in the tree at the snapshot. Separately, evaluating the toy storage shows
the nullifier word 39 unspent before the call and spent after it. -/
theorem journey_toy_content : ∃ (st : St Toy.P) (d : WithdrawData Toy.P),
    d.guard st ∧ 3 ≤ st.balance d.note.token ∧ st.inTreeAt d.snapshot d.note.cm ∧
    σ2.nullifiers 39 = false ∧ σ3.nullifiers 39 = true := by
  obtain ⟨_, st, d, _, _, _, _, hg, _, _, ha, _, _, _⟩ := journey_toy
  exact ⟨st, d, hg, Nat.le_trans (Nat.le_of_eq ha.symm) hg.2.2.2.2.2.2, hg.2.1, by decide,
    by decide⟩

end LeanShieldedPool.Refine.JourneyToy
