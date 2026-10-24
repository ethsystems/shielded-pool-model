import Refinement.Rep

/-!
# Refinement premises

Each structure is a `Prop` whose fields are per-entry facts about the contract, the circuits or
the tree. Each field docstring names the row of the claim board
(`evidence/2026-10-13-claim-board/CLAIM1-board.md`) it stands for; the board gives the row's
evidence and status. None is an axiom: the refinement theorems take them as hypotheses.

Scope: every contract premise quantifies only over states reachable in the pinned deployment
(`Reach`), verification is indexed by the verifier address in storage, token calls and nested
callback calls are part of each successful execution, reverted calls have a rollback premise,
A2 enters as a per-history witness property, and the tree link is restricted to the history's
leaf prefixes and extracted input words.
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

/-- BN254 scalar field modulus (`ShieldedPool.sol:28`). -/
def pBN254 : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Every public input is a canonical field element. -/
def Canonical (x : List Nat) : Prop := ∀ y ∈ x, y < pBN254

/-- Accepting relations of the three circuits on (public-input vector, witness). The witness is
the model's operation data: the note, key and salt witnesses the circuit binds. -/
structure Circuits (P : PrimSpec) where
  deposit : List Nat → DepositData P → Prop
  transfer : List Nat → TransferData P → Prop
  withdraw : List Nat → WithdrawData P → Prop

/-- A witness extractor: one witness per public-input vector and circuit. -/
structure Extractor (P : PrimSpec) where
  deposit : List Nat → DepositData P
  transfer : List Nat → TransferData P
  withdraw : List Nat → WithdrawData P

/-! ## Deployment, rollback and environment -/

/-- **Constructor post, pinned deployment.** The constructor leaves every slot zero except
`verifier` (the pinned verifier, C1), `attestationRegistry` and `owner`
(`ShieldedPool.sol:102-111`). Board row C1. -/
def ConstructorPost (X : Contract) : Prop :=
  ∃ reg o, X.genesis = Storage.genesis X.pinnedVerifier reg o

/-- **Rollback.** A reverted top-level call from a reachable state leaves storage
unchanged. Board rows A11 (EVM execution including rollback) and X3. -/
def Rollback (X : Contract) : Prop :=
  ∀ {σ c σ'}, Reach X σ → X.Fail σ c σ' → σ' = σ

/-- **Environment premise: no owner call inside a token callback.** From a reachable state, no
successful top-level call contains a successful owner-only pool call made from a token callback.
The owner functions have no reentrancy guard (`ShieldedPool.sol:293`, `:303`, `:328`, `:336`), so
this is a deployment and environment condition (G1, X1), not a contract property. -/
def OwnerCallbackFree (X : Contract) : Prop :=
  ∀ {σ c tr σ'}, Reach X σ → X.Exec σ c tr σ' → ∀ c', Ext.nested c' ∈ tr → c'.isOwner = false

/-! ## Contract posts, on reachable states -/

/-- **Contract post for `deposit`.** -/
structure DepositPost (H : Nat → Nat → Nat) (X : Contract) : Prop where
  /-- D1: the token is supported (`:145`). -/
  supported : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' → σ.supportedTokens tok = true
  /-- D2: the amount is not zero (`:146`). -/
  amount_ne_zero : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' → amt ≠ 0
  /-- D5: the commitment is not in the tree (LeanIMT `LeafAlreadyExists`). -/
  fresh_leaf : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' → σ.leafIndex c = 0
  /-- S2 and S1: the verifier at the stored `verifier` address accepted the six inputs in ABI
  order, all canonical (`:153-166`). -/
  verified : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' →
    X.Verified σ.verifier .deposit [c, tok, amt, fund, att, pay] ∧
      Canonical [c, tok, amt, fund, att, pay]
  /-- X1: the reentrancy guard lets no nested `deposit`, `transfer` or `withdraw` succeed inside
  the token callback; any nested success is an owner call. -/
  guarded : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' → ∀ c', Ext.nested c' ∈ tr → c'.isOwner = true
  /-- D6 and X2: the only token call is `transferFrom(fund, pool, amt)` on `tok` (`:178`). -/
  token_calls : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' →
    tokenCalls tr = [.transferFrom tok fund X.self amt]
  /-- T13 (deposit part) and the storage frame: with no nested call, the storage after is
  exactly one insert and one ring record (`:169-170`). -/
  post : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' → (∀ c', Ext.nested c' ∉ tr) →
    σ' = depositStorage H σ c

/-- **Contract post for `transfer`.** -/
structure TransferPost (H : Nat → Nat → Nat) (X : Contract) : Prop where
  /-- T6 (`:196`). -/
  distinct : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' → n0 ≠ n1
  /-- T5 (`:200-201`). -/
  unspent : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' →
    σ.nullifiers n0 = false ∧ σ.nullifiers n1 = false
  /-- T1 (`:204`). -/
  known_root : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' → σ.isKnownRoot root
  /-- T11: both outputs new and different (LeanIMT reverts). -/
  fresh_outputs : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' →
    σ.leafIndex c0 = 0 ∧ σ.leafIndex c1 = 0 ∧ c0 ≠ c1
  /-- S2 and S1 (`:207-221`). -/
  verified : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' →
    X.Verified σ.verifier .transfer [n0, n1, c0, c1, root, pay] ∧
      Canonical [n0, n1, c0, c1, root, pay]
  /-- Transfer calls no token, so it has no external effect (board row X1: "transfer calls no
  token", a source reading). -/
  no_effects : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' → tr = []
  /-- T12, T13 and the storage frame: with no nested call, two flags, two inserts in calldata
  order, one ring record (`:225-232`). -/
  post : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' → (∀ c', Ext.nested c' ∉ tr) →
    σ' = transferStorage H σ n0 n1 c0 c1

/-- **Contract post for `withdraw`.** -/
structure WithdrawPost (X : Contract) : Prop where
  /-- W7 (`:255`). -/
  amount_ne_zero : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' → amt ≠ 0
  /-- W6, check half (`:260`). -/
  unspent : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' → σ.nullifiers nf = false
  /-- W1 (`:263`). -/
  known_root : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' → σ.isKnownRoot root
  /-- S2 and S1 (`:266-280`). -/
  verified : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' →
    X.Verified σ.verifier .withdraw [nf, tok, amt, rcpt, root] ∧
      Canonical [nf, tok, amt, rcpt, root]
  /-- X1: any nested success inside the token callback is an owner call. -/
  guarded : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' → ∀ c', Ext.nested c' ∈ tr → c'.isOwner = true
  /-- W10: the only token call is `transfer(rcpt, amt)` on `tok` (`:286`). -/
  token_calls : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' → tokenCalls tr = [.transfer tok rcpt amt]
  /-- W6, mark half, and the storage frame: with no nested call, one flag and nothing else
  (`:283`). -/
  post : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' → (∀ c', Ext.nested c' ∉ tr) →
    σ' = withdrawStorage σ nf

/-- **Admin stutter.** Each admin call writes only its own slot. `setVerifier` is excluded
by C1. Board row G1. -/
structure AdminStutter (X : Contract) : Prop where
  /-- G1, `addSupportedToken` (`:293`). -/
  add : ∀ {σ tok tr σ'}, Reach X σ → X.Exec σ (.addSupportedToken tok) tr σ' →
    σ' = { σ with supportedTokens := Function.update σ.supportedTokens tok true }
  /-- G1, `removeSupportedToken` (`:303`). -/
  remove : ∀ {σ tok tr σ'}, Reach X σ → X.Exec σ (.removeSupportedToken tok) tr σ' →
    σ' = { σ with supportedTokens := Function.update σ.supportedTokens tok false }
  /-- G1, `setAttestationRegistry` (`:328`). -/
  registry : ∀ {σ reg tr σ'}, Reach X σ → X.Exec σ (.setAttestationRegistry reg) tr σ' →
    σ' = { σ with attestationRegistry := reg }
  /-- G1, `transferOwnership` (`:336`). -/
  owner : ∀ {σ o tr σ'}, Reach X σ → X.Exec σ (.transferOwnership o) tr σ' →
    σ' = { σ with owner := o }

/-! ## Extracted operations and A2 -/

/-- Forget the model snapshot of a spend: `refine_run` chooses it from `Rep`, the extractor
does not supply it. `CryptoHyp` does not read it. -/
def eraseSnap : Tx P → Tx P
  | .deposit d => .deposit d
  | .transfer d => .transfer { d with snapshot := 0 }
  | .withdraw d => .withdraw { d with snapshot := 0 }

/-- The public-input vector the pool passes for a pool call (ABI order, S2). -/
def Call.inputs : Call → List Nat
  | .deposit _ c tok amt fund att pay => [c, tok, amt, fund, att, pay]
  | .transfer n0 n1 c0 c1 root pay => [n0, n1, c0, c1, root, pay]
  | .withdraw nf tok amt rcpt root => [nf, tok, amt, rcpt, root]
  | _ => []

/-- The extracted model operation of a pool call; none for an admin call. -/
def Call.txs (ext : Extractor P) : Call → List (Tx P)
  | .deposit _ c tok amt fund att pay => [.deposit (ext.deposit [c, tok, amt, fund, att, pay])]
  | .transfer n0 n1 c0 c1 root pay => [.transfer (ext.transfer [n0, n1, c0, c1, root, pay])]
  | .withdraw nf tok amt rcpt root => [.withdraw (ext.withdraw [nf, tok, amt, rcpt, root])]
  | _ => []

/-- The extracted operations of a history, snapshots erased. -/
def txsOf (ext : Extractor P) (h : List Call) : List (Tx P) :=
  (h.flatMap (Call.txs ext)).map eraseSnap

/-- Input commitment words of the extracted spends of `h`, ballast inputs included. -/
def inputWords (E : Enc P) (ext : Extractor P) (h : List Call) : List Nat :=
  (txsOf ext h).flatMap (fun tx => tx.consumes.map E.cm)

/-- The extractor's witness satisfies the circuit on this call's public inputs. -/
def Call.extractOK (C : Circuits P) (ext : Extractor P) : Call → Prop
  | .deposit _ c tok amt fund att pay =>
      C.deposit [c, tok, amt, fund, att, pay] (ext.deposit [c, tok, amt, fund, att, pay])
  | .transfer n0 n1 c0 c1 root pay =>
      C.transfer [n0, n1, c0, c1, root, pay] (ext.transfer [n0, n1, c0, c1, root, pay])
  | .withdraw nf tok amt rcpt root =>
      C.withdraw [nf, tok, amt, rcpt, root] (ext.withdraw [nf, tok, amt, rcpt, root])
  | _ => True

/-- **Per-history witness property (from A2; idealised).** For every successful pool call of
the history `h`, the extractor's witness satisfies the circuit on that call's public inputs.
This is the property the proof uses. It is not a formalisation of knowledge soundness: it has
no adversary, extraction algorithm or failure probability, and it asserts perfect extraction on
this history. It is idealised and stronger than the board's reading of A2 ("the deployed proof
system is sound and knowledge-sound for the accepted spends"), which is computational. Board
row A2. -/
def ExtractedWitnesses (C : Circuits P) (ext : Extractor P) (h : List Call) : Prop :=
  ∀ c ∈ h, c.extractOK C ext

/-- **Global ideal extraction for the pinned verifier (idealised).** Every canonical input
vector the pinned verifier accepts has the extractor's witness in the circuit. Stronger than
`ExtractedWitnesses`: it quantifies over all vectors, not the history's. Used only to show
`ExtractedWitnesses` follows from it and the `verified` post fields
(`extractedWitnesses_of_ideal`). Board row A2. -/
structure IdealExtraction (X : Contract) (C : Circuits P) (ext : Extractor P) : Prop where
  deposit : ∀ x, X.Verified X.pinnedVerifier .deposit x → Canonical x → C.deposit x (ext.deposit x)
  transfer : ∀ x, X.Verified X.pinnedVerifier .transfer x → Canonical x →
    C.transfer x (ext.transfer x)
  withdraw : ∀ x, X.Verified X.pinnedVerifier .withdraw x → Canonical x →
    C.withdraw x (ext.withdraw x)

/-! ## Circuit facts -/

/-- **Circuit facts**, stated on the public-input vector. `Incl leaf root` is the circuit's
Merkle relation (`binary_merkle_root` with some path returns `root`; `foldRoot`). Each field is
discharged by citation of a separate package (`circuits-lampe/` or `circuits-acir/` in this
repository), not by import; it reaches the
deployed verifier only through S2, S3 and C1, A4 for source-level rows and A11 for bb. -/
structure CircuitFacts (E : Enc P) (C : Circuits P) (Incl : Nat → Nat → Prop) : Prop where
  /-- The deposit amount is below 2^128 (the board's deposit amount row), circuit half. -/
  d_amount : ∀ x d, C.deposit x d → d.note.amount < 2 ^ 128
  /-- D4: the public commitment encodes exactly the public token and amount. -/
  d_commitment : ∀ x d, C.deposit x d →
    x.getD 0 0 = E.cm d.note.cm ∧ x.getD 1 0 = E.tok d.note.token ∧ x.getD 2 0 = d.note.amount
  /-- D6, circuit side: the witness funding address is public input 3. The circuit leaves it
  unconstrained, so this holds by the extraction reading of the public input (spec section 5.3). -/
  d_funding : ∀ x d, C.deposit x d → x.getD 3 0 = E.addr d.funding
  /-- T2. -/
  t_owner : ∀ x d, C.transfer x d → d.in1.ownedBy d.key ∧ d.in2.ownedBy d.key
  /-- T3: input 0 is always a member; input 1 is a member unless it is ballast (spec sections 4.2
  and 5.3). -/
  t_member : ∀ x d, C.transfer x d →
    Incl (E.cm d.in1.cm) (x.getD 4 0) ∧
    (d.in2.isBallast ∨ Incl (E.cm d.in2.cm) (x.getD 4 0))
  /-- T4. -/
  t_nullifiers : ∀ x d, C.transfer x d → x.getD 0 0 = E.nf d.nf1 ∧ x.getD 1 0 = E.nf d.nf2
  /-- T7. -/
  t_tokens : ∀ x d, C.transfer x d →
    d.in2.token = d.in1.token ∧ d.out1.token = d.in1.token ∧ d.out2.token = d.in1.token
  /-- T8. -/
  t_ranges : ∀ x d, C.transfer x d →
    U128 d.in1.amount ∧ U128 d.in2.amount ∧ U128 d.out1.amount ∧ U128 d.out2.amount
  /-- T9. -/
  t_conservation : ∀ x d, C.transfer x d →
    d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount
  /-- T10. -/
  t_outputs : ∀ x d, C.transfer x d → x.getD 2 0 = E.cm d.out1.cm ∧ x.getD 3 0 = E.cm d.out2.cm
  /-- W2. -/
  w_member : ∀ x d, C.withdraw x d → Incl (E.cm d.note.cm) (x.getD 4 0)
  /-- W3. -/
  w_owner : ∀ x d, C.withdraw x d → d.note.ownedBy d.key
  /-- W4. -/
  w_nullifier : ∀ x d, C.withdraw x d → x.getD 0 0 = E.nf d.nf
  /-- W5. -/
  w_public : ∀ x d, C.withdraw x d → x.getD 1 0 = E.tok d.note.token ∧ x.getD 2 0 = d.note.amount
  /-- W10, circuit side: the witness recipient is public input 3 (unconstrained in-circuit,
  bound by the proof, A2). -/
  w_recipient : ∀ x d, C.withdraw x d → x.getD 3 0 = E.addr d.recipient
  /-- W8, circuit half. -/
  w_amount : ∀ x d, C.withdraw x d → U128 d.note.amount

/-! ## Tree link, restricted to the history -/

/-- **Tree link, reduction form, restricted.** For every prefix `L` of the history's
leaf list `G` and every nonzero extracted input word `leaf ∈ W`: if the circuit's Merkle relation
takes `leaf` to the LeanIMT root of `L`, then `leaf ∈ L` or the bad event `Coll L leaf` holds.
The zero word is excluded: the real fold at depth 0 returns its leaf, so `Incl 0 0` holds and
`rootOf H [] = 0` (`global_treeLink_inconsistent`). `depth0_treeLink` proves this
restricted form for the depth-0 fold and every hash. `Coll` is a parameter: its intended
instance is a PoseidonT3 collision, leaf and node confusion or a zero output among the path and
tree nodes. A choice such as `Coll L leaf := leaf ∉ L` makes the reduction trivial and moves the
whole obligation into `TreeHyp.no_bad`. Board rows A9a and A9b. -/
structure TreeLink (H : Nat → Nat → Nat) (Incl : Nat → Nat → Prop)
    (Coll : List Nat → Nat → Prop) (G W : List Nat) : Prop where
  reduction : ∀ L, L <+: G → ∀ leaf ∈ W, leaf ≠ 0 → Incl leaf (rootOf H L) → leaf ∈ L ∨ Coll L leaf

/-- **Tree premise per history (idealised crypto premise, scoped like `CryptoHyp`).** The extracted input
words are nonzero (no Poseidon4 output 0 among the run's inputs), and no bad event occurs for
the history's leaf prefixes and extracted input words. Board rows A9a, A9b and A1. -/
structure TreeHyp (Coll : List Nat → Nat → Prop) (G W : List Nat) : Prop where
  nonzero : ∀ leaf ∈ W, leaf ≠ 0
  no_bad : ∀ L, L <+: G → ∀ leaf ∈ W, ¬ Coll L leaf

theorem tree_member {H : Nat → Nat → Nat} {Incl : Nat → Nat → Prop}
    {Coll : List Nat → Nat → Prop} {G W : List Nat} (hTL : TreeLink H Incl Coll G W)
    (hTH : TreeHyp Coll G W) {L : List Nat} {leaf : Nat} (hL : L <+: G) (hw : leaf ∈ W)
    (hi : Incl leaf (rootOf H L)) : leaf ∈ L :=
  (hTL.reduction L hL leaf hw (hTH.nonzero leaf hw) hi).resolve_right (hTH.no_bad L hL leaf hw)

/-- The circuit's Merkle relation at depth 0: the fold returns the leaf. -/
def Incl0 (H : Nat → Nat → Nat) (leaf root : Nat) : Prop := foldRoot H leaf [] = root

/-- Leaf and node confusion: `leaf` equals the LeanIMT root of a prefix of `L` with at least
two leaves, which is a PoseidonT3 output. -/
def Coll0 (H : Nat → Nat → Nat) (L : List Nat) (leaf : Nat) : Prop :=
  ∃ n, 2 ≤ n ∧ n ≤ L.length ∧ leaf = rootOf H (L.take n)

/-- **Consistency check for the tree link.** The restricted tree link holds for the real fold at
depth 0, for every hash, every leaf list and every word list, with the concrete bad event
`Coll0`. -/
theorem depth0_treeLink (H : Nat → Nat → Nat) (G W : List Nat) :
    TreeLink H (Incl0 H) (Coll0 H) G W where
  reduction := fun L _ leaf _ hne hin => by
    have hl : leaf = rootOf H L := hin
    rcases L with _ | ⟨a, _ | ⟨b, t⟩⟩
    · exact absurd (hl.trans (rootOf_nil H)) hne
    · left
      rw [hl, rootOf_singleton]
      exact List.mem_singleton_self a
    · right
      refine ⟨(a :: b :: t).length, ?_, Nat.le_refl _, ?_⟩
      · simp only [List.length_cons]
        omega
      · rw [List.take_of_length_le (Nat.le_refl _)]
        exact hl

/-- **An unrestricted tree link is inconsistent with the depth-0 fold.** Any `Coll` that makes
the unrestricted reduction hold for `Incl0` must hold somewhere, so the premise pair (global
reduction and `∀ L leaf, ¬ Coll L leaf`) has no model with the real fold. This is why the tree
link above excludes the zero word and is restricted to the history. -/
theorem global_treeLink_inconsistent (H : Nat → Nat → Nat) (Coll : List Nat → Nat → Prop)
    (hred : ∀ L leaf, Incl0 H leaf (rootOf H L) → leaf ∈ L ∨ Coll L leaf)
    (hNC : ∀ L leaf, ¬ Coll L leaf) : False := by
  rcases hred [] 0 rfl with h | h
  · exact List.not_mem_nil h
  · exact hNC [] 0 h

end LeanShieldedPool.Refine
