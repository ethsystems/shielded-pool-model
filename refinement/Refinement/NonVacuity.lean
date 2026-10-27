import Refinement.Cases

/-!
# Refinement: non-vacuity and controls

1. `ToyRun`: every premise of `refine_run` holds for a toy pool on the history
   `[addSupportedToken 5, deposit 9, transfer (9 and ballast in, 39 and zero out), withdraw 39]`,
   with a reverted `setVerifier` call after the first call (rollback). The transfer spends the
   deposited note against the recorded root 9 and the withdraw spends the transfer's first output
   against the current root 96, both through the toy Merkle relation `InclT` (membership in a
   prefix of the toy leaves `[9, 39, 46]` with that LeanIMT root), so positive tree membership
   for input 0 (the model's transfer guard asks it), `withdraw_balance` and every case of the
   induction run. The real depth-0
   fold `Incl0` admits only the first leaf (a one-leaf tree's root is its leaf), too few for a
   member first transfer input and a withdraw of a different note; `depth0_treeLink` remains
   the consistency check of the tree link for the real fold. The tree link for `InclT` holds because the
   prefix roots `0, 9, 49, 96` are distinct (`hTL`), with the concrete bad event `Coll0`, and
   `TreeHyp` holds: no bad event occurs. `CryptoHyp` on the extracted operations holds, so the
   conclusion holds outright. A2 enters through `extractedWitnesses_of_ideal`.
2. Controls: `repCore_no_window_inclusion` (Rep without `valid` loses the window inclusion),
   `treeLink_needs_nonzero` (without the nonzero-leaf restriction the depth-0 fold breaks the
   tree link), `global_treeLink_inconsistent` (in `Post.lean`), `existential_shape_trivial`.

The toy verifier accepts only fixed witnesses. The instance shows the premises are jointly
satisfiable; it says nothing about the deployed pool.
-/

namespace LeanShieldedPool.Refine.Toy

open LeanShieldedPool LeanShieldedPool.Refine

/-- Toy primitives over `Nat`. -/
def P : PrimSpec where
  Token := Nat
  Address := Nat
  PubKey := Nat
  SpendKey := Nat
  Salt := Nat
  Commitment := Nat
  Nullifier := Nat
  derivePub := id
  commit := fun t a o s => t + a + o + s + 1
  nullify := fun c k => c + k

def E : Enc P := ⟨id, id, id, id⟩

/-- Toy PoseidonT3. -/
def H : Nat → Nat → Nat := fun a b => a + b + 1

/-- The note behind leaf 9: token 5, amount 3, owner 0, salt 0; funding address 7. -/
def d1 : DepositData P := ⟨⟨(5 : Nat), 3, (0 : Nat), (0 : Nat)⟩, (7 : Nat)⟩

/-- **Statement-shape control.** With a commitment collision, `∃ txs st, CryptoHyp P txs → Q`
is provable for every `Q`. This is why `refine_run` fixes `txs` to `txsOf ext h`. -/
theorem existential_shape_trivial (Q : List (Tx P) → St P → Prop) :
    ∃ txs st, CryptoHyp P txs → Q txs st := by
  let a : DepositData P := ⟨⟨(5 : Nat), 3, (0 : Nat), (0 : Nat)⟩, (0 : Nat)⟩
  let b : DepositData P := ⟨⟨(4 : Nat), 4, (0 : Nat), (0 : Nat)⟩, (0 : Nat)⟩
  refine ⟨[.deposit a, .deposit b], St.empty P (fun _ => True), fun hc => ?_⟩
  have hab := hc.commit_inj a.note (by simp only [runNotes, List.flatMap_cons, Tx.notes,
      List.mem_append, List.mem_cons, true_or]) b.note (by simp only [runNotes,
      List.flatMap_cons, Tx.notes, List.mem_append, List.mem_cons, true_or, or_true])
    (show (3 : Nat) ≤ 2 ^ 128 - 1 by decide) (show (4 : Nat) ≤ 2 ^ 128 - 1 by decide) rfl
  exact absurd (congrArg Note.amount hab) (by decide)

/-- A storage that `RepCore` accepts for the empty pool but whose valid-roots map accepts every
root. -/
def σbad : Storage := { Storage.genesis 1 2 3 with validRoots := fun _ => true }

/-- **Mutation control.** Dropping the valid-roots field from `Rep` breaks the window
inclusion. -/
theorem repCore_no_window_inclusion :
    RepCore H E (fun _ => True) [] σbad (St.empty P (fun _ => True)) ∧ σbad.isKnownRoot 5 ∧
      ¬ ∃ n ∈ (St.empty P (fun _ => True)).window,
        (5 : Nat) = rootOf H (([] : List Nat).take n) := by
  have g := (rep_genesis H E (fun _ => True) 1 2 3).toRepCore
  refine ⟨⟨g.leaves, g.tree, g.leafIndex, g.nullifiers, g.supported, g.supported_eq,
    g.ringIndex_lt, g.ring, g.head, g.window_le⟩, Or.inr rfl, ?_⟩
  rintro ⟨n, hn, h5⟩
  have hn0 : n = 0 := List.mem_singleton.1 hn
  rw [hn0] at h5
  exact absurd h5 (by decide)

/-- **Mutation control for the tree link.** Without the nonzero-leaf restriction the tree link fails for
the real depth-0 fold, even with the concrete bad event: leaf 0 at the empty prefix. -/
theorem treeLink_needs_nonzero :
    ¬ ∀ L, L <+: ([] : List Nat) → ∀ leaf ∈ [(0 : Nat)],
      Incl0 H leaf (rootOf H L) → leaf ∈ L ∨ Coll0 H L leaf := by
  intro hall
  rcases hall [] (List.prefix_refl _) 0 (List.mem_singleton_self 0) rfl with h | ⟨n, h2, hn, _⟩
  · exact List.not_mem_nil h
  · simp only [List.length_nil] at hn
    omega

end LeanShieldedPool.Refine.Toy

namespace LeanShieldedPool.Refine.ToyRun

open LeanShieldedPool LeanShieldedPool.Refine

theorem rootsNonzero_of_take {H : Nat → Nat → Nat} {h : List Call}
    (hk : ∀ k, k ≤ (ghostLeaves h).length → 0 < k → rootOf H ((ghostLeaves h).take k) ≠ 0) :
    RootsNonzero H h := by
  intro h₁ c h₂ he hc
  have hp : ghostLeaves (h₁ ++ [c]) <+: ghostLeaves h := by
    rw [he, show h₁ ++ c :: h₂ = (h₁ ++ [c]) ++ h₂ by
      simp only [List.append_assoc, List.singleton_append]]
    exact ghostLeaves_prefix (List.prefix_append _ _)
  have hne : ghostLeaves (h₁ ++ [c]) ≠ [] := by
    rw [ghostLeaves_snoc]
    intro h0
    exact hc (List.append_eq_nil_iff.1 h0).2
  rw [List.prefix_iff_eq_take.1 hp]
  exact hk _ hp.length_le (List.length_pos_of_ne_nil hne)

theorem no_bad_of_take {H : Nat → Nat → Nat} {G W : List Nat}
    (hk : ∀ n, n ≤ G.length → 2 ≤ n → ∀ leaf ∈ W, leaf ≠ rootOf H (G.take n)) :
    ∀ L, L <+: G → ∀ leaf ∈ W, ¬ Coll0 H L leaf := by
  rintro L hL leaf hw ⟨n, h2, hn, he⟩
  have hlen : L.length ≤ G.length := hL.length_le
  have hLe : L = G.take L.length := List.prefix_iff_eq_take.1 hL
  have ht : L.take n = G.take n := by
    rw [hLe, List.take_take]
    congr 1
    omega
  exact hk n (by omega) h2 leaf hw (he.trans (congrArg (rootOf H) ht))

/-- The toy history's leaves: the deposit's commitment and the transfer's two outputs. -/
def leavesT : List Nat := [9, 39, 46]

/-- Toy Merkle relation: `leaf` is a leaf of a prefix of `leavesT` whose LeanIMT root is
`root`. It stands in for the circuit's Merkle check (`Incl`); see the module header for why the
real depth-0 fold `Incl0` cannot serve here. -/
def InclT (leaf root : Nat) : Prop :=
  ∃ n, n ≤ leavesT.length ∧ root = rootOf Toy.H (leavesT.take n) ∧ leaf ∈ leavesT.take n

/-- Toy circuits: every `CircuitFacts` field. The transfer's first input and the withdraw note are members
under `InclT`; the transfer's second input is ballast. -/
def C : Circuits Toy.P where
  deposit := fun x d =>
    x.getD 0 0 = Toy.E.cm d.note.cm ∧ x.getD 1 0 = Toy.E.tok d.note.token ∧
      x.getD 2 0 = d.note.amount ∧ x.getD 3 0 = Toy.E.addr d.funding ∧ d.note.amount < 2 ^ 128
  transfer := fun x d =>
    x.getD 0 0 = Toy.E.nf d.nf1 ∧ x.getD 1 0 = Toy.E.nf d.nf2 ∧
    x.getD 2 0 = Toy.E.cm d.out1.cm ∧ x.getD 3 0 = Toy.E.cm d.out2.cm ∧
    d.in1.ownedBy d.key ∧ d.in2.ownedBy d.key ∧ InclT (Toy.E.cm d.in1.cm) (x.getD 4 0) ∧
    d.in2.isBallast ∧
    d.in2.token = d.in1.token ∧ d.out1.token = d.in1.token ∧ d.out2.token = d.in1.token ∧
    U128 d.in1.amount ∧ U128 d.in2.amount ∧ U128 d.out1.amount ∧ U128 d.out2.amount ∧
    d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount
  withdraw := fun x d =>
    x.getD 0 0 = Toy.E.nf d.nf ∧ x.getD 1 0 = Toy.E.tok d.note.token ∧
    x.getD 2 0 = d.note.amount ∧ x.getD 3 0 = Toy.E.addr d.recipient ∧
    InclT (Toy.E.cm d.note.cm) (x.getD 4 0) ∧ d.note.ownedBy d.key ∧ U128 d.note.amount

/-- Spend the deposited note (commitment 9) and a ballast note (salt 20), create a 3-unit note
(salt 30) and a zero note (salt 40); key 0: commitments 9, 26, 39, 46; nullifiers 9, 26. -/
def dT : TransferData Toy.P where
  key := (0 : Nat)
  in1 := Toy.d1.note
  in2 := ⟨(5 : Nat), 0, (0 : Nat), (20 : Nat)⟩
  out1 := ⟨(5 : Nat), 3, (0 : Nat), (30 : Nat)⟩
  out2 := ⟨(5 : Nat), 0, (0 : Nat), (40 : Nat)⟩
  snapshot := 0

/-- Withdraw of the transfer's first output (commitment 39, key 0, nullifier 39) to recipient
8. -/
def dW : WithdrawData Toy.P := ⟨(0 : Nat), dT.out1, (8 : Nat), 0⟩

/-- Toy extractor: fixed witnesses. -/
def ext : Extractor Toy.P := ⟨fun _ => Toy.d1, fun _ => dT, fun _ => dW⟩

/-- Toy verifier at address 1; it accepts only the fixed witnesses. -/
def Ver : Nat → Circuit → List Nat → Prop
  | v, .deposit, x => v = 1 ∧ C.deposit x Toy.d1
  | v, .transfer, x => v = 1 ∧ C.transfer x dT
  | v, .withdraw, x => v = 1 ∧ C.withdraw x dW

def Ex : Storage → Call → List Ext → Storage → Prop
  | σ, .deposit _ c tok amt fund att pay, tr, σ' =>
      σ.supportedTokens tok = true ∧ amt ≠ 0 ∧ σ.leafIndex c = 0 ∧
      Ver σ.verifier .deposit [c, tok, amt, fund, att, pay] ∧
      Canonical [c, tok, amt, fund, att, pay] ∧
      tr = [.transferFrom tok fund 99 amt] ∧ σ' = depositStorage Toy.H σ c
  | σ, .transfer n0 n1 c0 c1 root pay, tr, σ' =>
      n0 ≠ n1 ∧ σ.nullifiers n0 = false ∧ σ.nullifiers n1 = false ∧ σ.isKnownRoot root ∧
      σ.leafIndex c0 = 0 ∧ σ.leafIndex c1 = 0 ∧ c0 ≠ c1 ∧
      Ver σ.verifier .transfer [n0, n1, c0, c1, root, pay] ∧
      Canonical [n0, n1, c0, c1, root, pay] ∧ tr = [] ∧ σ' = transferStorage Toy.H σ n0 n1 c0 c1
  | σ, .withdraw nf tok amt rcpt root, tr, σ' =>
      amt ≠ 0 ∧ σ.nullifiers nf = false ∧ σ.isKnownRoot root ∧
      Ver σ.verifier .withdraw [nf, tok, amt, rcpt, root] ∧ Canonical [nf, tok, amt, rcpt, root] ∧
      tr = [.transfer tok rcpt amt] ∧ σ' = withdrawStorage σ nf
  | σ, .addSupportedToken tok, tr, σ' =>
      tr = [] ∧ σ' = { σ with supportedTokens := Function.update σ.supportedTokens tok true }
  | σ, .removeSupportedToken tok, tr, σ' =>
      tr = [] ∧ σ' = { σ with supportedTokens := Function.update σ.supportedTokens tok false }
  | σ, .setAttestationRegistry reg, tr, σ' => tr = [] ∧ σ' = { σ with attestationRegistry := reg }
  | σ, .transferOwnership o, tr, σ' => tr = [] ∧ σ' = { σ with owner := o }
  | _, .setVerifier _, _, _ => False

/-- Toy pool: self address 99, pinned verifier 1, every revert rolls back. -/
def X : Contract where
  Exec := Ex
  Fail := fun σ _ σ' => σ' = σ
  Verified := Ver
  self := 99
  pinnedVerifier := 1
  genesis := Storage.genesis 1 2 3

theorem hG0 : ConstructorPost X := ⟨2, 3, rfl⟩

theorem hRB : Rollback X := by
  intro σ c σ' _ h
  exact h

theorem hEnv : OwnerCallbackFree X := by
  intro σ c tr σ' _ hx c' hc'
  exfalso
  cases c with
  | deposit s cm tok amt fund att pay =>
    obtain ⟨-, -, -, -, -, htr, -⟩ := hx
    rw [htr] at hc'
    cases List.mem_singleton.1 hc'
  | transfer n0 n1 c0 c1 root pay =>
    obtain ⟨-, -, -, -, -, -, -, -, -, htr, -⟩ := hx
    rw [htr] at hc'
    exact List.not_mem_nil hc'
  | withdraw nf tok amt rcpt root =>
    obtain ⟨-, -, -, -, -, htr, -⟩ := hx
    rw [htr] at hc'
    cases List.mem_singleton.1 hc'
  | addSupportedToken tok =>
    obtain ⟨htr, -⟩ := hx
    rw [htr] at hc'
    exact List.not_mem_nil hc'
  | removeSupportedToken tok =>
    obtain ⟨htr, -⟩ := hx
    rw [htr] at hc'
    exact List.not_mem_nil hc'
  | setAttestationRegistry reg =>
    obtain ⟨htr, -⟩ := hx
    rw [htr] at hc'
    exact List.not_mem_nil hc'
  | transferOwnership o =>
    obtain ⟨htr, -⟩ := hx
    rw [htr] at hc'
    exact List.not_mem_nil hc'
  | setVerifier v => exact hx

theorem hD : DepositPost Toy.H X where
  supported := fun _ hx => by obtain ⟨h, -⟩ := hx; exact h
  amount_ne_zero := fun _ hx => by obtain ⟨-, h, -⟩ := hx; exact h
  fresh_leaf := fun _ hx => by obtain ⟨-, -, h, -⟩ := hx; exact h
  verified := fun _ hx => by obtain ⟨-, -, -, h1, h2, -⟩ := hx; exact ⟨h1, h2⟩
  guarded := fun _ hx c' hc' => by
    obtain ⟨-, -, -, -, -, htr, -⟩ := hx
    rw [htr] at hc'
    cases List.mem_singleton.1 hc'
  token_calls := fun _ hx => by
    obtain ⟨-, -, -, -, -, htr, -⟩ := hx
    rw [htr]
    rfl
  post := fun _ hx _ => by obtain ⟨-, -, -, -, -, -, h⟩ := hx; exact h

theorem hTP : TransferPost Toy.H X where
  distinct := fun _ hx => by obtain ⟨h, -⟩ := hx; exact h
  unspent := fun _ hx => by obtain ⟨-, h1, h2, -⟩ := hx; exact ⟨h1, h2⟩
  known_root := fun _ hx => by obtain ⟨-, -, -, h, -⟩ := hx; exact h
  fresh_outputs := fun _ hx => by obtain ⟨-, -, -, -, h1, h2, h3, -⟩ := hx; exact ⟨h1, h2, h3⟩
  verified := fun _ hx => by obtain ⟨-, -, -, -, -, -, -, h1, h2, -⟩ := hx; exact ⟨h1, h2⟩
  no_effects := fun _ hx => by obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := hx; exact h
  post := fun _ hx _ => by obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := hx; exact h

theorem hWP : WithdrawPost X where
  amount_ne_zero := fun _ hx => by obtain ⟨h, -⟩ := hx; exact h
  unspent := fun _ hx => by obtain ⟨-, h, -⟩ := hx; exact h
  known_root := fun _ hx => by obtain ⟨-, -, h, -⟩ := hx; exact h
  verified := fun _ hx => by obtain ⟨-, -, -, h1, h2, -⟩ := hx; exact ⟨h1, h2⟩
  guarded := fun _ hx c' hc' => by
    obtain ⟨-, -, -, -, -, htr, -⟩ := hx
    rw [htr] at hc'
    cases List.mem_singleton.1 hc'
  token_calls := fun _ hx => by
    obtain ⟨-, -, -, -, -, htr, -⟩ := hx
    rw [htr]
    rfl
  post := fun _ hx _ => by obtain ⟨-, -, -, -, -, -, h⟩ := hx; exact h

theorem hA : AdminStutter X where
  add := fun _ hx => by obtain ⟨-, h⟩ := hx; exact h
  remove := fun _ hx => by obtain ⟨-, h⟩ := hx; exact h
  registry := fun _ hx => by obtain ⟨-, h⟩ := hx; exact h
  owner := fun _ hx => by obtain ⟨-, h⟩ := hx; exact h

theorem hIdeal : IdealExtraction X C ext where
  deposit := fun _ hv _ => by obtain ⟨-, h⟩ := hv; exact h
  transfer := fun _ hv _ => by obtain ⟨-, h⟩ := hv; exact h
  withdraw := fun _ hv _ => by obtain ⟨-, h⟩ := hv; exact h

theorem hC : CircuitFacts Toy.E C InclT where
  d_amount := fun _ _ hd => by obtain ⟨-, -, -, -, h⟩ := hd; exact h
  d_commitment := fun _ _ hd => by obtain ⟨h1, h2, h3, -⟩ := hd; exact ⟨h1, h2, h3⟩
  d_funding := fun _ _ hd => by obtain ⟨-, -, -, h, -⟩ := hd; exact h
  t_owner := fun _ _ hd => by obtain ⟨-, -, -, -, h1, h2, -⟩ := hd; exact ⟨h1, h2⟩
  t_member := fun _ _ hd => by
    obtain ⟨-, -, -, -, -, -, h1, h2, -⟩ := hd; exact ⟨h1, Or.inl h2⟩
  t_nullifiers := fun _ _ hd => by obtain ⟨h1, h2, -⟩ := hd; exact ⟨h1, h2⟩
  t_tokens := fun _ _ hd => by
    obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, -⟩ := hd; exact ⟨h1, h2, h3⟩
  t_ranges := fun _ _ hd => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, h3, h4, -⟩ := hd; exact ⟨h1, h2, h3, h4⟩
  t_conservation := fun _ _ hd => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := hd; exact h
  t_outputs := fun _ _ hd => by obtain ⟨-, -, h1, h2, -⟩ := hd; exact ⟨h1, h2⟩
  w_member := fun _ _ hd => by obtain ⟨-, -, -, -, h, -⟩ := hd; exact h
  w_owner := fun _ _ hd => by obtain ⟨-, -, -, -, -, h, -⟩ := hd; exact h
  w_nullifier := fun _ _ hd => by obtain ⟨h, -⟩ := hd; exact h
  w_public := fun _ _ hd => by obtain ⟨-, h1, h2, -⟩ := hd; exact ⟨h1, h2⟩
  w_recipient := fun _ _ hd => by obtain ⟨-, -, -, h, -⟩ := hd; exact h
  w_amount := fun _ _ hd => by obtain ⟨-, -, -, -, -, -, h⟩ := hd; exact h

theorem hinj : Function.Injective Toy.E.cm := fun _ _ h => h

def hist : List Call :=
  [.addSupportedToken 5, .deposit 7 9 5 3 7 0 0, .transfer 9 26 39 46 9 0, .withdraw 39 5 3 8 96]

def σa : Storage :=
  { Storage.genesis 1 2 3 with
    supportedTokens := Function.update (Storage.genesis 1 2 3).supportedTokens 5 true }

def σ1 : Storage := depositStorage Toy.H σa 9
def σ2 : Storage := transferStorage Toy.H σ1 9 26 39 46
def σ3 : Storage := withdrawStorage σ2 39

theorem hacc : Accepted X hist σ3 := by
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
  have e4 : X.Exec σ2 (.withdraw 39 5 3 8 96) [.transfer 5 8 3] σ3 :=
    ⟨by decide, by decide, Or.inl (by decide),
      ⟨rfl, rfl, rfl, rfl, rfl, ⟨3, by decide, by decide, by decide⟩, rfl,
        by show (3 : Nat) ≤ 2 ^ 128 - 1; decide⟩,
      by unfold Canonical; decide, rfl, rfl⟩
  have a1 : Accepted X ([] ++ [Call.addSupportedToken 5]) σa := Accepted.snoc Accepted.nil e1
  have a1' : Accepted X ([] ++ [Call.addSupportedToken 5]) σa :=
    Accepted.fail (c := .setVerifier 0) a1 rfl
  exact Accepted.snoc (Accepted.snoc (Accepted.snoc a1' e2) e3) e4

theorem hC1 : NoSetVerifier hist := by
  intro c hc v
  simp only [hist, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> intro he <;> cases he

/-- A2 per history, from global ideal extraction through the pinned-verifier bridge. -/
theorem hEx : ExtractedWitnesses C ext hist :=
  extractedWitnesses_of_ideal hG0 hRB hEnv hD hTP hWP hA hIdeal hacc hC1

/-- The tree link for `InclT`: the prefix roots of `leavesT` are distinct, so a root fixes its
prefix and an included leaf is a leaf of that prefix. The bad event is never needed. -/
theorem hTL : TreeLink Toy.H InclT (Coll0 Toy.H) (ghostLeaves hist) (inputWords Toy.E ext hist) where
  reduction := fun L hL leaf _ _ hi => by
    obtain ⟨n, hn, hr, hm⟩ := hi
    have hG : ghostLeaves hist = leavesT := rfl
    rw [hG] at hL
    have hLe : L = leavesT.take L.length := List.prefix_iff_eq_take.1 hL
    have hlen : L.length ≤ leavesT.length := hL.length_le
    have key : ∀ m, m ≤ leavesT.length → ∀ k, k ≤ leavesT.length →
        rootOf Toy.H (leavesT.take m) = rootOf Toy.H (leavesT.take k) →
          leavesT.take m = leavesT.take k := by decide
    have heq : L = leavesT.take n :=
      hLe.trans (key _ hlen n hn (by rw [← hLe]; exact hr))
    left
    rw [heq]
    exact hm

/-- No bad event: the input words 9, 26, 39 are nonzero and none is a root of a two- or
three-leaf prefix of `[9, 39, 46]` (those roots are 49 and 96). -/
theorem hTH : TreeHyp (Coll0 Toy.H) (ghostLeaves hist) (inputWords Toy.E ext hist) :=
  ⟨by decide, no_bad_of_take (by decide)⟩

theorem hZ : RootsNonzero Toy.H hist := rootsNonzero_of_take (by decide)

/-- `CryptoHyp` holds for the extracted operations: four distinct notes (commitments 9, 26,
39, 46; the transfer spends the deposit's note, the withdraw the transfer's first output) and
the single key 0. -/
theorem hcr : CryptoHyp Toy.P (txsOf ext hist) := by
  have e : runNotes (txsOf ext hist) =
      [Toy.d1.note, Toy.d1.note, dT.in2, dT.out1, dT.out2, dT.out1] := rfl
  have hn : ([Toy.d1.note, dT.in2, dT.out1, dT.out2].map Note.cm).Nodup := by
    show ([9, 26, 39, 46] : List Nat).Nodup
    decide
  have hsub : ∀ n ∈ runNotes (txsOf ext hist),
      n ∈ [Toy.d1.note, dT.in2, dT.out1, dT.out2] := by
    intro n hm
    rw [e] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  refine ⟨fun n h1 n' h2 _ _ he => List.inj_on_of_nodup_map hn (hsub n h1) (hsub n' h2) he,
    fun k h1 k' h2 _ => ?_⟩
  have ek : runKeys (txsOf ext hist) = [(0 : Nat), (0 : Nat)] := rfl
  have hk0 : ∀ x ∈ runKeys (txsOf ext hist), x = (0 : Nat) := by
    intro x hx
    rw [ek] at hx
    rcases List.mem_cons.1 hx with h | h
    · exact h
    · exact List.mem_singleton.1 h
  rw [hk0 k h1, hk0 k' h2]

/-- **Non-vacuity.** `refine_run` with every premise instantiated, on a history with an
admin call, a reverted call, a deposit, a transfer and a withdraw. The conclusion holds
outright. -/
theorem refine_run_toy : ∃ txs st, txs.map eraseSnap = txsOf ext hist ∧
    Run (supOf Toy.E hist) txs st ∧ Rep Toy.H Toy.E (supOf Toy.E hist) (ghostLeaves hist) σ3 st :=
  refine_run hG0 hRB hEnv hD hTP hWP hA hC hinj hacc hC1 hEx hTL hTH hZ hcr

/-- The model state holds the leaves 9, 39, 46 in order, and nullifier 39 of the withdraw. -/
theorem toy_state : ∃ st : St Toy.P,
    st.leaves.map Toy.E.cm = [9, 39, 46] ∧ (39 : Nat) ∈ st.nullifiers.map Toy.E.nf := by
  obtain ⟨_, st, _, _, hR⟩ := refine_run_toy
  exact ⟨st, hR.leaves, (hR.nullifiers 39).1 (by decide)⟩

end LeanShieldedPool.Refine.ToyRun

/-! Axiom census. -/
#print axioms LeanShieldedPool.Refine.refine_run
#print axioms LeanShieldedPool.Refine.refine_inv
#print axioms LeanShieldedPool.Refine.reach_verifier
#print axioms LeanShieldedPool.Refine.extractedWitnesses_of_ideal
#print axioms LeanShieldedPool.Refine.deposit_token_binding
#print axioms LeanShieldedPool.Refine.withdraw_token_binding
#print axioms LeanShieldedPool.Refine.depth0_treeLink
#print axioms LeanShieldedPool.Refine.global_treeLink_inconsistent
#print axioms LeanShieldedPool.Refine.rep_genesis
#print axioms LeanShieldedPool.Refine.Rep.known_root_in_window
#print axioms LeanShieldedPool.Refine.deposit_step
#print axioms LeanShieldedPool.Refine.transfer_step
#print axioms LeanShieldedPool.Refine.withdraw_step
#print axioms LeanShieldedPool.Refine.withdraw_balance
#print axioms LeanShieldedPool.Refine.ToyRun.refine_run_toy
#print axioms LeanShieldedPool.Refine.ToyRun.toy_state
#print axioms LeanShieldedPool.Refine.Toy.repCore_no_window_inclusion
#print axioms LeanShieldedPool.Refine.Toy.treeLink_needs_nonzero
#print axioms LeanShieldedPool.Refine.Toy.existential_shape_trivial
