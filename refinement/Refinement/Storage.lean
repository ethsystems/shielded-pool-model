import LeanShieldedPool.Statements.L3

/-!
# Pool storage

Storage of `ShieldedPool` at ethsystems/pocs `a04b8b3`. The slot numbers come from forge
`storageLayout` for that build (read from the compiler output; not re-run by this package):
`_tree` 0 (`size` 0, `depth` 1, `sideNodes` 2, `leaves` 3), `historicalRoots` 4..103,
`historicalRootIndex` 104, `validRoots` 105, `nullifiers` 106, `supportedTokens` 107,
`verifier` 108, `attestationRegistry` 109, `owner` 110. The OpenZeppelin reentrancy status is
not in this list and is not modelled.

A word is a `Nat`. Mappings are total functions. The contract's top-level calls are the
uninterpreted relations `Contract.Exec` (success, with its external-call trace) and
`Contract.Fail` (revert); the premises in `Refinement/Post.lean` constrain them on reachable states
of the pinned deployment.
-/

namespace LeanShieldedPool.Refine

/-- The LeanIMT slots of `_tree`: `size`, `depth`, `sideNodes`
(`InternalLeanIMT.sol`, struct `LeanIMTData`). -/
structure Imt where
  size : Nat
  depth : Nat
  side : Nat → Nat

/-- The constructor's tree: every slot zero. -/
def Imt.empty : Imt := ⟨0, 0, fun _ => 0⟩

/-- `_root`: `sideNodes[depth]` (`InternalLeanIMT.sol:346`). -/
def Imt.root (t : Imt) : Nat := t.side t.depth

/-- One pass of the `_insert` loop body at `level` (`InternalLeanIMT.sol:65-73`).
`(index >> level) & 1 == 1` is written `(index >>> level) % 2 = 1`. `H` is `PoseidonT3.hash`. -/
def imtStep (H : Nat → Nat → Nat) (index : Nat) (acc : Nat × (Nat → Nat)) (level : Nat) :
    Nat × (Nat → Nat) :=
  if (index >>> level) % 2 = 1 then (H (acc.2 level) acc.1, acc.2)
  else (acc.1, Function.update acc.2 level acc.1)

/-- `_insert` on the tree slots (`InternalLeanIMT.sol:40-82`), without its three reverts and
without the `leaves` mapping write (see `Storage.insertLeaf`). -/
def imtInsert (H : Nat → Nat → Nat) (t : Imt) (leaf : Nat) : Imt :=
  let d := if 2 ^ t.depth < t.size + 1 then t.depth + 1 else t.depth
  let r := (List.range d).foldl (imtStep H t.size) (leaf, t.side)
  ⟨t.size + 1, d, Function.update r.2 d r.1⟩

/-- The tree slots after inserting `L` in order from the constructor. -/
def imtOf (H : Nat → Nat → Nat) (L : List Nat) : Imt := L.foldl (imtInsert H) Imt.empty

/-- The LeanIMT root of the leaf list `L`: the value `commitmentRoot()` returns when the tree
holds exactly `L`. -/
def rootOf (H : Nat → Nat → Nat) (L : List Nat) : Nat := (imtOf H L).root

theorem imtOf_append (H : Nat → Nat → Nat) (L : List Nat) (c : Nat) :
    imtOf H (L ++ [c]) = imtInsert H (imtOf H L) c := by
  simp only [imtOf, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rootOf_nil (H : Nat → Nat → Nat) : rootOf H [] = 0 := rfl

/-- A one-leaf LeanIMT has the leaf as its root (depth 0, no hash). -/
theorem rootOf_singleton (H : Nat → Nat → Nat) (a : Nat) : rootOf H [a] = a := rfl

/-- `binary_merkle_root` of zk-kit.noir v0.0.2 (`binary-merkle-root/src/lib.nr:10-41`) on the
first `depth` levels of the path, given as (index bit, sibling) pairs from the leaf up. At
depth 0 it returns the leaf unchanged. -/
def foldRoot (H : Nat → Nat → Nat) (leaf : Nat) (path : List (Bool × Nat)) : Nat :=
  path.foldl (fun node bs => if bs.1 then H bs.2 node else H node bs.2) leaf

/-- Pool storage, one field per slot. `ring p` is `historicalRoots[p]`, slot `4 + p`, for
`p < 100`. -/
structure Storage where
  /-- slot 0, `_tree.size` -/
  size : Nat
  /-- slot 1, `_tree.depth` -/
  depth : Nat
  /-- slot 2, `_tree.sideNodes` -/
  sideNodes : Nat → Nat
  /-- slot 3, `_tree.leaves`: leaf to its 1-based index, 0 when absent -/
  leafIndex : Nat → Nat
  /-- slots 4..103, `historicalRoots` -/
  ring : Nat → Nat
  /-- slot 104, `historicalRootIndex` -/
  ringIndex : Nat
  /-- slot 105, `validRoots` -/
  validRoots : Nat → Bool
  /-- slot 106, `nullifiers` -/
  nullifiers : Nat → Bool
  /-- slot 107, `supportedTokens` -/
  supportedTokens : Nat → Bool
  /-- slot 108, `verifier` -/
  verifier : Nat
  /-- slot 109, `attestationRegistry` -/
  attestationRegistry : Nat
  /-- slot 110, `owner` -/
  owner : Nat

namespace Storage

/-- The tree slots as an `Imt`. -/
def imt (σ : Storage) : Imt := ⟨σ.size, σ.depth, σ.sideNodes⟩

/-- `commitmentRoot()`: `_tree._root()`. -/
def currentRoot (σ : Storage) : Nat := σ.sideNodes σ.depth

/-- `isKnownRoot(root)` (`ShieldedPool.sol:313`). -/
def isKnownRoot (σ : Storage) (r : Nat) : Prop := r = σ.currentRoot ∨ σ.validRoots r = true

/-- Storage after the constructor (`ShieldedPool.sol:102-111`): every slot zero except
`verifier`, `attestationRegistry` and `owner`. -/
def genesis (v reg o : Nat) : Storage where
  size := 0
  depth := 0
  sideNodes := fun _ => 0
  leafIndex := fun _ => 0
  ring := fun _ => 0
  ringIndex := 0
  validRoots := fun _ => false
  nullifiers := fun _ => false
  supportedTokens := fun _ => false
  verifier := v
  attestationRegistry := reg
  owner := o

/-- `_tree.insert(leaf)` on success: the tree slots per `imtInsert` and
`leaves[leaf] = size + 1`. -/
def insertLeaf (H : Nat → Nat → Nat) (σ : Storage) (leaf : Nat) : Storage :=
  let t := imtInsert H σ.imt leaf
  { σ with
    size := t.size
    depth := t.depth
    sideNodes := t.side
    leafIndex := Function.update σ.leafIndex leaf (σ.size + 1) }

/-- `_recordRoot()` (`ShieldedPool.sol:368-380`): evict the ring entry at the index if it is
nonzero, mark the current root valid, store it in the ring, advance the index mod 100. -/
def recordRoot (σ : Storage) : Storage :=
  { σ with
    validRoots := fun r =>
      if r = σ.currentRoot then true
      else if σ.ring σ.ringIndex ≠ 0 ∧ r = σ.ring σ.ringIndex then false
      else σ.validRoots r
    ring := Function.update σ.ring σ.ringIndex σ.currentRoot
    ringIndex := (σ.ringIndex + 1) % 100 }

/-- `nullifiers[x] = true`. -/
def markSpent (σ : Storage) (x : Nat) : Storage :=
  { σ with nullifiers := Function.update σ.nullifiers x true }

theorem insertLeaf_imt (H : Nat → Nat → Nat) (σ : Storage) (leaf : Nat) :
    (σ.insertLeaf H leaf).imt = imtInsert H σ.imt leaf := rfl

theorem recordRoot_imt (σ : Storage) : σ.recordRoot.imt = σ.imt := rfl

theorem currentRoot_eq_imt_root (σ : Storage) : σ.currentRoot = σ.imt.root := rfl

end Storage

/-- The exact storage a successful `deposit` leaves: one insert, one ring record. -/
def depositStorage (H : Nat → Nat → Nat) (σ : Storage) (c : Nat) : Storage :=
  (σ.insertLeaf H c).recordRoot

/-- The exact storage a successful `transfer` leaves: both flags, two inserts in calldata
order, one ring record of the final root (`ShieldedPool.sol:225-232`). -/
def transferStorage (H : Nat → Nat → Nat) (σ : Storage) (n0 n1 c0 c1 : Nat) : Storage :=
  ((((σ.markSpent n0).markSpent n1).insertLeaf H c0).insertLeaf H c1).recordRoot

/-- The exact storage a successful `withdraw` leaves: one flag (`ShieldedPool.sol:283`). -/
def withdrawStorage (σ : Storage) (x : Nat) : Storage := σ.markSpent x

/-- A top-level call to the pool, with the calldata the refinement reads. Proof bytes and
payloads are dropped. The history also records the two public inputs the pool computes rather
than reads: `att` (`attestationRoot()`) and `pay` (`payloadCommitment(payload)`). -/
inductive Call where
  | deposit (sender commitment token amount funding att pay : Nat)
  | transfer (nf0 nf1 cm0 cm1 root pay : Nat)
  | withdraw (nf token amount recipient root : Nat)
  | addSupportedToken (token : Nat)
  | removeSupportedToken (token : Nat)
  | setAttestationRegistry (registry : Nat)
  | transferOwnership (newOwner : Nat)
  | setVerifier (newVerifier : Nat)

/-- The owner-only functions (`onlyOwner`, `ShieldedPool.sol:98`). -/
def Call.isOwner : Call → Bool
  | .addSupportedToken _ => true
  | .removeSupportedToken _ => true
  | .setAttestationRegistry _ => true
  | .transferOwnership _ => true
  | .setVerifier _ => true
  | _ => false

/-- One external effect of a successful top-level call, in order: a token call the pool makes,
or a successful pool call made from inside a token callback. -/
inductive Ext where
  /-- `IERC20(token).safeTransferFrom(src, dst, amount)` (`ShieldedPool.sol:178`). -/
  | transferFrom (token src dst amount : Nat)
  /-- `IERC20(token).safeTransfer(dst, amount)` (`ShieldedPool.sol:286`). -/
  | transfer (token dst amount : Nat)
  /-- A pool call that succeeded inside a token callback. -/
  | nested (c : Call)

def Ext.isNested : Ext → Bool
  | .nested _ => true
  | _ => false

/-- The token calls of a trace, in order. -/
def tokenCalls (tr : List Ext) : List Ext := tr.filter (fun e => !e.isNested)

/-- Leaves a call inserts, in order. -/
def Call.inserts : Call → List Nat
  | .deposit _ c _ _ _ _ _ => [c]
  | .transfer _ _ c0 c1 _ _ => [c0, c1]
  | _ => []

/-- Ghost leaf order of a history: every inserted commitment, in insertion order. -/
def ghostLeaves (h : List Call) : List Nat := h.flatMap Call.inserts

theorem ghostLeaves_snoc (h : List Call) (c : Call) :
    ghostLeaves (h ++ [c]) = ghostLeaves h ++ c.inserts := by
  simp only [ghostLeaves, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The circuit a verifier call targets. -/
inductive Circuit where
  | deposit
  | transfer
  | withdraw

/-- The deployed pool, uninterpreted. The premises of `Refinement/Post.lean` constrain it only on
states reachable from `genesis` without a `setVerifier` call (`Reach`). -/
structure Contract where
  /-- `Exec σ c tr σ'`: the top-level call `c` succeeds from storage `σ`, makes the external
  effects `tr` in order and leaves `σ'`. Bytecode and EVM semantics (A11). -/
  Exec : Storage → Call → List Ext → Storage → Prop
  /-- `Fail σ c σ'`: the top-level call `c` reverts from storage `σ`; `σ'` is the storage after
  the transaction. The rollback premise (`Rollback`) says `σ' = σ`. -/
  Fail : Storage → Call → Storage → Prop
  /-- `Verified v k x`: the verifier contract at address `v`, entry point of circuit `k`, returns
  true on some proof with public inputs `x`. -/
  Verified : Nat → Circuit → List Nat → Prop
  /-- The pool's own address (`address(this)`). -/
  self : Nat
  /-- The pinned composite verifier address (C1). -/
  pinnedVerifier : Nat
  /-- Storage right after the constructor. -/
  genesis : Storage

/-- Histories of successful top-level calls from the constructor's storage. Reverted calls
are transitions too; they leave the history unchanged. -/
inductive Accepted (X : Contract) : List Call → Storage → Prop where
  | nil : Accepted X [] X.genesis
  | snoc {h : List Call} {σ σ' : Storage} {c : Call} {tr : List Ext} :
      Accepted X h σ → X.Exec σ c tr σ' → Accepted X (h ++ [c]) σ'
  | fail {h : List Call} {σ σ' : Storage} {c : Call} :
      Accepted X h σ → X.Fail σ c σ' → Accepted X h σ'

/-- C1 on a history: no successful `setVerifier` call. -/
def NoSetVerifier (h : List Call) : Prop := ∀ c ∈ h, ∀ v, c ≠ .setVerifier v

/-- Reachable states of the pinned deployment: reached from `genesis` by a history with no
`setVerifier` call. Every contract premise quantifies over these states only. -/
def Reach (X : Contract) (σ : Storage) : Prop := ∃ h, Accepted X h σ ∧ NoSetVerifier h

end LeanShieldedPool.Refine
