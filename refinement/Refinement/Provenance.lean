import Refinement.Cases

/-!
# Root provenance

Board rows T1 and W1 restated as root provenance: every root `isKnownRoot` accepts is the LeanIMT
root of some prefix of the current leaves. Freshness (the last 100 roots) is spec section 4.4
conformance and is not used here.

Part 1, storage model. `Prov H L σ`: the tree slots hold the LeanIMT of `L`, and every
`validRoots` key that is true is the root of a prefix of `L`. `prov_run` proves it for every
accepted history of the pinned deployment from two premises:

* `ValidRootsFresh` (the board's bounded Halmos frame check, row T1): in one successful call, a `validRoots` key turns true
  only if it was true before or it is the post-state current root;
* `TreeAppend`: one successful call appends its inserts to the tree slots, in order. This is the
  tree half of the contract posts (`treeAppend_of_posts`).

Part 2, model. `Step'` is `Step` with the root conjunct of transfer and withdraw replaced by
provenance: the snapshot is a leaf count of the current tree (`snapshot ≤ minted.length`), not
a window entry. `Run'.to_run` maps every `Step'` run to a `Step` run with the same states and
the same operations up to snapshots, so all six money theorems hold for `Step'` (`*_prov`).
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

/-! ## Part 1: provenance over the contract-storage model -/

/-- `r` is the LeanIMT root of some prefix of `L`. -/
def PrefixRoot (H : Nat → Nat → Nat) (L : List Nat) (r : Nat) : Prop :=
  ∃ n ≤ L.length, r = rootOf H (L.take n)

theorem PrefixRoot.self (H : Nat → Nat → Nat) (L : List Nat) : PrefixRoot H L (rootOf H L) :=
  ⟨L.length, Nat.le_refl _, by rw [List.take_length]⟩

/-- **Zero-root edge case.** `0` is the root of the empty prefix (`rootOf_nil`), so it is a
provenance root of every leaf list. A recorded zero root (a PoseidonT3 output 0) is never
evicted (`ShieldedPool.sol:373`), but it stays inside provenance. -/
theorem PrefixRoot.zero (H : Nat → Nat → Nat) (L : List Nat) : PrefixRoot H L 0 :=
  ⟨0, Nat.zero_le _, by rw [List.take_zero, rootOf_nil]⟩

theorem PrefixRoot.mono {H : Nat → Nat → Nat} {L L' : List Nat} {r : Nat} (hp : L <+: L')
    (h : PrefixRoot H L r) : PrefixRoot H L' r := by
  obtain ⟨n, hn, hr⟩ := h
  refine ⟨n, Nat.le_trans hn hp.length_le, ?_⟩
  rw [hr, List.prefix_iff_eq_take.1 hp, List.take_take, Nat.min_eq_left hn]

/-- **The provenance invariant** on pool storage, for the ghost leaf list `L`. -/
structure Prov (H : Nat → Nat → Nat) (L : List Nat) (σ : Storage) : Prop where
  /-- The tree slots hold the LeanIMT of `L`. -/
  tree : σ.imt = imtOf H L
  /-- Every valid root is the root of a prefix of `L`. -/
  valid : ∀ r, σ.validRoots r = true → PrefixRoot H L r

theorem Prov.current_root {H : Nat → Nat → Nat} {L : List Nat} {σ : Storage} (hP : Prov H L σ) :
    σ.currentRoot = rootOf H L :=
  congrArg Imt.root hP.tree

/-- **Accepted-root provenance**: every root `isKnownRoot` accepts is the root of a prefix of
the leaves. -/
theorem Prov.known_root {H : Nat → Nat → Nat} {L : List Nat} {σ : Storage} (hP : Prov H L σ)
    {r : Nat} (hk : σ.isKnownRoot r) : PrefixRoot H L r := by
  rcases hk with hc | hv
  · rw [hc, hP.current_root]
    exact PrefixRoot.self H L
  · exact hP.valid r hv

theorem prov_genesis (H : Nat → Nat → Nat) (v reg o : Nat) :
    Prov H [] (Storage.genesis v reg o) where
  tree := rfl
  valid := fun _ h => absurd h Bool.false_ne_true

theorem imtOf_append_foldl (H : Nat → Nat → Nat) (L M : List Nat) :
    imtOf H (L ++ M) = M.foldl (imtInsert H) (imtOf H L) := by
  simp only [imtOf, List.foldl_append]

/-- **One step.** A call that appends `M` to the tree and turns true no `validRoots` key except
the post-state current root preserves provenance. -/
theorem prov_step {H : Nat → Nat → Nat} {L M : List Nat} {σ σ' : Storage} (hP : Prov H L σ)
    (htree : σ'.imt = M.foldl (imtInsert H) σ.imt)
    (hfresh : ∀ r, σ'.validRoots r = true → σ.validRoots r = true ∨ r = σ'.currentRoot) :
    Prov H (L ++ M) σ' := by
  have ht : σ'.imt = imtOf H (L ++ M) := by rw [htree, hP.tree, imtOf_append_foldl]
  refine ⟨ht, fun r hr => ?_⟩
  rcases hfresh r hr with hold | hcur
  · exact (hP.valid r hold).mono (List.prefix_append L M)
  · rw [hcur, show σ'.currentRoot = rootOf H (L ++ M) from congrArg Imt.root ht]
    exact PrefixRoot.self H (L ++ M)

/-- **Valid-roots freshness, as a premise.** From a reachable state, in one successful call other than
`setVerifier`, a `validRoots` key is true afterwards only if it was true before or it is the
post-state current root (`commitmentRoot()` after the call). The board's Halmos check (row T1, not in this
package) supports this for deposit and transfer, and the stronger form without the current-root
case for withdraw and all five owner calls, in its bounded environment. Board rows T1 and W1. -/
def ValidRootsFresh (X : Contract) : Prop :=
  ∀ {σ c tr σ'}, Reach X σ → X.Exec σ c tr σ' → (∀ v, c ≠ .setVerifier v) →
    ∀ r, σ'.validRoots r = true → σ.validRoots r = true ∨ r = σ'.currentRoot

/-- **Tree premise.** From a reachable state, one successful call other than `setVerifier`
appends its inserts, in calldata order, to the tree slots. Board rows: the insertion rows (D5,
T11, T12, X1, X2); follows from the contract posts (`treeAppend_of_posts`). -/
def TreeAppend (H : Nat → Nat → Nat) (X : Contract) : Prop :=
  ∀ {σ c tr σ'}, Reach X σ → X.Exec σ c tr σ' → (∀ v, c ≠ .setVerifier v) →
    σ'.imt = c.inserts.foldl (imtInsert H) σ.imt

/-- **Provenance for every accepted history** of the pinned deployment (no successful
`setVerifier`). Premises: constructor, rollback, check 1 and the tree premise. No window,
ring, `RootsNonzero` or hash premise. -/
theorem prov_run {H : Nat → Nat → Nat} {X : Contract} (hG0 : ConstructorPost X)
    (hRB : Rollback X) (hF : ValidRootsFresh X) (hT : TreeAppend H X) {h : List Call}
    {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h) : Prov H (ghostLeaves h) σ := by
  revert hC1
  induction hacc with
  | nil =>
    intro _
    obtain ⟨reg, o, hg⟩ := hG0
    rw [hg]
    exact prov_genesis H _ reg o
  | @snoc h σ σ' c tr ha hx ih =>
    intro hC1
    have hC1' : NoSetVerifier h := fun c' hc' => hC1 c' (List.mem_append_left _ hc')
    have hR : Reach X σ := ⟨h, ha, hC1'⟩
    have hc : ∀ v, c ≠ .setVerifier v := hC1 c (List.mem_append_right _ (List.mem_singleton_self c))
    rw [ghostLeaves_snoc]
    exact prov_step (ih hC1') (hT hR hx hc) (hF hR hx hc)
  | @fail h σ σ' c ha hf ih =>
    intro hC1
    rw [hRB ⟨h, ha, hC1⟩ hf]
    exact ih hC1

/-- **T1/W1 restated (provenance).** For every accepted history of the pinned deployment, every
root `isKnownRoot` accepts is the LeanIMT root of a prefix of the history's leaves. -/
theorem accepted_root_provenance {H : Nat → Nat → Nat} {X : Contract} (hG0 : ConstructorPost X)
    (hRB : Rollback X) (hF : ValidRootsFresh X) (hT : TreeAppend H X) {h : List Call}
    {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h) {r : Nat}
    (hk : σ.isKnownRoot r) :
    ∃ n ≤ (ghostLeaves h).length, r = rootOf H ((ghostLeaves h).take n) :=
  (prov_run hG0 hRB hF hT hacc hC1).known_root hk

/-- **T1, restated.** The root of every successful transfer from an accepted state is the
LeanIMT root of a prefix of the leaves at that point (with `TransferPost.known_root`, the
lookup guard at `ShieldedPool.sol:204`). -/
theorem transfer_root_provenance {H : Nat → Nat → Nat} {X : Contract} (hG0 : ConstructorPost X)
    (hRB : Rollback X) (hF : ValidRootsFresh X) (hT : TreeAppend H X) (hTP : TransferPost H X)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h)
    {n0 n1 c0 c1 root pay : Nat} {tr : List Ext} {σ' : Storage}
    (hx : X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ') : PrefixRoot H (ghostLeaves h) root :=
  (prov_run hG0 hRB hF hT hacc hC1).known_root (hTP.known_root ⟨h, hacc, hC1⟩ hx)

/-- **W1, restated.** The root of every successful withdraw from an accepted state is the
LeanIMT root of a prefix of the leaves at that point (`ShieldedPool.sol:263`). -/
theorem withdraw_root_provenance {H : Nat → Nat → Nat} {X : Contract} (hG0 : ConstructorPost X)
    (hRB : Rollback X) (hF : ValidRootsFresh X) (hT : TreeAppend H X) (hWP : WithdrawPost X)
    {h : List Call} {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h)
    {nf tok amt rcpt root : Nat} {tr : List Ext} {σ' : Storage}
    (hx : X.Exec σ (.withdraw nf tok amt rcpt root) tr σ') : PrefixRoot H (ghostLeaves h) root :=
  (prov_run hG0 hRB hF hT hacc hC1).known_root (hWP.known_root ⟨h, hacc, hC1⟩ hx)

/-- The roots a later operation can use are roots of prefixes of the leaves at that time, and
those are prefixes of every later leaf list: provenance is stable under history extension. -/
theorem PrefixRoot.of_history_prefix {H : Nat → Nat → Nat} {h₁ h₂ : List Call} {r : Nat}
    (hp : h₁ <+: h₂) (hr : PrefixRoot H (ghostLeaves h₁) r) : PrefixRoot H (ghostLeaves h₂) r :=
  hr.mono (ghostLeaves_prefix hp)

/-! ### The premises follow from the contract posts -/

theorem recordRoot_validRoots {σ : Storage} {r : Nat} (h : σ.recordRoot.validRoots r = true) :
    σ.validRoots r = true ∨ r = σ.recordRoot.currentRoot := by
  have h' : (if r = σ.currentRoot then true
      else if σ.ring σ.ringIndex ≠ 0 ∧ r = σ.ring σ.ringIndex then false
      else σ.validRoots r) = true := h
  by_cases h1 : r = σ.currentRoot
  · exact Or.inr h1
  · rw [if_neg h1] at h'
    by_cases h2 : σ.ring σ.ringIndex ≠ 0 ∧ r = σ.ring σ.ringIndex
    · rw [if_pos h2] at h'
      exact absurd h' Bool.false_ne_true
    · rw [if_neg h2] at h'
      exact Or.inl h'

/-- `_recordRoot` as modelled (`Storage.recordRoot`) satisfies check 1's property. -/
theorem depositStorage_fresh (H : Nat → Nat → Nat) (σ : Storage) (c : Nat) (r : Nat)
    (h : (depositStorage H σ c).validRoots r = true) :
    σ.validRoots r = true ∨ r = (depositStorage H σ c).currentRoot :=
  recordRoot_validRoots h

theorem transferStorage_fresh (H : Nat → Nat → Nat) (σ : Storage) (n0 n1 c0 c1 : Nat) (r : Nat)
    (h : (transferStorage H σ n0 n1 c0 c1).validRoots r = true) :
    σ.validRoots r = true ∨ r = (transferStorage H σ n0 n1 c0 c1).currentRoot :=
  recordRoot_validRoots h

/-- Valid-roots freshness follows from the contract posts. -/
theorem validRootsFresh_of_posts {H : Nat → Nat → Nat} {X : Contract}
    (hEnv : OwnerCallbackFree X) (hD : DepositPost H X) (hTP : TransferPost H X)
    (hWP : WithdrawPost X) (hA : AdminStutter X) : ValidRootsFresh X := by
  intro σ c tr σ' hR hx hc r hr
  cases c with
  | deposit s cm tok amt fund att pay =>
    rw [hD.post hR hx (no_nested hEnv hR hx (hD.guarded hR hx))] at hr ⊢
    exact depositStorage_fresh H σ cm r hr
  | transfer n0 n1 c0 c1 root pay =>
    rw [hTP.post hR hx (no_nested_of_nil (hTP.no_effects hR hx))] at hr ⊢
    exact transferStorage_fresh H σ n0 n1 c0 c1 r hr
  | withdraw nf tok amt rcpt root =>
    rw [hWP.post hR hx (no_nested hEnv hR hx (hWP.guarded hR hx))] at hr
    exact Or.inl hr
  | addSupportedToken tok =>
    rw [hA.add hR hx] at hr
    exact Or.inl hr
  | removeSupportedToken tok =>
    rw [hA.remove hR hx] at hr
    exact Or.inl hr
  | setAttestationRegistry reg =>
    rw [hA.registry hR hx] at hr
    exact Or.inl hr
  | transferOwnership o =>
    rw [hA.owner hR hx] at hr
    exact Or.inl hr
  | setVerifier v => exact absurd rfl (hc v)

/-- The tree premise follows from the contract posts. -/
theorem treeAppend_of_posts {H : Nat → Nat → Nat} {X : Contract}
    (hEnv : OwnerCallbackFree X) (hD : DepositPost H X) (hTP : TransferPost H X)
    (hWP : WithdrawPost X) (hA : AdminStutter X) : TreeAppend H X := by
  intro σ c tr σ' hR hx hc
  cases c with
  | deposit s cm tok amt fund att pay =>
    rw [hD.post hR hx (no_nested hEnv hR hx (hD.guarded hR hx))]
    rfl
  | transfer n0 n1 c0 c1 root pay =>
    rw [hTP.post hR hx (no_nested_of_nil (hTP.no_effects hR hx))]
    rfl
  | withdraw nf tok amt rcpt root =>
    rw [hWP.post hR hx (no_nested hEnv hR hx (hWP.guarded hR hx))]
    rfl
  | addSupportedToken tok =>
    rw [hA.add hR hx]
    rfl
  | removeSupportedToken tok =>
    rw [hA.remove hR hx]
    rfl
  | setAttestationRegistry reg =>
    rw [hA.registry hR hx]
    rfl
  | transferOwnership o =>
    rw [hA.owner hR hx]
    rfl
  | setVerifier v => exact absurd rfl (hc v)

/-- **Provenance from the premises of `refine_run`**, with no `RootsNonzero` and no ring premise. -/
theorem prov_run_of_posts {H : Nat → Nat → Nat} {X : Contract} (hG0 : ConstructorPost X)
    (hRB : Rollback X) (hEnv : OwnerCallbackFree X) (hD : DepositPost H X)
    (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X) {h : List Call}
    {σ : Storage} (hacc : Accepted X h σ) (hC1 : NoSetVerifier h) : Prov H (ghostLeaves h) σ :=
  prov_run hG0 hRB (validRootsFresh_of_posts hEnv hD hTP hWP hA)
    (treeAppend_of_posts hEnv hD hTP hWP hA) hacc hC1

/-- **Repeated-root edge case (T13, not provenance).** If the evicted ring entry's value also
sits in another ring slot, `_recordRoot` clears its flag although the ring still holds it:
`validRoots` then under-approximates the ring. Provenance is unaffected (it only needs the
flags that are true). Exact retention (T13) fails here. -/
theorem repeated_root_evicts_early :
    let σ : Storage := { Storage.genesis 1 2 3 with
      ring := fun p => if p < 2 then 5 else 0, validRoots := fun r => r == 5,
      sideNodes := fun _ => 7 }
    σ.recordRoot.validRoots 5 = false ∧ σ.recordRoot.ring 1 = 5 := by
  refine ⟨?_, ?_⟩ <;> decide

end LeanShieldedPool.Refine
