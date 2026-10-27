import Refinement.Provenance
import Refinement.ProvenanceModel
import Refinement.ProvenanceRefine
import Refinement.NonVacuity

/-!
# Root provenance: non-vacuity and controls

1. `ProvToy.prov_toy`: `prov_run_of_posts` on the toy pool and history (admin call, reverted
   `setVerifier`, deposit, transfer, withdraw). The deposit root 9 and the current root 96 are
   accepted, and the theorem places both at prefixes of the leaves `[9, 39, 46]`.
2. `ProvToy.Xm H`: the storage-model contract (every call does exactly the storage the contract
   posts state). Both provenance premises hold for every hash `H` (`fresh_Xm`, `tree_Xm`).
3. Zero-root edge case (`zero_root_case`): with a hash that returns 0, a recorded root is 0,
   `RootsNonzero` fails, `validRoots 0` is true, and provenance still holds.
4. Control (`bad_breaks_prov`): a withdraw that also marks its nullifier valid (a mutant of
   the board's Halmos frame check) satisfies every premise except valid-roots freshness, and breaks the invariant: root 5
   is accepted but is no prefix root. `bad_not_fresh`: freshness fails for it.
5. `refineP_run_toy`: `refineP_run` (no `RootsNonzero`) with every premise instantiated on the
   toy.
6. `Step'` is strictly weaker than `Step` (`step'_not_step`): a withdraw against the transfer's
   intermediate prefix (snapshot 2, not in the window `[3, 1, 0]`) is a `Step'` but not a `Step`.
-/

namespace LeanShieldedPool.Refine.ProvToy

open LeanShieldedPool LeanShieldedPool.Refine

/-! ## 1. The toy pool -/

theorem prov_toy : Prov Toy.H (ghostLeaves ToyRun.hist) ToyRun.σ3 :=
  prov_run_of_posts ToyRun.hG0 ToyRun.hRB ToyRun.hEnv ToyRun.hD ToyRun.hTP ToyRun.hWP ToyRun.hA ToyRun.hacc ToyRun.hC1

theorem toy_known_roots :
    ToyRun.σ3.isKnownRoot 9 ∧ ToyRun.σ3.isKnownRoot 96 ∧ ¬ ToyRun.σ3.isKnownRoot 5 ∧
      ghostLeaves ToyRun.hist = [9, 39, 46] := by
  refine ⟨Or.inr (by decide), Or.inl (by decide), ?_, rfl⟩
  rintro (h | h) <;> revert h <;> decide

/-- The theorem's conclusion on the toy: both accepted roots are prefix roots. -/
theorem toy_provenance :
    (∃ n ≤ 3, (9 : Nat) = rootOf Toy.H ([9, 39, 46].take n)) ∧
      (∃ n ≤ 3, (96 : Nat) = rootOf Toy.H ([9, 39, 46].take n)) := by
  have h9 := prov_toy.known_root toy_known_roots.1
  have h96 := prov_toy.known_root toy_known_roots.2.1
  rw [toy_known_roots.2.2.2] at h9 h96
  exact ⟨h9, h96⟩

/-- **Non-vacuity of `refineP_run`**: every premise holds on the toy (no `RootsNonzero`). -/
theorem refineP_run_toy : ∃ txs st, txs.map eraseSnap = txsOf ToyRun.ext ToyRun.hist ∧
    Run' (supOf Toy.E ToyRun.hist) txs st ∧
    RepP Toy.H Toy.E (supOf Toy.E ToyRun.hist) (ghostLeaves ToyRun.hist) ToyRun.σ3 st :=
  refineP_run ToyRun.hG0 ToyRun.hRB ToyRun.hEnv ToyRun.hD ToyRun.hTP ToyRun.hWP ToyRun.hA ToyRun.hC ToyRun.hinj ToyRun.hacc
    ToyRun.hC1 ToyRun.hEx ToyRun.hTL ToyRun.hTH ToyRun.hcr

/-! ## 2. The storage-model contract, for every hash -/

/-- One successful call on storage, exactly as the contract posts state it. -/
def modelStep (H : Nat → Nat → Nat) (σ : Storage) : Call → Storage
  | .deposit _ c _ _ _ _ _ => depositStorage H σ c
  | .transfer n0 n1 c0 c1 _ _ => transferStorage H σ n0 n1 c0 c1
  | .withdraw nf _ _ _ _ => withdrawStorage σ nf
  | .addSupportedToken t => { σ with supportedTokens := Function.update σ.supportedTokens t true }
  | .removeSupportedToken t => { σ with supportedTokens := Function.update σ.supportedTokens t false }
  | .setAttestationRegistry r => { σ with attestationRegistry := r }
  | .transferOwnership o => { σ with owner := o }
  | .setVerifier v => { σ with verifier := v }

/-- The storage-model contract: every call succeeds with no external effect. -/
def Xm (H : Nat → Nat → Nat) : Contract where
  Exec := fun σ c tr σ' => tr = [] ∧ σ' = modelStep H σ c
  Fail := fun σ _ σ' => σ' = σ
  Verified := fun _ _ _ => True
  self := 99
  pinnedVerifier := 1
  genesis := Storage.genesis 1 2 3

theorem g0_Xm (H : Nat → Nat → Nat) : ConstructorPost (Xm H) := ⟨2, 3, rfl⟩

theorem rb_Xm (H : Nat → Nat → Nat) : Rollback (Xm H) := fun _ h => h

theorem fresh_Xm (H : Nat → Nat → Nat) : ValidRootsFresh (Xm H) := by
  intro σ c tr σ' _ hx _ r hr
  obtain ⟨-, rfl⟩ := hx
  cases c with
  | deposit s cm tok amt fund att pay => exact depositStorage_fresh H σ cm r hr
  | transfer n0 n1 c0 c1 root pay => exact transferStorage_fresh H σ n0 n1 c0 c1 r hr
  | withdraw nf tok amt rcpt root => exact Or.inl hr
  | addSupportedToken t => exact Or.inl hr
  | removeSupportedToken t => exact Or.inl hr
  | setAttestationRegistry reg => exact Or.inl hr
  | transferOwnership o => exact Or.inl hr
  | setVerifier v => exact Or.inl hr

theorem tree_Xm (H : Nat → Nat → Nat) : TreeAppend H (Xm H) := by
  intro σ c tr σ' _ hx _
  obtain ⟨-, rfl⟩ := hx
  cases c <;> rfl

/-! ## 3. Zero-root edge case: provenance without `RootsNonzero` -/

/-- A hash whose every output is 0. -/
def H0 : Nat → Nat → Nat := fun _ _ => 0

def histZ : List Call := [.deposit 1 9 5 3 1 0 0, .deposit 1 4 5 3 1 0 0]

def σZ : Storage := modelStep H0 (modelStep H0 (Storage.genesis 1 2 3) (.deposit 1 9 5 3 1 0 0))
  (.deposit 1 4 5 3 1 0 0)

theorem accZ : Accepted (Xm H0) histZ σZ :=
  Accepted.snoc (h := [.deposit 1 9 5 3 1 0 0])
    (Accepted.snoc (h := []) Accepted.nil ⟨rfl, rfl⟩) ⟨rfl, rfl⟩

theorem c1Z : NoSetVerifier histZ := by
  intro c hc v
  simp only [histZ, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> intro he <;> cases he

/-- With an all-zero hash the second deposit records root 0: `RootsNonzero` fails and the zero
flag is set, yet provenance holds and 0 is the empty prefix's root. -/
theorem zero_root_case :
    ¬ RootsNonzero H0 histZ ∧ σZ.validRoots 0 = true ∧ Prov H0 (ghostLeaves histZ) σZ ∧
      PrefixRoot H0 (ghostLeaves histZ) 0 := by
  refine ⟨fun hZ => ?_, by decide, prov_run (g0_Xm H0) (rb_Xm H0) (fresh_Xm H0) (tree_Xm H0) accZ c1Z,
    PrefixRoot.zero H0 _⟩
  exact hZ [.deposit 1 9 5 3 1 0 0] (.deposit 1 4 5 3 1 0 0) [] rfl (by decide) (by decide)

/-! ## 4. Control: an extra `validRoots` write breaks provenance -/

/-- The `wd_extra` mutant on storage: withdraw also marks its nullifier as a valid root. -/
def badStep (H : Nat → Nat → Nat) (σ : Storage) : Call → Storage
  | .withdraw nf _ _ _ _ =>
      { withdrawStorage σ nf with validRoots := Function.update σ.validRoots nf true }
  | c => modelStep H σ c

def Xbad (H : Nat → Nat → Nat) : Contract :=
  { Xm H with Exec := fun σ c tr σ' => tr = [] ∧ σ' = badStep H σ c }

theorem tree_Xbad (H : Nat → Nat → Nat) : TreeAppend H (Xbad H) := by
  intro σ c tr σ' _ hx _
  obtain ⟨-, rfl⟩ := hx
  cases c <;> rfl

def histB : List Call := [.deposit 1 9 5 3 1 0 0, .withdraw 5 5 3 8 9]

def σB : Storage := badStep Toy.H (badStep Toy.H (Storage.genesis 1 2 3) (.deposit 1 9 5 3 1 0 0))
  (.withdraw 5 5 3 8 9)

theorem accB : Accepted (Xbad Toy.H) histB σB :=
  Accepted.snoc (h := [.deposit 1 9 5 3 1 0 0])
    (Accepted.snoc (h := []) Accepted.nil ⟨rfl, rfl⟩) ⟨rfl, rfl⟩

theorem c1B : NoSetVerifier histB := by
  intro c hc v
  simp only [histB, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> intro he <;> cases he

/-- **Control.** Constructor, rollback and the tree premise hold, root 5 is accepted, and 5 is
not the root of any prefix of the leaves `[9]`: the invariant fails. -/
theorem bad_breaks_prov :
    ConstructorPost (Xbad Toy.H) ∧ Rollback (Xbad Toy.H) ∧ TreeAppend Toy.H (Xbad Toy.H) ∧
      σB.isKnownRoot 5 ∧ ¬ PrefixRoot Toy.H (ghostLeaves histB) 5 ∧
      ¬ Prov Toy.H (ghostLeaves histB) σB := by
  have hnot : ¬ PrefixRoot Toy.H (ghostLeaves histB) 5 := by
    rintro ⟨n, hn, h5⟩
    have hl : (ghostLeaves histB).length = 1 := rfl
    rw [hl] at hn
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;> revert h5 <;> decide
  have hk : σB.isKnownRoot 5 := Or.inr (by decide)
  exact ⟨⟨2, 3, rfl⟩, fun _ h => h, tree_Xbad Toy.H, hk, hnot, fun hP => hnot (hP.known_root hk)⟩

/-- Check 1 fails for the mutant: the step from the deposit state turns key 5 true. -/
theorem bad_not_fresh : ¬ ValidRootsFresh (Xbad Toy.H) := by
  intro hF
  have hR : Reach (Xbad Toy.H) (badStep Toy.H (Storage.genesis 1 2 3) (.deposit 1 9 5 3 1 0 0)) :=
    ⟨[.deposit 1 9 5 3 1 0 0], Accepted.snoc (h := []) Accepted.nil ⟨rfl, rfl⟩, by
      intro c hc v
      rw [List.mem_singleton.1 hc]
      intro he
      cases he⟩
  rcases hF hR (c := .withdraw 5 5 3 8 9) ⟨rfl, rfl⟩ (fun v he => by cases he) 5 (by decide) with
    h | h <;> revert h <;> decide

/-! ## 5. `Step'` is strictly weaker than `Step` -/

/-- Deposit of note (token 5, amount 3, owner 0, salt 0), commitment 9. -/
def dD : DepositData Toy.P := Toy.d1

/-- Transfer: spend the deposited note and a ballast note, create (5, 3, 0, 50) and (5, 0, 0, 60). -/
def dT : TransferData Toy.P where
  key := (0 : Nat)
  in1 := Toy.d1.note
  in2 := ⟨(5 : Nat), 0, (0 : Nat), (20 : Nat)⟩
  out1 := ⟨(5 : Nat), 3, (0 : Nat), (50 : Nat)⟩
  out2 := ⟨(5 : Nat), 0, (0 : Nat), (60 : Nat)⟩
  snapshot := 1

/-- Withdraw the first output against snapshot 2: the transfer's intermediate prefix. -/
def dW : WithdrawData Toy.P := ⟨(0 : Nat), dT.out1, (8 : Nat), 2⟩

def sup5 : Toy.P.Token → Prop := fun t => t = (5 : Nat)

noncomputable def st1 : St Toy.P := dD.post (St.empty Toy.P sup5)
noncomputable def st2 : St Toy.P := dT.post st1

theorem st2_window : st2.window = [3, 1, 0] := rfl

theorem run'_example : Run' sup5 [.deposit dD, .transfer dT, .withdraw dW] (dW.post st2) := by
  have h1 : Run' sup5 [.deposit dD] st1 :=
    Run'.step (txs := []) Run'.empty
      (Step'.deposit ⟨rfl, by decide, by unfold U128 maxU128; decide,
        show dD.note.cm ∉ ([] : List Toy.P.Commitment) from fun h => List.not_mem_nil h⟩)
  have hbal : dW.note.amount ≤ st2.balance dW.note.token := by
    show dW.note.amount ≤ bump (St.empty Toy.P sup5).balance dD.note.token dD.note.amount dW.note.token
    unfold bump
    rw [if_pos (show dW.note.token = dD.note.token from rfl)]
    exact Nat.le_refl 3
  have h2 : Run' sup5 [.deposit dD, .transfer dT] st2 :=
    Run'.step (txs := [.deposit dD]) h1 (Step'.transfer ⟨by decide, rfl, rfl,
      show (9 : Nat) ∈ ([9] : List Nat).take 1 by decide,
      Or.inl rfl,
      show dT.nf1 ∉ ([] : List Toy.P.Nullifier) from fun h => List.not_mem_nil h,
      show dT.nf2 ∉ ([] : List Toy.P.Nullifier) from fun h => List.not_mem_nil h,
      show (9 : Nat) ≠ 26 by decide, rfl, rfl, rfl,
      by unfold U128 maxU128; decide, by unfold U128 maxU128; decide,
      by unfold U128 maxU128; decide, by unfold U128 maxU128; decide, rfl,
      show (59 : Nat) ∉ ([9] : List Nat) by decide, show (66 : Nat) ∉ ([9] : List Nat) by decide,
      show (59 : Nat) ≠ 66 by decide⟩)
  exact Run'.step (txs := [.deposit dD, .transfer dT]) h2 (Step'.withdraw ⟨by decide,
    show (59 : Nat) ∈ ([9, 59, 66] : List Nat).take 2 by decide, rfl,
    show (59 : Nat) ∉ ([9, 26] : List Nat) by decide, by decide, by unfold U128 maxU128; decide, hbal⟩)

/-- The last step is not a `Step`: snapshot 2 is not in the window `[3, 1, 0]`. -/
theorem step'_not_step : ¬ dW.guard st2 := by
  intro hg
  have h2 : (2 : Nat) ∈ ([3, 1, 0] : List Nat) := hg.1
  exact absurd h2 (by decide)

end LeanShieldedPool.Refine.ProvToy

/-! Axiom census. -/
#print axioms LeanShieldedPool.Refine.prov_run
#print axioms LeanShieldedPool.Refine.accepted_root_provenance
#print axioms LeanShieldedPool.Refine.transfer_root_provenance
#print axioms LeanShieldedPool.Refine.withdraw_root_provenance
#print axioms LeanShieldedPool.Refine.prov_step
#print axioms LeanShieldedPool.Refine.prov_run_of_posts
#print axioms LeanShieldedPool.Refine.validRootsFresh_of_posts
#print axioms LeanShieldedPool.Refine.treeAppend_of_posts
#print axioms LeanShieldedPool.Refine.PrefixRoot.zero
#print axioms LeanShieldedPool.Refine.repeated_root_evicts_early
#print axioms LeanShieldedPool.Refine.Run'.to_run
#print axioms LeanShieldedPool.Refine.run_to_run'
#print axioms LeanShieldedPool.Refine.transfer_guard_iff
#print axioms LeanShieldedPool.Refine.withdraw_guard_iff
#print axioms LeanShieldedPool.Refine.poolSolvency_prov
#print axioms LeanShieldedPool.Refine.noOverWithdrawal_prov
#print axioms LeanShieldedPool.Refine.nullifierUniqueness_prov
#print axioms LeanShieldedPool.Refine.noDoubleSpend_prov
#print axioms LeanShieldedPool.Refine.valueConservation_prov
#print axioms LeanShieldedPool.Refine.noMinting_prov
#print axioms LeanShieldedPool.Refine.balanceIsLiveValue_prov
#print axioms LeanShieldedPool.Refine.refineP_run
#print axioms LeanShieldedPool.Refine.refineP_inv
#print axioms LeanShieldedPool.Refine.refineP_valueConservation
#print axioms LeanShieldedPool.Refine.Rep.toRepP
#print axioms LeanShieldedPool.Refine.withdraw_balanceP
#print axioms LeanShieldedPool.Refine.depositP_step
#print axioms LeanShieldedPool.Refine.transferP_step
#print axioms LeanShieldedPool.Refine.withdrawP_step
#print axioms LeanShieldedPool.Refine.ProvToy.prov_toy
#print axioms LeanShieldedPool.Refine.ProvToy.refineP_run_toy
#print axioms LeanShieldedPool.Refine.ProvToy.toy_provenance
#print axioms LeanShieldedPool.Refine.ProvToy.fresh_Xm
#print axioms LeanShieldedPool.Refine.ProvToy.tree_Xm
#print axioms LeanShieldedPool.Refine.ProvToy.zero_root_case
#print axioms LeanShieldedPool.Refine.ProvToy.bad_breaks_prov
#print axioms LeanShieldedPool.Refine.ProvToy.bad_not_fresh
#print axioms LeanShieldedPool.Refine.ProvToy.run'_example
#print axioms LeanShieldedPool.Refine.ProvToy.step'_not_step
