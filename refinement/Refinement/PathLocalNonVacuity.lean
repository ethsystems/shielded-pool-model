import Refinement.PathLocal
import Refinement.NonVacuity
import Tree.Checks

/-!
# Path-local premises: positive-depth witness and controls

1. `refinePL_run_toy`: `refinePL_run` with every premise instantiated on the toy history
   (`ToyRun`): admin call, reverted `setVerifier`, deposit, transfer with ballast input 1, withdraw.
   The withdrawal's retained path has length 2 against the depth-2 tree of `[9, 39, 46]`
   (`toy_positive_depth`). The membership facts are the real LeanIMT fold (`Tree/LeanImt.lean`),
   not a toy relation.
2. `old_premise_false_on_toy`: on the same history, the global premise with the bad event of the
   LeanIMT module, `TreeHyp (CollC Toy.H)`, is false: the ballast word 26 has a path to the root of `[9, 39]`
   that collides with the tree.
3. Control (a), `control_planted_bad`: a bad event planted on the retained path (the internal
   node 49 folded to the root along one sibling) is the bad branch of `binding_mem_or_bad`, and
   `PathTreeHyp` rejects every input list that contains it.
4. Control (c), `control_zero_input0`: a transfer whose input 0 has amount 0 and is not in the
   tree, with input 1 ballast, is rejected by `PathTreeHyp`. Input 0 gets no exemption. The
   variant that exempts a zero-valued input 0 accepts it (`control_zero_input0_exempt_accepts`).
5. Positive control and contrast: the onto-hash obstruction of the LeanIMT module
   (`LeanImt.Checks.collC_of_onto`) still proves, and with it the global premise is false for every nonempty word list and every hash
   that is surjective in the second argument for every fixed first argument
   (`global_premise_false_of_onto`). Joint surjectivity or compression alone does not give that
   hypothesis. The per-path premise holds for `xor`, which has the property, on an honest path
   (`onto_contrast`).
-/

namespace LeanShieldedPool.Refine.PathToy

open LeanShieldedPool LeanShieldedPool.Refine LeanShieldedPool.Refine.LeanImt

/-- A retained path from its (bit, sibling) pairs, padded to the circuit width 32. -/
def mkPath (p : List (Bool × Nat)) (h : p.length ≤ 32) : MPath :=
  ⟨p.length, padI p 32 h, padP p 32 h⟩

/-- `¬ Bad` from bounded checks over the fold pairs and the tree pairs. -/
theorem not_bad_of {H : Nat → Nat → Nat} {l : Nat} {M : List Nat} {leaf : Nat}
    {p : List (Bool × Nat)}
    (h1 : ∀ a ∈ foldPairs H leaf p, ∀ b ∈ pairs H l M, a ≠ b → H a.1 a.2 ≠ H b.1 b.2)
    (h2 : ∀ b ∈ pairs H l M, leaf ≠ H b.1 b.2)
    (h3 : ∀ a ∈ foldPairs H leaf p, H a.1 a.2 ∉ M ∧ ¬ (M = [] ∧ H a.1 a.2 = 0)) :
    ¬ Bad H l M leaf p := by
  rintro (⟨x, y, u, v, hx, hu, hne, he⟩ | ⟨u, v, hu, he⟩ | ⟨x, y, hx, ha⟩)
  · exact h1 _ hx _ hu hne he
  · exact h2 _ hu he
  · rcases ha with ha | ha
    · exact (h3 _ hx).1 ha
    · exact (h3 _ hx).2 ha

/-! ## 1. Positive-depth witness on the toy -/

/-- Paths in the toy tree `[9, 39, 46]` with `Toy.H a b = a + b + 1` (roots: `[9]` 9,
`[9, 39]` 49, `[9, 39, 46]` 96). Bit `true` puts the sibling on the left. -/
def T0 : MPath := mkPath [] (by decide)
def T1 : MPath := mkPath [(false, 39)] (by decide)
def T2 : MPath := mkPath [(false, 39), (false, 46)] (by decide)
def W1 : MPath := mkPath [(true, 9)] (by decide)
def W2 : MPath := mkPath [(true, 9), (false, 46)] (by decide)

/-- The toy path extractor: the honest LeanIMT path of the spent note for the public root. -/
def pext : PathExt where
  transfer := fun x =>
    (if x.getD 4 0 = 9 then T0 else if x.getD 4 0 = 49 then T1 else T2, T0)
  withdraw := fun x => if x.getD 4 0 = 49 then W1 else W2

/-- the circuit's fold equation on the retained path holds for every vector the toy circuits accept. -/
theorem hPF : PathFacts Toy.H Toy.E ToyRun.C ToyRun.ext pext where
  t_path0 := fun x hd => by
    obtain ⟨-, -, -, -, -, -, ⟨n, hn, hr, hm⟩, -⟩ := hd
    have hn' : n ≤ 3 := hn
    replace hm : (9 : Nat) ∈ ToyRun.leavesT.take n := hm
    show (pext.transfer x).1.fold Toy.H 9 = x.getD 4 0
    simp only [pext]
    rw [hr]
    interval_cases n
    · exact absurd hm (by decide)
    all_goals decide
  t_path1 := fun _ _ ha => absurd rfl ha
  w_path := fun x hd => by
    obtain ⟨-, -, -, -, ⟨n, hn, hr, hm⟩, -⟩ := hd
    have hn' : n ≤ 3 := hn
    replace hm : (39 : Nat) ∈ ToyRun.leavesT.take n := hm
    show (pext.withdraw x).fold Toy.H 39 = x.getD 4 0
    simp only [pext]
    rw [hr]
    interval_cases n
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    all_goals decide

/-- The membership-checked inputs of the toy history: input 0 of the transfer (word 9, empty
path at the one-leaf root 9) and the withdrawn note (word 39, the depth-2 path). The ballast
input 1 (word 26) is not checked. -/
theorem toy_checked : checkedInputs Toy.E ToyRun.ext pext ToyRun.hist = [(9, T0), (39, W2)] := rfl

/-- **The per-path premise holds on the toy history.** -/
theorem hPT : PathTreeHyp Toy.H (ghostLeaves ToyRun.hist) (checkedInputs Toy.E ToyRun.ext pext ToyRun.hist)
    where
  nonzero := by
    rw [toy_checked]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> decide
  no_bad := by
    rw [toy_checked]
    intro L hL q hq hf
    have hG : ghostLeaves ToyRun.hist = ToyRun.leavesT := rfl
    rw [hG] at hL
    obtain ⟨k, hk, rfl⟩ : ∃ k, k ≤ 3 ∧ L = ToyRun.leavesT.take k :=
      ⟨L.length, hL.length_le, List.prefix_iff_eq_take.1 hL⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    interval_cases k <;> rcases hq with rfl | rfl <;>
      first
      | exact absurd hf (by decide)
      | exact not_bad_of (by decide) (by decide) (by decide)

/-- **Positive depth.** The toy tree has depth 2, and the withdrawal's retained path has length
2 and folds the note to the root the withdrawal names (96). -/
theorem toy_positive_depth :
    (imtOf Toy.H (ghostLeaves ToyRun.hist)).depth = 2 ∧ W2.len = 2 ∧
      W2.fold Toy.H 39 = rootOf Toy.H (ghostLeaves ToyRun.hist) ∧
      rootOf Toy.H (ghostLeaves ToyRun.hist) = 96 ∧
      pext.withdraw [39, 5, 3, 8, 96] = W2 := by
  refine ⟨by decide, rfl, by decide, by decide, rfl⟩

/-- **Non-vacuity of `refinePL_run`**: every premise holds on the toy, with the LeanIMT module's real
fold for the membership facts and a depth-2 withdrawal path. -/
theorem refinePL_run_toy : ∃ txs st, txs.map eraseSnap = txsOf ToyRun.ext ToyRun.hist ∧
    Run' (supOf Toy.E ToyRun.hist) txs st ∧
    RepP Toy.H Toy.E (supOf Toy.E ToyRun.hist) (ghostLeaves ToyRun.hist) ToyRun.σ3 st :=
  refinePL_run ToyRun.hG0 ToyRun.hRB ToyRun.hEnv ToyRun.hD ToyRun.hTP ToyRun.hWP ToyRun.hA ToyRun.hC hPF ToyRun.hinj
    ToyRun.hacc ToyRun.hC1 ToyRun.hEx hPT ToyRun.hcr

/-! ## 2. The global premise fails on the same history -/

/-- A path that folds the ballast word 26 to the root 49 of `[9, 39]`. -/
def B26 : MPath := mkPath [(false, 22)] (by decide)

/-- **The old global premise is false on the toy history.** With the bad event `LeanImt.Bad` `CollC`,
`TreeHyp` fails: the ballast word 26 is an input word, and the path `B26` folds it to the root
of the prefix `[9, 39]` through the pair `(26, 22)`, which collides with the tree pair `(9, 39)`.
Nobody supplied this path. -/
theorem old_premise_false_on_toy :
    ¬ TreeHyp (CollC Toy.H) (ghostLeaves ToyRun.hist) (inputWords Toy.E ToyRun.ext ToyRun.hist) := by
  intro hTH
  have hL : ToyRun.leavesT.take 2 <+: ghostLeaves ToyRun.hist := List.take_prefix _ _
  have hw : (26 : Nat) ∈ inputWords Toy.E ToyRun.ext ToyRun.hist := by decide
  refine hTH.no_bad _ hL 26 hw ⟨B26.len, B26.idx, B26.sib, by decide, Or.inl ?_⟩
  exact ⟨26, 22, 9, 39, by decide, by decide, by decide, by decide⟩

/-! ## 3. Control (a): a bad event planted on the retained path -/

/-- The internal node value 49 (`Toy.H 9 39`) folded to the root 96 along the sibling 46. -/
def B49 : MPath := mkPath [(false, 46)] (by decide)

/-- **Control (a).** The planted path folds 49 to the root of `[9, 39, 46]`, 49 is not a leaf,
`binding_mem_or_bad` takes the bad branch, and `PathTreeHyp` rejects every input list that
contains this input. -/
theorem control_planted_bad :
    B49.fold Toy.H 49 = rootOf Toy.H ToyRun.leavesT ∧ (49 : Nat) ∉ ToyRun.leavesT ∧
      Bad Toy.H (imtOf Toy.H ToyRun.leavesT).depth ToyRun.leavesT 49 B49.active ∧
      ∀ Q, (49, B49) ∈ Q → ¬ PathTreeHyp Toy.H ToyRun.leavesT Q := by
  have hf : B49.fold Toy.H 49 = rootOf Toy.H ToyRun.leavesT := by decide
  have hn : (49 : Nat) ∉ ToyRun.leavesT := by decide
  have hb : Bad Toy.H (imtOf Toy.H ToyRun.leavesT).depth ToyRun.leavesT 49 B49.active :=
    (binding_mem_or_bad Toy.H ToyRun.leavesT 49 B49.len B49.idx B49.sib (by decide) hf).resolve_left hn
  exact ⟨hf, hn, hb, fun Q hq hPT => hPT.no_bad _ (List.prefix_refl _) _ hq hf hb⟩

/-! ## 4. Control (c): zero-valued input 0 gets no exemption -/

/-- A transfer that spends a zero-valued input 0 (token 5, amount 0, salt 20: word 26, not a
leaf) and a ballast input 1 (salt 21: word 27). -/
def dZ : TransferData Toy.P where
  key := (0 : Nat)
  in1 := ⟨(5 : Nat), 0, (0 : Nat), (20 : Nat)⟩
  in2 := ⟨(5 : Nat), 0, (0 : Nat), (21 : Nat)⟩
  out1 := ⟨(5 : Nat), 0, (0 : Nat), (30 : Nat)⟩
  out2 := ⟨(5 : Nat), 0, (0 : Nat), (40 : Nat)⟩
  snapshot := 0

def extZ : Extractor Toy.P := ⟨fun _ => Toy.d1, fun _ => dZ, fun _ => ToyRun.dW⟩

/-- Input 0's retained path: sibling 69 folds 26 to the root 96 of `[9, 39, 46]`. -/
def Z : MPath := mkPath [(false, 69)] (by decide)

def pextZ : PathExt := ⟨fun _ => (Z, T0), fun _ => W2⟩

def histZ : List Call := [.transfer 26 27 35 45 96 0]

/-- **Control (c).** The zero-valued input 0 is membership-checked, its path folds it to the
root of `[9, 39, 46]`, and it is not a leaf, so `PathTreeHyp` is false for this transfer. -/
theorem control_zero_input0 :
    (dZ.in1.amount = 0 ∧ dZ.in2.isBallast) ∧
      (26, Z) ∈ checkedInputs Toy.E extZ pextZ histZ ∧
      ¬ PathTreeHyp Toy.H ToyRun.leavesT (checkedInputs Toy.E extZ pextZ histZ) := by
  have hq : (26, Z) ∈ checkedInputs Toy.E extZ pextZ histZ := by
    simp only [checkedInputs, histZ, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Call.checked, checkedT]
    exact List.mem_cons_self
  refine ⟨⟨rfl, rfl⟩, hq, fun hPT => ?_⟩
  exact absurd (pathTree_member hPT (List.prefix_refl _) hq (by decide)) (by decide)

/-- The over-narrowed variant: input 0 exempted when its amount is 0, like ballast input 1. -/
def checkedT_exempt (E : Enc Toy.P) (ext : Extractor Toy.P) (pext : PathExt) (x : List Nat) :
    List (Nat × MPath) :=
  (if (ext.transfer x).in1.amount = 0 then []
    else [(E.cm (ext.transfer x).in1.cm, (pext.transfer x).1)]) ++
    if (ext.transfer x).in2.amount = 0 then []
    else [(E.cm (ext.transfer x).in2.cm, (pext.transfer x).2)]

/-- **Control (c), refutation half.** The over-narrowed variant checks nothing for `histZ`, so
its per-path premise accepts the transfer that `control_zero_input0` rejects. -/
theorem control_zero_input0_exempt_accepts :
    checkedT_exempt Toy.E extZ pextZ [26, 27, 35, 45, 96, 0] = [] ∧
      PathTreeHyp Toy.H ToyRun.leavesT (checkedT_exempt Toy.E extZ pextZ [26, 27, 35, 45, 96, 0]) := by
  have he : checkedT_exempt Toy.E extZ pextZ [26, 27, 35, 45, 96, 0] = [] := rfl
  rw [he]
  exact ⟨rfl, fun _ h => (List.not_mem_nil h).elim, fun _ _ _ h => (List.not_mem_nil h).elim⟩

/-! ## 5. Positive control: the onto-hash obstruction, and the contrast -/

/-- **The global premise is false for every hash that is surjective in the second argument for
every fixed first argument** (`hH`; `LeanImt.collC_of_onto`, unchanged): any nonzero word has a bad
path at the empty prefix. Joint surjectivity or compression alone does not give `hH`. -/
theorem global_premise_false_of_onto (H : Nat → Nat → Nat) (hH : ∀ x r, ∃ s, H x s = r)
    {G W : List Nat} {w : Nat} (hw : w ∈ W) : ¬ TreeHyp (CollC H) G W := fun hTH =>
  hTH.no_bad [] List.nil_prefix w hw
    (Checks.collC_of_onto H hH [] w (hTH.nonzero w hw) List.not_mem_nil)

/-- A hash that is surjective in the second argument for every fixed first argument. -/
def Hx (a b : Nat) : Nat := a ^^^ b

theorem Hx_onto : ∀ x r, ∃ s, Hx x s = r := fun x r =>
  ⟨x ^^^ r, by show x ^^^ (x ^^^ r) = r; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]⟩

/-- Leaf 2 of `[1, 2]` with its honest path (sibling 1 on the left): `Hx 1 2 = 3`. -/
def X1 : MPath := mkPath [(true, 1)] (by decide)

/-- **Contrast.** For `Hx` (surjective in the second argument for every fixed first argument),
the per-path premise holds for the honest path of a member, while the global premise is false on
the same tree and word. -/
theorem onto_contrast :
    PathTreeHyp Hx [1, 2] [(2, X1)] ∧ ¬ TreeHyp (CollC Hx) [1, 2] [2] := by
  refine ⟨⟨?_, ?_⟩, global_premise_false_of_onto Hx Hx_onto (List.mem_singleton_self 2)⟩
  · intro q hq
    rw [List.mem_singleton.1 hq]
    decide
  · intro L hL q hq hf
    rw [List.mem_singleton.1 hq] at hf ⊢
    obtain ⟨k, hk, rfl⟩ : ∃ k, k ≤ 2 ∧ L = [1, 2].take k :=
      ⟨L.length, hL.length_le, List.prefix_iff_eq_take.1 hL⟩
    interval_cases k <;>
      first
      | exact absurd hf (by decide)
      | exact not_bad_of (by decide) (by decide) (by decide)

end LeanShieldedPool.Refine.PathToy
