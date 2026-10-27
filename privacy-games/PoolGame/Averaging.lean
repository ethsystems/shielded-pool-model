import PoolGame.Summand

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace PoolGame.Averaging

/-- The real probability of a bind is a weighted sum over its joint prefix. -/
theorem probOutput_bind_toReal {α β : Type} (pref : ProbComp α)
    (f : α → ProbComp β) (b : β) :
    (Pr[= b | pref >>= f]).toReal =
      ∑' a, (Pr[= a | pref]).toReal * (Pr[= b | f a]).toReal := by
  rw [probOutput_bind_eq_tsum, ENNReal.tsum_toReal_eq
    (fun _ => ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
  simp only [ENNReal.toReal_mul]

/-- Probability weights are summable and have total mass one. -/
theorem weight_sum {α : Type} (pref : ProbComp α) :
    (∑' a, (Pr[= a | pref]).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun _ => probOutput_ne_top),
    tsum_probOutput_of_liftM_PMF, ENNReal.toReal_one]

theorem weights_summable {α : Type} (pref : ProbComp α) :
    Summable (fun a => (Pr[= a | pref]).toReal) :=
  ENNReal.summable_toReal tsum_probOutput_ne_top

theorem weighted_output_summable {α : Type} (pref : ProbComp α)
    (f : α → ProbComp Bool) :
    Summable (fun a => (Pr[= a | pref]).toReal * (Pr[= true | f a]).toReal) := by
  apply (weights_summable pref).of_nonneg_of_le
  · intro a; positivity
  · intro a
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg
      (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (probOutput_le_one (mx := f a) (x := true)))

/-- Moving absolute value through expectation preserves the whole joint prefix. -/
theorem boolDistAdvantage_bind_le {α : Type} (pref : ProbComp α)
    (f g : α → ProbComp Bool) :
    (pref >>= f).boolDistAdvantage (pref >>= g) ≤
      ∑' a, (Pr[= a | pref]).toReal * (f a).boolDistAdvantage (g a) := by
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_bind_toReal, probOutput_bind_toReal,
    ← (weighted_output_summable pref f).tsum_sub (weighted_output_summable pref g)]
  calc
    _ ≤ ∑' a, |(Pr[= a | pref]).toReal * (Pr[= true | f a]).toReal -
      (Pr[= a | pref]).toReal * (Pr[= true | g a]).toReal| :=
        by
          simpa only [Real.norm_eq_abs] using
            (norm_tsum_le_tsum_norm ((weighted_output_summable pref f).sub
              (weighted_output_summable pref g)).norm)
    _ = _ := by
      apply tsum_congr
      intro a
      rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]

/-- A constant distance bound is needed only on the sampled support. -/
theorem boolDistAdvantage_bind_le_const {α : Type} (pref : ProbComp α)
    (f g : α → ProbComp Bool) (c : ℝ)
    (h : ∀ a ∈ support pref, (f a).boolDistAdvantage (g a) ≤ c) :
    (pref >>= f).boolDistAdvantage (pref >>= g) ≤ c := by
  have hs : Summable (fun a => (Pr[= a | pref]).toReal *
      (f a).boolDistAdvantage (g a)) := by
    have ht := ((weighted_output_summable pref f).sub
      (weighted_output_summable pref g)).abs
    simpa only [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
      ProbComp.boolDistAdvantage] using ht
  refine (boolDistAdvantage_bind_le pref f g).trans ?_
  calc
    _ ≤ ∑' a, (Pr[= a | pref]).toReal * c := by
      apply Summable.tsum_le_tsum _ hs ((weights_summable pref).mul_right c)
      intro a
      by_cases ha : a ∈ support pref
      · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
      · rw [probOutput_eq_zero_of_not_mem_support ha]
        simp
    _ = c := by rw [(weights_summable pref).tsum_mul_right, weight_sum, one_mul]

variable {P : PrimSpec} [SampleableType P.Salt]

/-- An illegal challenge uses the same constant guess in both branches. -/
noncomputable def challengeBranch (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State) (b : Bool) : ProbComp Bool := by
  classical
  exact if LegalChallenge ws₀ ws₁ then do
    let log ← publish (if b then ws₁ else ws₀)
    simulateQ (observerImpl log) (adv.distinguish st)
  else pure false

theorem challengeBranch_illegal_distance (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (h : ¬ LegalChallenge ws₀ ws₁) :
    (challengeBranch adv ws₀ ws₁ st true).boolDistAdvantage
      (challengeBranch adv ws₀ ws₁ st false) = 0 := by
  simp [challengeBranch, h, ProbComp.boolDistAdvantage]

/-- Fair rejection has zero signed success bias for each illegal sample. -/
theorem illegal_signed_bias (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (h : ¬ LegalChallenge ws₀ ws₁) :
    (Pr[= true | transferChallengeExp adv ws₀ ws₁ st]).toReal - 1 / 2 = 0 := by
  simp [transferChallengeExp_of_illegal adv ws₀ ws₁ st h]

/-- The guarded branches give the same win distribution as the frozen game. -/
theorem challenge_coin_decomposition (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State) (x : Bool) :
    Pr[= x | transferChallengeExp adv ws₀ ws₁ st] = Pr[= x | do
      let b ← $ᵗ Bool
      let z ← if b then challengeBranch adv ws₀ ws₁ st true
        else challengeBranch adv ws₀ ws₁ st false
      pure (b == z)] := by
  classical
  by_cases h : LegalChallenge ws₀ ws₁
  · rw [transferChallengeExp_of_legal adv ws₀ ws₁ st h]
    apply probOutput_bind_congr'
    intro b
    cases b <;> simp [challengeBranch, h]
  · rw [transferChallengeExp_of_illegal adv ws₀ ws₁ st h]
    cases x <;> simp [challengeBranch, h]

/-- The first phase remains one shared sample, including the adversary state. -/
theorem transferIndAdvantage_eq_half_distance (adv : TransferIndAdv P) :
    transferIndAdvantage adv =
      (adv.chooseWorlds >>= fun (ws₀, ws₁, st) =>
        challengeBranch adv ws₀ ws₁ st true).boolDistAdvantage
      (adv.chooseWorlds >>= fun (ws₀, ws₁, st) =>
        challengeBranch adv ws₀ ws₁ st false) / 2 := by
  let f := fun (a : List (TransferWitness P) × List (TransferWitness P) × adv.State) =>
    challengeBranch adv a.1 a.2.1 a.2.2 true
  let g := fun (a : List (TransferWitness P) × List (TransferWitness P) × adv.State) =>
    challengeBranch adv a.1 a.2.1 a.2.2 false
  have hp (x : Bool) : Pr[= x | transferIndExp adv] = Pr[= x | do
      let a ← adv.chooseWorlds
      let b ← $ᵗ Bool
      let z ← if b then f a else g a
      pure (b == z)] := by
    apply probOutput_bind_congr'
    intro a
    exact challenge_coin_decomposition adv a.1 a.2.1 a.2.2 x
  have hb := ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage
    adv.chooseWorlds f g
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half, ← hp true] at hb
  change 2 * transferIndAdvantage adv = _ at hb
  change transferIndAdvantage adv = (adv.chooseWorlds >>= f).boolDistAdvantage
    (adv.chooseWorlds >>= g) / 2
  linarith

variable [DecidableEq P.Commitment] [SampleableType P.Nullifier]

/-- Summing the frozen per-transfer bounds gives the fixed legal distance. -/
theorem legal_distance_le_length (A : PoolAssumptions P) (adv : TransferIndAdv P)
    (ws₀ ws₁ : List (TransferWitness P)) (st : adv.State)
    (h : LegalChallenge ws₀ ws₁) :
    (challengeBranch adv ws₀ ws₁ st true).boolDistAdvantage
      (challengeBranch adv ws₀ ws₁ st false) ≤ 4 * ws₀.length * A.εHiding := by
  classical
  simp only [challengeBranch, if_pos h, ↓reduceIte, Bool.false_eq_true]
  rw [show ∀ p q : ProbComp Bool, p.boolDistAdvantage q = q.boolDistAdvantage p
    from fun _ _ => abs_sub_comm _ _]
  refine (hybrid_bound adv ws₀ ws₁ st h).trans ?_
  calc
    _ ≤ ∑ _i ∈ Finset.range ws₀.length, 4 * A.εHiding := by
      apply Finset.sum_le_sum
      intro i hi
      exact Summand.legal_hybrid_step_distance_le A adv ws₀ ws₁ st h i
        (Finset.mem_range.mp hi)
    _ = _ := by simp; ring

/-- The left history length is bounded on the joint first-phase support. -/
def LengthBound (adv : TransferIndAdv P) (n : Nat) : Prop :=
  ∀ a ∈ support adv.chooseWorlds, a.1.length ≤ n

/-- Privacy of the frozen experiment, with an explicit nonnegative error bound. -/
theorem transferIndAdvantage_le (A : PoolAssumptions P) (hε : 0 ≤ A.εHiding)
    (adv : TransferIndAdv P) (n : Nat) (hlen : LengthBound adv n) :
    transferIndAdvantage adv ≤ 2 * n * A.εHiding := by
  rw [transferIndAdvantage_eq_half_distance]
  have hd := boolDistAdvantage_bind_le_const adv.chooseWorlds
    (fun a => challengeBranch adv a.1 a.2.1 a.2.2 true)
    (fun a => challengeBranch adv a.1 a.2.1 a.2.2 false) (4 * n * A.εHiding) (by
      intro a ha
      by_cases h : LegalChallenge a.1 a.2.1
      · exact (legal_distance_le_length A adv a.1 a.2.1 a.2.2 h).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hlen a ha)) (by norm_num)) hε)
      · rw [challengeBranch_illegal_distance adv a.1 a.2.1 a.2.2 h]
        positivity)
  linarith

/-- A real message makes the hiding bound nonvacuous. -/
theorem epsHiding_nonneg_of_message (A : PoolAssumptions P)
    (m : P.Token × Nat × P.PubKey) : 0 ≤ A.εHiding := by
  let red := Summand.hidingReduction (pure ()) m m
    (fun (_ : Unit) (_ : P.Commitment) => (pure false : ProbComp Bool))
  exact (abs_nonneg _).trans (A.hiding_bound red)

/-- Nonempty messages discharge the explicit sign condition. -/
theorem transferIndAdvantage_le_of_nonempty_message
    [Nonempty (P.Token × Nat × P.PubKey)] (A : PoolAssumptions P)
    (adv : TransferIndAdv P) (n : Nat) (hlen : LengthBound adv n) :
    transferIndAdvantage adv ≤ 2 * n * A.εHiding := by
  exact transferIndAdvantage_le A
    (epsHiding_nonneg_of_message A (Classical.choice inferInstance)) adv n hlen

namespace EmptyMessageCounterexample

abbrev primitives : PrimSpec where
  Token := Empty
  Address := Unit
  PubKey := Unit
  SpendKey := Unit
  Salt := Unit
  Commitment := Unit
  Nullifier := Unit
  derivePub := fun _ => ()
  commit := fun _ _ _ _ => ()
  nullify := fun _ _ => ()

noncomputable def assumptions : PoolAssumptions primitives where
  cs := {
    setup := pure ()
    commit := fun _ _ => pure ((), ())
    verify := fun _ _ _ _ => true }
  cs_commit := by intro t; exact t.elim
  prf := { keygen := pure (), eval := fun _ _ => () }
  prf_eval := by intros; rfl
  εHiding := -1
  hiding_bound := by
    classical
    intro adv
    obtain ⟨x, _⟩ := finSupport_nonempty_of_liftM_PMF (adv.chooseMessages ())
    exact x.1.1.elim
  εPRF := 1
  prf_bound := by
    intro adv
    unfold PRFScheme.prfAdvantage
    have hprob (p : ProbComp Bool) : (Pr[= true | p]).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (probOutput_le_one (mx := p) (x := true))
    exact abs_sub_le_iff.mpr
      ⟨(sub_le_self _ ENNReal.toReal_nonneg).trans (hprob _),
        (sub_le_self _ ENNReal.toReal_nonneg).trans (hprob _)⟩

def adversary : TransferIndAdv primitives where
  State := Unit
  chooseWorlds := pure ([], [], ())
  distinguish := fun _ => pure false

theorem length_bound : LengthBound adversary 1 := by
  intro a ha
  simp [adversary] at ha
  subst a
  simp

theorem advantage_zero : transferIndAdvantage adversary = 0 := by
  simp [transferIndAdvantage, transferIndExp, adversary, transferChallengeExp,
    LegalChallenge, publish]

/-- The requested statement is false without a sign or nonemptiness condition. -/
theorem requested_bound_false :
    ¬ transferIndAdvantage adversary ≤ 2 * (1 : Nat) * assumptions.εHiding := by
  rw [advantage_zero]
  norm_num [assumptions]

end EmptyMessageCounterexample

#print axioms probOutput_bind_toReal
#print axioms weight_sum
#print axioms weights_summable
#print axioms weighted_output_summable
#print axioms boolDistAdvantage_bind_le
#print axioms boolDistAdvantage_bind_le_const
#print axioms challengeBranch_illegal_distance
#print axioms illegal_signed_bias
#print axioms challenge_coin_decomposition
#print axioms transferIndAdvantage_eq_half_distance
#print axioms legal_distance_le_length
#print axioms transferIndAdvantage_le
#print axioms epsHiding_nonneg_of_message
#print axioms transferIndAdvantage_le_of_nonempty_message
#print axioms EmptyMessageCounterexample.assumptions
#print axioms EmptyMessageCounterexample.length_bound
#print axioms EmptyMessageCounterexample.advantage_zero
#print axioms EmptyMessageCounterexample.requested_bound_false

end PoolGame.Averaging
