import ChainGame.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame
open GameCorrespondence RecipientGame.Rejection
variable {P : PrimSpec}

abbrev NullifierTargets (P : PrimSpec) := List (P.SpendKey × P.Nullifier)

def NullifierHit (note : Note P) (targets : NullifierTargets P) : Prop :=
  ∃ target ∈ targets, note.nf target.1 = target.2

structure NullifierSpread [SampleableType P.Salt] (q : Nat) : Prop where
  positive : 0 < q
  point_bound : ∀ (note : Note P) (key : P.SpendKey) (nf : P.Nullifier),
    Pr[fun s => P.nullify (P.commit note.token note.amount note.ownerPubkey s) key = nf |
      $ᵗ P.Salt] ≤ (q : ℝ≥0∞)⁻¹

theorem nullifierSpread_of_injective [SampleableType P.Salt] (q : Nat)
    (spread : CommitmentSpread (P := P) q)
    (injective : ∀ key : P.SpendKey, Function.Injective (fun cm => P.nullify cm key)) :
    NullifierSpread (P := P) q := by
  classical
  refine ⟨spread.positive, ?_⟩
  intro note key nf
  by_cases hex : ∃ cm, P.nullify cm key = nf
  · obtain ⟨cm, hcm⟩ := hex
    refine (probEvent_mono (fun s _ hs => ?_)).trans (spread.point_bound note cm)
    exact injective key (hs.trans hcm.symm)
  · have he (s : P.Salt) : ¬ P.nullify (P.commit note.token note.amount note.ownerPubkey s) key = nf :=
      fun h => hex ⟨_, h⟩
    simp [he]

/-- Targets protect later input guards. They do not change execution or salt sampling. -/
def WellFormed (k : Nat) : St P → List (TransferData P) → List (Template P) → Prop
  | _, _, [] => True
  | st, history, t :: ts =>
    Backward history.length t.input1 ∧ Backward history.length t.input2 ∧
    DeterministicGuard (resolve history t) st ∧
    ∃ (first : NullifierTargets P) (second : P.Salt → NullifierTargets P),
      first.length ≤ k ∧ (∀ s1, (second s1).length ≤ k) ∧
      ∀ s1 s2,
        let d := RecipientGame.withSalts (resolve history t) s1 s2
        OutputFresh d st → ¬ NullifierHit d.out1 first →
          ¬ NullifierHit d.out2 (second s1) →
          WellFormed k (d.post st) (history ++ [d]) ts

theorem nullifier_hit_le [SampleableType P.Salt] (q : Nat)
    (spread : NullifierSpread (P := P) q) (note : Note P) (targets : NullifierTargets P) :
    Pr[fun s => NullifierHit { note with salt := s } targets | $ᵗ P.Salt] ≤
      (targets.length : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
  induction targets with
  | nil => simp [NullifierHit]
  | cons target targets ih =>
    have he (s : P.Salt) : NullifierHit { note with salt := s } (target :: targets) ↔
        P.nullify (P.commit note.token note.amount note.ownerPubkey s) target.1 = target.2 ∨
        NullifierHit { note with salt := s } targets := by
      simp [NullifierHit, Note.nf, Note.cm]
    simp only [he, List.length_cons, Nat.cast_add, Nat.cast_one]
    exact (probEvent_or_le _ _ _).trans (by
      calc
        _ ≤ (q : ℝ≥0∞)⁻¹ + (targets.length : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ :=
          add_le_add (spread.point_bound note target.1 target.2) ih
        _ = _ := by ring)

noncomputable def exposureBound (m n k qC qN : Nat) : ℝ≥0∞ :=
  (exposures m n : ℝ≥0∞) * (qC : ℝ≥0∞)⁻¹ +
    (2 * k * n : Nat) * (qN : ℝ≥0∞)⁻¹

theorem exposureBound_succ (m n k qC qN : Nat) :
    exposureBound m (n + 1) k qC qN =
      (m : ℝ≥0∞) * (qC : ℝ≥0∞)⁻¹ + (k : ℝ≥0∞) * (qN : ℝ≥0∞)⁻¹ +
      (((m + 1 : Nat) : ℝ≥0∞) * (qC : ℝ≥0∞)⁻¹ + (k : ℝ≥0∞) * (qN : ℝ≥0∞)⁻¹) +
      exposureBound (m + 2) n k qC qN := by
  simp only [exposureBound, exposures, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem sampleWorld_rejection_le [SampleableType P.Salt] (qC qN k : Nat)
    (spreadC : CommitmentSpread (P := P) qC) (spreadN : NullifierSpread (P := P) qN)
    (st : St P) (history : List (TransferData P)) (ts : List (Template P))
    (wf : WellFormed k st history ts) :
    Pr[fun ds => RecipientGame.runChecked st (ds.map Tx.transfer) = none | sampleWorld history ts] ≤
      exposureBound st.minted.length ts.length k qC qN := by
  classical
  induction ts generalizing st history with
  | nil => simp [sampleWorld, RecipientGame.runChecked, exposureBound, exposures]
  | cons t ts ih =>
    rcases wf with ⟨_, _, hd, first, second, hfirst, hsecond, hrest⟩
    let base := resolve history t
    let d := fun s1 s2 => RecipientGame.withSalts base s1 s2
    let m := st.minted.length
    let rC : ℝ≥0∞ := (qC : ℝ≥0∞)⁻¹
    let rN : ℝ≥0∞ := (qN : ℝ≥0∞)⁻¹
    have hs1 : Pr[fun s1 => (d s1 s1).out1.cm ∈ st.leaves ∨
          NullifierHit (d s1 s1).out1 first | $ᵗ P.Salt] ≤ (m : ℝ≥0∞) * rC + k * rN := by
      apply (probEvent_or_le _ _ _).trans
      apply add_le_add
      · simpa [St.leaves, d, base, RecipientGame.withSalts, Note.cm, m, rC] using
          hit_list_le qC spreadC base.out1 st.leaves
      · exact (nullifier_hit_le qN spreadN base.out1 first).trans (by
          dsimp [rN]; gcongr)
    have hs2 (s1 : P.Salt) :
        Pr[fun s2 => (d s1 s2).out2.cm ∈ (d s1 s1).out1.cm :: st.leaves ∨
          NullifierHit (d s1 s2).out2 (second s1) | $ᵗ P.Salt] ≤
          ((m + 1 : Nat) : ℝ≥0∞) * rC + k * rN := by
      apply (probEvent_or_le _ _ _).trans
      apply add_le_add
      · simpa [St.leaves, d, base, RecipientGame.withSalts, Note.cm, m, rC] using
          hit_list_le qC spreadC base.out2 ((d s1 s1).out1.cm :: st.leaves)
      · exact (nullifier_hit_le qN spreadN base.out2 (second s1)).trans (by
          dsimp [rN]; gcongr; exact hsecond s1)
    simp only [sampleWorld, List.length_cons, exposureBound_succ]
    refine le_trans (probEvent_bind_le_probEvent_add
      (p := fun s1 => (d s1 s1).out1.cm ∈ st.leaves ∨ NullifierHit (d s1 s1).out1 first)
      (ε := (((m + 1 : Nat) : ℝ≥0∞) * rC + k * rN) +
        exposureBound (m + 2) ts.length k qC qN) ?_) ?_
    · intro s1 _ h1
      simp only [not_or] at h1
      refine le_trans (probEvent_bind_le_probEvent_add
        (p := fun s2 => (d s1 s2).out2.cm ∈ (d s1 s1).out1.cm :: st.leaves ∨
          NullifierHit (d s1 s2).out2 (second s1))
        (ε := exposureBound (m + 2) ts.length k qC qN) ?_) ?_
      · intro s2 _ h2
        simp only [not_or, List.mem_cons] at h2
        have hf : OutputFresh (d s1 s2) st := ⟨h1.1, h2.1.2, Ne.symm h2.1.1⟩
        have hg := (guard_iff _ _).mpr
          ⟨(deterministic_withSalts base st s1 s2).mpr hd, hf⟩
        simpa [probEvent_bind_pure_comp, Function.comp_def, RecipientGame.runChecked,
          RecipientGame.stepChecked, hg, TransferData.post, m, d, base] using
          ih ((d s1 s2).post st) (history ++ [d s1 s2]) (hrest s1 s2 hf h1.2 h2.2)
      · exact add_le_add (hs2 s1) le_rfl
    · exact (add_le_add hs1 le_rfl).trans_eq (by dsimp [m, rC, rN]; ring)

theorem exposureBound_mono {m m' n n' : Nat} (hm : m ≤ m') (hn : n ≤ n')
    (k qC qN : Nat) : exposureBound m n k qC qN ≤ exposureBound m' n' k qC qN := by
  unfold exposureBound
  apply add_le_add
  · gcongr
    exact_mod_cast exposures_mono hm hn
  · gcongr

structure WellFormedAdversary [SampleableType P.Salt] (sup : P.Token → Prop)
    (setup : List (Tx P)) (adv : Adversary P) (m k : Nat) where
  initial : St P
  setup_run : Run sup setup initial
  leaf_bound : initial.minted.length ≤ m
  worlds : ∀ a ∈ support adv.chooseWorlds,
    WellFormed k initial [] a.1 ∧ WellFormed k initial [] a.2.1

noncomputable def delta (m n k qC qN : Nat) : ℝ :=
  (2 * m * n + n * (2 * n - 1) : Nat) / (qC : ℝ) + (2 * k * n : Nat) / (qN : ℝ)

theorem delta_no_nullifier_targets (m n qC qN : Nat) :
    delta m n 0 qC qN = RecipientGame.Rejection.delta m n qC := by
  simp [delta, RecipientGame.Rejection.delta]

theorem draws_rejection_le [SampleableType P.Salt] (qC qN k : Nat)
    (spreadC : CommitmentSpread (P := P) qC) (spreadN : NullifierSpread (P := P) qN)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m k)
    (length_bound : ∀ a ∈ support adv.chooseWorlds, a.1.length ≤ n) :
    Pr[fun draw => rejected sup draw = true | draws setup adv] ≤ exposureBound m n k qC qN := by
  classical
  unfold draws
  apply probEvent_bind_le_of_forall_le
  intro a ha
  rcases a with ⟨ts, us, state⟩
  by_cases hp : RecipientPair ts us
  · simp only [hp, if_pos]
    apply probEvent_bind_le_of_forall_le
    intro b _
    have hlen : ts.length = us.length := hp.2.2.length_eq
    have hwb : WellFormed k W.initial [] (if b then us else ts) := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (W.worlds _ ha).1
      · exact (W.worlds _ ha).2
    have hlb : (if b then us else ts).length ≤ n := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact length_bound _ ha
      · rw [← hlen]; exact length_bound _ ha
    have h := sampleWorld_rejection_le qC qN k spreadC spreadN W.initial [] _ hwb
    have hb := exposureBound_mono W.leaf_bound hlb k qC qN
    have hr := RecipientGame.runChecked_complete W.setup_run
    simpa [probEvent_bind_pure_comp, Function.comp_def, rejected, RecipientGame.runChecked_append, hr]
      using h.trans hb
  · simp [hp, rejected]

theorem rejectionProbability_le [SampleableType P.Salt] (qC qN k : Nat)
    (spreadC : CommitmentSpread (P := P) qC) (spreadN : NullifierSpread (P := P) qN)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m k)
    (length_bound : ∀ a ∈ support adv.chooseWorlds, a.1.length ≤ n) :
    rejectionProbability sup setup adv ≤ delta m n k qC qN := by
  have h := draws_rejection_le qC qN k spreadC spreadN sup setup adv m n W length_bound
  have hc : (qC : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.ne_of_gt spreadC.positive)
  have hn : (qN : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.ne_of_gt spreadN.positive)
  have hfinite : exposureBound m n k qC qN ≠ ⊤ := by
    simp only [exposureBound, ENNReal.add_ne_top]
    exact ⟨ENNReal.mul_ne_top (by simp) hc, ENNReal.mul_ne_top (by finiteness) hn⟩
  have hr := ENNReal.toReal_mono hfinite h
  rw [exposureBound, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hc)
    (ENNReal.mul_ne_top (by finiteness) hn)] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast] at hr
  rw [exposures_closed] at hr
  simpa [rejectionProbability, ← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp,
    Function.comp_def, delta, div_eq_mul_inv] using hr


theorem advantage_le_delta [SampleableType P.Salt] [DecidableEq P.Commitment]
    [SampleableType P.Nullifier] (qC qN k : Nat)
    (spreadC : CommitmentSpread (P := P) qC) (spreadN : NullifierSpread (P := P) qN)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m k) (H : BoundAssumptions adv n) :
    advantage sup setup adv ≤ 2 * n * H.primitives.εHiding + delta m n k qC qN / 2 := by
  have hp := advantage_le sup setup adv n H
  have hr := rejectionProbability_le qC qN k spreadC spreadN sup setup adv m n W H.length_bound
  linarith

end LeanShieldedPool.ChainGame
