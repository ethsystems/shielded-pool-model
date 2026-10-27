import RecipientGame.Basic

/-! Collision bounds for static, well-formed transfer templates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.Rejection

open GameCorrespondence

variable {P : LeanShieldedPool.PrimSpec}

/-- Every transfer guard except the three output-commitment collision checks. -/
def DeterministicGuard (d : TransferData P) (st : St P) : Prop :=
  st.rootInWindow d.snapshot ∧
  d.in1.ownedBy d.key ∧ d.in2.ownedBy d.key ∧
  st.inTreeAt d.snapshot d.in1.cm ∧
  (d.in2.isBallast ∨ st.inTreeAt d.snapshot d.in2.cm) ∧
  st.fresh d.nf1 ∧ st.fresh d.nf2 ∧ d.nf1 ≠ d.nf2 ∧
  d.in2.token = d.in1.token ∧ d.out1.token = d.in1.token ∧
  d.out2.token = d.in1.token ∧
  U128 d.in1.amount ∧ U128 d.in2.amount ∧
  U128 d.out1.amount ∧ U128 d.out2.amount ∧
  d.in1.amount + d.in2.amount = d.out1.amount + d.out2.amount

def OutputFresh (d : TransferData P) (st : St P) : Prop :=
  d.out1.cm ∉ st.leaves ∧ d.out2.cm ∉ st.leaves ∧ d.out1.cm ≠ d.out2.cm

theorem guard_iff (d : TransferData P) (st : St P) :
    d.guard st ↔ DeterministicGuard d st ∧ OutputFresh d st := by
  simp only [TransferData.guard, DeterministicGuard, OutputFresh]
  tauto

theorem deterministic_withSalts (d : TransferData P) (st : St P) (s1 s2 : P.Salt) :
    DeterministicGuard (withSalts d s1 s2) st ↔ DeterministicGuard d st := Iff.rfl

/-- All salt choices preserve deterministic validity, including after a collision. -/
def WellFormed : St P → List (TransferData P) → Prop
  | _, [] => True
  | st, d :: ds => DeterministicGuard d st ∧
      ∀ s1 s2, WellFormed ((withSalts d s1 s2).post st) ds

/-- Collision status in the unchecked sequence of post-states. -/
def Collision : St P → List (TransferData P) → Prop
  | _, [] => False
  | st, d :: ds => ¬ OutputFresh d st ∨ Collision (d.post st) ds

theorem rejection_iff_collision [SampleableType P.Salt]
    (st : St P) (ds sampled : List (TransferData P)) (wf : WellFormed st ds)
    (hs : sampled ∈ support (sampleWorld ds)) :
    runChecked st (sampled.map Tx.transfer) = none ↔ Collision st sampled := by
  classical
  induction ds generalizing st sampled with
  | nil => simp [sampleWorld] at hs; subst sampled; simp [runChecked, Collision]
  | cons d ds ih =>
    simp only [WellFormed] at wf
    simp [sampleWorld] at hs
    obtain ⟨s1, s2, rest, hr, rfl⟩ := hs
    have hd := (deterministic_withSalts d st s1 s2).mpr wf.1
    by_cases hf : OutputFresh (withSalts d s1 s2) st
    · have hg := (guard_iff _ _).mpr ⟨hd, hf⟩
      simpa [runChecked, stepChecked, hg, Collision, hf] using
        ih _ rest (wf.2 s1 s2) hr
    · have hg : ¬ (withSalts d s1 s2).guard st := fun h => hf ((guard_iff _ _).mp h).2
      simp [runChecked, stepChecked, hg, Collision, hf]

/-- A fixed-message commitment hits each target with probability at most 1/q. -/
structure CommitmentSpread [SampleableType P.Salt] (q : Nat) : Prop where
  positive : 0 < q
  point_bound : ∀ (note : Note P) (c : P.Commitment),
    Pr[fun s => P.commit note.token note.amount note.ownerPubkey s = c | $ᵗ P.Salt] ≤
      (q : ℝ≥0∞)⁻¹

def exposures (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (2 * m + 1) + exposures (m + 2) n

theorem exposures_closed (m n : Nat) :
    exposures m n = 2 * m * n + n * (2 * n - 1) := by
  induction n generalizing m with
  | zero => simp [exposures]
  | succ n ih =>
    rw [exposures, ih]
    cases n with
    | zero => simp
    | succ n =>
      have h1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
      have h2 : 2 * (n + 1 + 1) - 1 = 2 * n + 3 := by omega
      rw [h1, h2]
      ring

variable [SampleableType P.Salt]

theorem hit_list_le (q : Nat) (spread : CommitmentSpread (P := P) q)
    (note : Note P) (cs : List P.Commitment) :
    Pr[fun s => P.commit note.token note.amount note.ownerPubkey s ∈ cs | $ᵗ P.Salt] ≤
      (cs.length : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.mem_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    exact (probEvent_or_le _ _ _).trans (by
      calc
        _ ≤ (q : ℝ≥0∞)⁻¹ + (cs.length : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ :=
          add_le_add (spread.point_bound note c) ih
        _ = _ := by ring)

theorem sampleWorld_rejection_le (q : Nat) (spread : CommitmentSpread (P := P) q)
    (st : St P) (ds : List (TransferData P)) (wf : WellFormed st ds) :
    Pr[fun sampled => runChecked st (sampled.map Tx.transfer) = none | sampleWorld ds] ≤
      (exposures st.minted.length ds.length : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
  classical
  induction ds generalizing st with
  | nil => simp [sampleWorld, runChecked, exposures]
  | cons d ds ih =>
    let m := st.minted.length
    let r : ℝ≥0∞ := (q : ℝ≥0∞)⁻¹
    have hs1 := hit_list_le q spread d.out1 st.leaves
    have hs2 (s1 : P.Salt) := hit_list_le q spread d.out2
      ((withSalts d s1 s1).out1.cm :: st.leaves)
    simp only [sampleWorld, List.length_cons, exposures]
    have houter :
        Pr[fun sampled => runChecked st (sampled.map Tx.transfer) = none |
          (do let s1 ← $ᵗ P.Salt
              let s2 ← $ᵗ P.Salt
              let rest ← sampleWorld ds
              pure (withSalts d s1 s2 :: rest))] ≤
        (m : ℝ≥0∞) * r + ((m + 1 : Nat) : ℝ≥0∞) * r +
          (exposures (m + 2) ds.length : ℝ≥0∞) * r := by
      refine le_trans (probEvent_bind_le_probEvent_add
        (p := fun s1 => (withSalts d s1 s1).out1.cm ∈ st.leaves)
        (ε := ((m + 1 : Nat) : ℝ≥0∞) * r +
          (exposures (m + 2) ds.length : ℝ≥0∞) * r) ?_) ?_
      · intro s1 _ hf1
        refine le_trans (probEvent_bind_le_probEvent_add
          (p := fun s2 => (withSalts d s1 s2).out2.cm ∈
            (withSalts d s1 s1).out1.cm :: st.leaves)
          (ε := (exposures (m + 2) ds.length : ℝ≥0∞) * r) ?_) ?_
        · intro s2 _ hf2
          have hf : OutputFresh (withSalts d s1 s2) st := by
            simp only [List.mem_cons, not_or] at hf2
            exact ⟨hf1, hf2.2, Ne.symm hf2.1⟩
          have hg := (guard_iff _ _).mpr
            ⟨(deterministic_withSalts d st s1 s2).mpr wf.1, hf⟩
          simpa [probEvent_bind_pure_comp, Function.comp_def, runChecked,
            stepChecked, hg, TransferData.post, m, r] using
            ih ((withSalts d s1 s2).post st) (wf.2 s1 s2)
        · exact add_le_add (by simpa [St.leaves, m, r, withSalts, Note.cm] using hs2 s1) le_rfl
      · have hfirst : Pr[fun s1 => (withSalts d s1 s1).out1.cm ∈ st.leaves |
              $ᵗ P.Salt] ≤ (m : ℝ≥0∞) * r := by
          simpa [St.leaves, m, r, withSalts, Note.cm] using hs1
        calc
          _ ≤ (m : ℝ≥0∞) * r +
              (((m + 1 : Nat) : ℝ≥0∞) * r +
                (exposures (m + 2) ds.length : ℝ≥0∞) * r) := add_le_add hfirst le_rfl
          _ = _ := by ring
    exact houter.trans_eq (by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      dsimp [m, r]
      ring)

theorem exposures_mono {m m' n n' : Nat} (hm : m ≤ m') (hn : n ≤ n') :
    exposures m n ≤ exposures m' n' := by
  rw [exposures_closed, exposures_closed]
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) hn)
    (Nat.mul_le_mul hn (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hn) 1))

/-- The setup is an accepted run; both supported worlds satisfy the static guard class. -/
structure WellFormedAdversary (sup : P.Token → Prop) (setup : List (Tx P))
    (adv : Adversary P) (m : Nat) where
  initial : St P
  setup_run : Run sup setup initial
  leaf_bound : initial.minted.length ≤ m
  worlds : ∀ a ∈ support adv.chooseWorlds,
    WellFormed initial a.1 ∧ WellFormed initial a.2.1

noncomputable def delta (m n q : Nat) : ℝ := (2 * m * n + n * (2 * n - 1) : Nat) / (q : ℝ)

theorem delta_eq (m n q : Nat) :
    delta m n q = (exposures m n : ℝ) / (q : ℝ) := by rw [exposures_closed]; rfl

theorem draws_rejection_le (q : Nat) (spread : CommitmentSpread (P := P) q)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m)
    (length_bound : ∀ a ∈ support adv.chooseWorlds, a.1.length ≤ n) :
    Pr[fun draw => rejected sup draw = true | draws setup adv] ≤
      (exposures m n : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
  classical
  unfold draws
  apply probEvent_bind_le_of_forall_le
  intro a ha
  rcases a with ⟨ds0, ds1, state⟩
  by_cases hp : RecipientPair ds0 ds1
  · simp only [hp, if_pos]
    apply probEvent_bind_le_of_forall_le
    intro b _
    have hlen : ds0.length = ds1.length := by
      simpa [projectWorld] using PoolGame.lengths_match_of_legalChallenge hp
    have hwb : WellFormed W.initial (if b then ds1 else ds0) := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (W.worlds _ ha).1
      · exact (W.worlds _ ha).2
    have hlb : (if b then ds1 else ds0).length ≤ n := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact length_bound _ ha
      · rw [← hlen]; exact length_bound _ ha
    have h := sampleWorld_rejection_le q spread W.initial _ hwb
    have hb : (exposures W.initial.minted.length (if b then ds1 else ds0).length : ℝ≥0∞) *
        (q : ℝ≥0∞)⁻¹ ≤ (exposures m n : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast exposures_mono W.leaf_bound hlb
    have hr := runChecked_complete W.setup_run
    simpa [probEvent_bind_pure_comp, Function.comp_def, rejected, runChecked_append, hr] using h.trans hb
  · simp [hp, rejected]

theorem rejectionProbability_le (q : Nat) (spread : CommitmentSpread (P := P) q)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m)
    (length_bound : ∀ a ∈ support adv.chooseWorlds, a.1.length ≤ n) :
    rejectionProbability sup setup adv ≤ delta m n q := by
  have h := draws_rejection_le q spread sup setup adv m n W length_bound
  have hfinite : (exposures m n : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.ne_of_gt spread.positive))
  have hr := ENNReal.toReal_mono hfinite h
  rw [delta_eq]
  simpa [rejectionProbability, ← probEvent_eq_eq_probOutput,
    probEvent_bind_pure_comp, Function.comp_def, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv] using hr

noncomputable def rejectionBound (q : Nat) (spread : CommitmentSpread (P := P) q)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m)
    (length_bound : ∀ a ∈ support adv.chooseWorlds, a.1.length ≤ n) :
    RecipientGame.RejectionBound sup setup adv where
  δ := delta m n q
  rejection_le := rejectionProbability_le q spread sup setup adv m n W length_bound

theorem advantage_le [DecidableEq P.Commitment] [SampleableType P.Nullifier]
    (q : Nat) (spread : CommitmentSpread (P := P) q)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m) (H : BoundAssumptions adv n) :
    advantage sup setup adv ≤ 2 * n * H.primitives.εHiding + delta m n q / 2 :=
  advantage_le_of_rejection_bound sup setup adv n H
    (rejectionBound q spread sup setup adv m n W H.length_bound)

omit [SampleableType P.Salt] in
theorem setup_leaves_le {sup : P.Token → Prop} {setup : List (Tx P)} {st : St P}
    (run : Run sup setup st) : st.minted.length ≤ 2 * setup.length := by
  induction run with
  | empty => simp [St.empty]
  | step run step ih =>
    cases step <;> simp only [DepositData.post, TransferData.post, WithdrawData.post,
      List.length_append, List.length_cons, List.length_nil] at * <;> omega

theorem advantage_le_history [DecidableEq P.Commitment] [SampleableType P.Nullifier]
    (q : Nat) (spread : CommitmentSpread (P := P) q)
    (sup : P.Token → Prop) (setup : List (Tx P)) (adv : Adversary P) (m n : Nat)
    (W : WellFormedAdversary sup setup adv m) (H : BoundAssumptions adv n) :
    advantage sup setup adv ≤ 2 * n * H.primitives.εHiding +
      delta (2 * setup.length) n q / 2 := by
  let W' : WellFormedAdversary sup setup adv (2 * setup.length) :=
    { W with leaf_bound := setup_leaves_le W.setup_run }
  exact advantage_le q spread sup setup adv _ n W' H

structure SaltInjective (P : PrimSpec) : Prop where
  injective : ∀ token amount pubkey, Function.Injective (P.commit token amount pubkey)

theorem spread_of_injective [Fintype P.Salt] (I : SaltInjective P) :
    CommitmentSpread (P := P) (Fintype.card P.Salt) := by
  classical
  refine ⟨Fintype.card_pos, ?_⟩
  intro note c
  by_cases h : ∃ s, P.commit note.token note.amount note.ownerPubkey s = c
  · obtain ⟨s0, hs⟩ := h
    have he : (fun s => P.commit note.token note.amount note.ownerPubkey s = c) =
        (fun s => s = s0) := by
      funext s
      apply propext
      rw [← hs]
      exact (I.injective _ _ _).eq_iff
    rw [he, probEvent_eq_eq_probOutput, probOutput_uniformSample]
  · have hz : ∀ s, ¬ P.commit note.token note.amount note.ownerPubkey s = c := by
      simpa using h
    simp [hz]

namespace Fixture

abbrev Prim := SaltCollision.primitives

def adversary (observer : OracleComp (PoolGame.observerSpec (gamePrim Prim)) Bool) : Adversary Prim where
  State := Unit
  chooseWorlds := pure ([SaltCollision.transfer], [SaltCollision.transfer], ())
  distinguish := fun _ => observer

theorem legal : RecipientPair [SaltCollision.transfer] [SaltCollision.transfer] := by
  exact SaltCollision.world_legal

theorem world_wellFormed :
    WellFormed SaltCollision.initial [SaltCollision.transfer] := by
  exact ⟨((guard_iff _ _).mp SaltCollision.transfer_guard).1, fun _ _ => trivial⟩

noncomputable def wellFormed (observer : OracleComp (PoolGame.observerSpec (gamePrim Prim)) Bool) :
    WellFormedAdversary (fun _ => True) [Tx.deposit SaltCollision.deposit] (adversary observer) 1 where
  initial := SaltCollision.initial
  setup_run := SaltCollision.setup_run
  leaf_bound := by simp [SaltCollision.initial, DepositData.post, St.empty]
  worlds := by
    intro a ha
    simp only [adversary, support_pure] at ha
    subst a
    exact ⟨world_wellFormed, world_wellFormed⟩

theorem salt_injective : SaltInjective Prim := ⟨fun _ _ _ => Function.injective_id⟩

theorem spread : CommitmentSpread (P := Prim) 4 := spread_of_injective salt_injective

theorem length_bound (observer : OracleComp (PoolGame.observerSpec (gamePrim Prim)) Bool) :
    ∀ a ∈ support (adversary observer).chooseWorlds, a.1.length ≤ 1 := by
  intro a ha
  simp only [adversary, support_pure] at ha
  subst a
  simp

theorem rejection_eq_five_eighths (observer : OracleComp (PoolGame.observerSpec (gamePrim Prim)) Bool) :
    rejectionProbability (fun _ => True) [Tx.deposit SaltCollision.deposit] (adversary observer) = 5 / 8 := by
  have hc (s1 s2 : Fin 4) :
      runChecked SaltCollision.initial
        [Tx.transfer (withSalts SaltCollision.transfer s1 s2)] = none ↔
          s1 = 0 ∨ s2 = 0 ∨ s1 = s2 := by
    have hs : [withSalts SaltCollision.transfer s1 s2] ∈
        support (sampleWorld [SaltCollision.transfer]) := by simp [sampleWorld]
    have h := rejection_iff_collision _ _ _ world_wellFormed hs
    simp only [Collision, or_false, List.map_cons, List.map_nil] at h
    rw [h]
    simp [OutputFresh, SaltCollision.initial, DepositData.post,
      SaltCollision.deposit, St.empty, St.leaves, withSalts, Note.cm,
      SaltCollision.transfer, SaltCollision.note]
    tauto
  have hp : Pr[fun sampled => runChecked SaltCollision.initial
      (sampled.map Tx.transfer) = none | sampleWorld [SaltCollision.transfer]] = 5 / 8 := by
    simp only [sampleWorld, pure_bind]
    simp only [probEvent_bind_eq_sum_fintype, probOutput_uniformSample,
      Fintype.card_fin, probEvent_pure]
    simp only [Fin.sum_univ_succ]
    norm_num [hc, Function.comp_def, Prim, SaltCollision.primitives, Fin.ext_iff]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_inv]
  unfold rejectionProbability draws
  simp only [adversary, pure_bind, legal, ↓reduceIte]
  have he : Pr[= true | do
      let b ← $ᵗ Bool
      let sampled ← sampleWorld [SaltCollision.transfer]
      pure (rejected (fun _ => True)
        (some ((), b, [Tx.deposit SaltCollision.deposit] ++ sampled.map Tx.transfer) :
          Draw (adversary observer)))] = 5 / 8 := by
    rw [probOutput_bind_of_const ($ᵗ Bool) (r := 5 / 8)]
    · simp
    · intro b _
      simpa [← probEvent_eq_eq_probOutput, probEvent_bind_pure_comp,
        Function.comp_def, rejected, runChecked, stepChecked,
        SaltCollision.deposit_guard, SaltCollision.initial] using hp
  simpa [bind_assoc, rejected] using congrArg ENNReal.toReal he

theorem rejection_le_five_eighths (observer : OracleComp (PoolGame.observerSpec (gamePrim Prim)) Bool) :
    rejectionProbability (fun _ => True) [Tx.deposit SaltCollision.deposit] (adversary observer) ≤ 5 / 8 :=
  le_of_eq (rejection_eq_five_eighths observer)

theorem advantage_le (observer : OracleComp (PoolGame.observerSpec (gamePrim Prim)) Bool)
    (H : BoundAssumptions (adversary observer) 1) :
    advantage (fun _ => True) [Tx.deposit SaltCollision.deposit] (adversary observer) ≤
      2 * H.primitives.εHiding + 5 / 16 := by
  have h := advantage_le_of_rejection_bound (fun _ => True) [Tx.deposit SaltCollision.deposit]
    (adversary observer) 1 H
    ⟨5 / 8, rejection_le_five_eighths observer⟩
  norm_num at h ⊢
  exact h

end Fixture

namespace Funded

abbrev Prim (k : Nat) : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool
  Salt := Fin (k + 8)
  Commitment := Fin (k + 8)
  Nullifier := Fin (k + 8)
  derivePub := id
  commit := fun _ _ _ s => s
  nullify := fun cm _ => cm

def note (k : Nat) (owner : Bool) (s : Fin 8) : Note (Prim k) where
  token := ()
  amount := 1
  ownerPubkey := owner
  salt := ⟨s.val, by have := s.isLt; omega⟩

def deposit (k : Nat) (s : Fin 8) : DepositData (Prim k) := ⟨note k false s, ()⟩

def setup (k : Nat) : List (Tx (Prim k)) := [.deposit (deposit k 0), .deposit (deposit k 1)]

noncomputable def initial (k : Nat) : St (Prim k) :=
  (deposit k 1).post ((deposit k 0).post (St.empty (Prim k) (fun _ => True)))

def transfer (k : Nat) (recipient : Bool) : TransferData (Prim k) where
  key := false
  in1 := note k false 0
  in2 := note k false 1
  out1 := note k recipient 2
  out2 := note k recipient 3
  snapshot := 2

theorem setup_run (k : Nat) : Run (fun _ => True) (setup k) (initial k) := by
  have h0 : (deposit k 0).guard (St.empty (Prim k) (fun _ => True)) := by
    norm_num [DepositData.guard, deposit, note, St.empty, St.leaves, U128, maxU128]
  have h1 : (deposit k 1).guard ((deposit k 0).post (St.empty (Prim k) (fun _ => True))) := by
    norm_num [DepositData.guard, DepositData.post, deposit, note, St.empty, St.leaves,
      Note.cm, U128, maxU128, Fin.ext_iff]
  exact Run.step (Run.step Run.empty (Step.deposit h0)) (Step.deposit h1)

theorem transfer_guard (k : Nat) (recipient : Bool) :
    (transfer k recipient).guard (initial k) := by
  norm_num [TransferData.guard, transfer, initial, DepositData.post, deposit, note,
    St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy, Note.isBallast,
    St.inTreeAt, St.leaves, St.fresh, TransferData.nf1, TransferData.nf2, Note.nf,
    Note.cm, U128, maxU128, Prim, Fin.ext_iff]
  simp only [Fin.ext_iff]
  norm_num

theorem world_wellFormed (k : Nat) (recipient : Bool) :
    WellFormed (initial k) [transfer k recipient] :=
  ⟨((guard_iff _ _).mp (transfer_guard k recipient)).1, fun _ _ => trivial⟩

theorem legal (k : Nat) : RecipientPair [transfer k false] [transfer k true] := by
  simp [RecipientPair, projectWorld, PoolGame.LegalChallenge, PoolGame.RecipientOnly,
    transferWitness, transfer, note]

theorem different_worlds (k : Nat) : [transfer k false] ≠ [transfer k true] := by
  intro h
  have ho := congrArg (fun ds : List (TransferData (Prim k)) =>
    ds.map (fun d => d.out1.ownerPubkey)) h
  simp [transfer, note] at ho

def adversary (k : Nat) (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    Adversary (Prim k) where
  State := Unit
  chooseWorlds := pure ([transfer k false], [transfer k true], ())
  distinguish := fun _ => observer

noncomputable def wellFormed (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    WellFormedAdversary (fun _ => True) (setup k) (adversary k observer) 2 where
  initial := initial k
  setup_run := setup_run k
  leaf_bound := by simp [initial, DepositData.post, St.empty]
  worlds := by
    intro a ha
    simp only [adversary, support_pure] at ha
    subst a
    exact ⟨world_wellFormed k false, world_wellFormed k true⟩

theorem salt_injective (k : Nat) : SaltInjective (Prim k) :=
  ⟨fun _ _ _ => Function.injective_id⟩

theorem spread (k : Nat) : CommitmentSpread (P := Prim k) (k + 8) := by
  simpa only [Prim, Fintype.card_fin] using spread_of_injective (salt_injective k)

theorem length_bound (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    ∀ a ∈ support (adversary k observer).chooseWorlds, a.1.length ≤ 1 := by
  intro a ha
  simp only [adversary, support_pure] at ha
  subst a
  simp

theorem rejection_le (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    rejectionProbability (fun _ => True) (setup k) (adversary k observer) ≤
      5 / (k + 8 : ℝ) := by
  simpa [delta] using rejectionProbability_le (k + 8) (spread k) (fun _ => True) (setup k)
    (adversary k observer) 2 1 (wellFormed k observer) (length_bound k observer)

theorem advantage_le (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool)
    (H : BoundAssumptions (adversary k observer) 1) :
    advantage (fun _ => True) (setup k) (adversary k observer) ≤
      2 * H.primitives.εHiding + (5 / (k + 8 : ℝ)) / 2 := by
  simpa [delta] using Rejection.advantage_le (k + 8) (spread k) (fun _ => True) (setup k)
    (adversary k observer) 2 1 (wellFormed k observer) H

def commitmentScheme (k : Nat) :
    CommitmentScheme Unit (Unit × Nat × Bool) (Fin (k + 8)) (Fin (k + 8)) where
  setup := pure ()
  commit := fun _ _ => do
    let s ← $ᵗ Fin (k + 8)
    pure (s, s)
  verify := fun _ _ c s => c == s

def prf (k : Nat) : PRFScheme Bool (Fin (k + 8)) (Fin (k + 8)) where
  keygen := pure false
  eval := fun _ cm => cm

theorem fair_guess (guess : ProbComp Bool) :
    Pr[= true | do let b ← $ᵗ Bool; let g ← guess; pure (b == g)] = 1 / 2 := by
  rw [probOutput_bind_uniformBool]
  simp

theorem hiding_zero (k : Nat)
    (A : CommitmentScheme.HidingAdv Unit (Unit × Nat × Bool) (Fin (k + 8))) :
    (commitmentScheme k).hidingAdvantage A = 0 := by
  have hf : Pr[= true | (commitmentScheme k).hidingExp A] = 1 / 2 := by
    simp only [CommitmentScheme.hidingExp, commitmentScheme, pure_bind]
    rw [probOutput_bind_of_const (A.chooseMessages ()) (r := 1 / 2)]
    · simp
    · rintro ⟨m0, m1, state⟩ _
      simpa only [bind_assoc, pure_bind] using fair_guess
        (do let s ← $ᵗ Fin (k + 8); A.distinguish state s)
  simp [CommitmentScheme.hidingAdvantage, hf]

theorem prf_bound (k : Nat) (A : PRFScheme.PRFAdversary (Fin (k + 8)) (Fin (k + 8))) :
    (prf k).prfAdvantage A ≤ 1 := by
  have hi (p : ProbComp Bool) : (Pr[= true | p]).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (probOutput_le_one (mx := p) (x := true))
  have hlo (p : ProbComp Bool) : 0 ≤ (Pr[= true | p]).toReal := ENNReal.toReal_nonneg
  unfold PRFScheme.prfAdvantage
  rw [abs_le]
  constructor <;> linarith [hi ((prf k).prfRealExp A), hi (PRFScheme.prfIdealExp A),
    hlo ((prf k).prfRealExp A), hlo (PRFScheme.prfIdealExp A)]

noncomputable def assumptions (k : Nat) : PoolGame.PoolAssumptions (gamePrim (Prim k)) where
  cs := commitmentScheme k
  cs_commit := fun _ _ _ => rfl
  prf := prf k
  prf_eval := fun _ _ => rfl
  εHiding := 0
  hiding_bound := fun A => le_of_eq (hiding_zero k A)
  εPRF := 1
  prf_bound := prf_bound k

noncomputable def boundAssumptions (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    BoundAssumptions (adversary k observer) 1 where
  primitives := assumptions k
  hiding_nonneg := le_rfl
  length_bound := length_bound k observer

theorem concrete_advantage_le (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    advantage (fun _ => True) (setup k) (adversary k observer) ≤ (5 / (k + 8 : ℝ)) / 2 := by
  simpa [boundAssumptions, assumptions] using advantage_le k observer (boundAssumptions k observer)

end Funded

end LeanShieldedPool.RecipientGame.Rejection
