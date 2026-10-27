import ChainGame.AdaptiveRejection

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame.Chain
open GameCorrespondence RecipientGame.Rejection

abbrev Prim := Funded.Prim

def note (k : Nat) (amount : Nat) (owner : Bool) (salt : Fin (k + 8)) : Note (Prim k) :=
  ⟨(), amount, owner, salt⟩

def deposit (k : Nat) : DepositData (Prim k) := ⟨note k 2 false 0, ()⟩

def setup (k : Nat) : List (Tx (Prim k)) := [.deposit (deposit k)]

noncomputable def initial (k : Nat) : St (Prim k) :=
  (deposit k).post (St.empty (Prim k) (fun _ => True))

def first (k : Nat) : Template (Prim k) where
  body := {
    key := false
    in1 := note k 2 false 0
    in2 := note k 0 false 1
    out1 := note k 1 false 2
    out2 := note k 1 false 3
    snapshot := 1 }

def second (k : Nat) (recipient : Bool) : Template (Prim k) where
  body := {
    key := false
    in1 := note k 1 false 2
    in2 := note k 1 false 3
    out1 := note k 1 recipient 4
    out2 := note k 1 recipient 5
    snapshot := 3 }
  input1 := some (0, false)
  input2 := some (0, true)

def world (k : Nat) (recipient : Bool) : List (Template (Prim k)) :=
  [first k, second k recipient]

def firstDraw (k : Nat) (s1 s2 : Fin (k + 8)) : TransferData (Prim k) :=
  RecipientGame.withSalts (resolve [] (first k)) s1 s2

def secondDraw (k : Nat) (recipient : Bool) (s1 s2 s3 s4 : Fin (k + 8)) :
    TransferData (Prim k) :=
  RecipientGame.withSalts (resolve [firstDraw k s1 s2] (second k recipient)) s3 s4

theorem setup_run (k : Nat) : Run (fun _ => True) (setup k) (initial k) := by
  apply Run.step Run.empty
  apply Step.deposit
  norm_num [DepositData.guard, deposit, note, St.empty, St.leaves, U128, maxU128]

theorem first_deterministic (k : Nat) :
    DeterministicGuard (resolve [] (first k)) (initial k) := by
  norm_num [DeterministicGuard, resolve, resolveNote, first, initial, DepositData.post,
    deposit, note, St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy,
    Note.isBallast, St.inTreeAt, St.leaves, St.fresh, TransferData.nf1, TransferData.nf2,
    Note.nf, Note.cm, U128, maxU128, Prim, Funded.Prim, Fin.ext_iff]

theorem second_deterministic (k : Nat) (recipient : Bool) (s1 s2 : Fin (k + 8))
    (hf : OutputFresh (firstDraw k s1 s2) (initial k))
    (h1 : ¬ NullifierHit (firstDraw k s1 s2).out1 [(false, 1)])
    (h2 : ¬ NullifierHit (firstDraw k s1 s2).out2 [(false, 1)]) :
    DeterministicGuard (resolve [firstDraw k s1 s2] (second k recipient))
      ((firstDraw k s1 s2).post (initial k)) := by
  have hs1 : s1 ≠ 1 := by simpa [NullifierHit, firstDraw, RecipientGame.withSalts,
    resolve, first, Note.nf, Note.cm, Prim, Funded.Prim] using h1
  have hs2 : s2 ≠ 1 := by simpa [NullifierHit, firstDraw, RecipientGame.withSalts,
    resolve, first, Note.nf, Note.cm, Prim, Funded.Prim] using h2
  have hf' : s1 ≠ 0 ∧ s2 ≠ 0 ∧ s1 ≠ s2 := by
    simpa [OutputFresh, firstDraw, RecipientGame.withSalts, resolve, first, initial,
      DepositData.post, deposit, note, St.empty, St.leaves, Note.cm, Prim, Funded.Prim] using hf
  norm_num [DeterministicGuard, resolve, resolveNote, output, second, firstDraw,
    RecipientGame.withSalts, first, initial, TransferData.post, DepositData.post, deposit, note,
    St.rootInWindow, St.pushWindow, rootWindow, St.empty, Note.ownedBy, Note.isBallast,
    St.inTreeAt, St.leaves, St.fresh, TransferData.nf1, TransferData.nf2, Note.nf,
    Note.cm, U128, maxU128, Prim, Funded.Prim, hs1, hs2, hf'.1, hf'.2.1, hf'.2.2]

theorem world_wellFormed (k : Nat) (recipient : Bool) :
    WellFormed 1 (initial k) [] (world k recipient) := by
  refine ⟨by simp [first, Backward], by simp [first, Backward], first_deterministic k,
    [(false, 1)], (fun _ => [(false, 1)]), by simp, (fun _ => by simp), ?_⟩
  intro s1 s2
  dsimp only
  intro hf h1 h2
  refine ⟨by simp [second, Backward], by simp [second, Backward],
    second_deterministic k recipient s1 s2 hf h1 h2,
    [], (fun _ => []), by simp, (fun _ => by simp), ?_⟩
  intros
  trivial

theorem legal (k : Nat) : RecipientPair (world k false) (world k true) := by
  simp [RecipientPair, Scoped, Backward, world, first, second, RecipientOnly,
    PoolGame.RecipientOnly, transferWitness, note]

theorem different_worlds (k : Nat) : world k false ≠ world k true := by
  intro h
  have ho := congrArg (fun ts => ts.map (fun t => t.body.out1.ownerPubkey)) h
  simp [world, first, second, note] at ho

def adversary (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) : Adversary (Prim k) where
  State := Unit
  chooseWorlds := pure (world k false, world k true, ())
  distinguish := fun _ => observer

noncomputable def wellFormed (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    WellFormedAdversary (fun _ => True) (setup k) (adversary k observer) 1 1 where
  initial := initial k
  setup_run := setup_run k
  leaf_bound := by simp [initial, DepositData.post, St.empty]
  worlds := by
    intro a ha
    simp only [adversary, support_pure] at ha
    subst a
    exact ⟨world_wellFormed k false, world_wellFormed k true⟩

theorem nullifier_spread (k : Nat) : NullifierSpread (P := Prim k) (k + 8) := by
  refine ⟨by omega, ?_⟩
  intro note key nf
  exact (Funded.spread k).point_bound note nf

noncomputable def assumptions (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    BoundAssumptions (adversary k observer) 2 where
  primitives := Funded.assumptions k
  hiding_nonneg := le_rfl
  length_bound := by
    intro a ha
    simp only [adversary, support_pure] at ha
    subst a
    simp [world]

theorem rejection_le (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    rejectionProbability (fun _ => True) (setup k) (adversary k observer) ≤ 14 / (k + 8 : ℝ) := by
  have h := rejectionProbability_le (k + 8) (k + 8) 1 (Funded.spread k) (nullifier_spread k)
    (fun _ => True) (setup k) (adversary k observer) 1 2 (wellFormed k observer)
    (assumptions k observer).length_bound
  norm_num [delta] at h
  convert h using 1
  ring

theorem concrete_advantage_le (k : Nat)
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim k))) Bool) :
    advantage (fun _ => True) (setup k) (adversary k observer) ≤ 7 / (k + 8 : ℝ) := by
  have h := advantage_le_delta (k + 8) (k + 8) 1 (Funded.spread k) (nullifier_spread k)
    (fun _ => True) (setup k) (adversary k observer) 1 2 (wellFormed k observer) (assumptions k observer)
  norm_num [assumptions, Funded.assumptions, delta] at h
  convert h using 1
  ring

theorem resolved_inputs_exact (k : Nat) (recipient : Bool)
    (s1 s2 s3 s4 : Fin (k + 8)) :
    (secondDraw k recipient s1 s2 s3 s4).in1 = (firstDraw k s1 s2).out1 ∧
    (secondDraw k recipient s1 s2 s3 s4).in2 = (firstDraw k s1 s2).out2 := by
  constructor <;> rfl

theorem resolved_inputs_owned (k : Nat) (recipient : Bool)
    (s1 s2 s3 s4 : Fin (k + 8)) :
    (secondDraw k recipient s1 s2 s3 s4).in1.ownedBy false ∧
    (secondDraw k recipient s1 s2 s3 s4).in2.ownedBy false := by
  constructor <;> rfl

theorem accepted_chain (k : Nat) (recipient : Bool) :
    Run (fun _ => True)
      (setup k ++ [Tx.transfer (firstDraw k 2 3), Tx.transfer (secondDraw k recipient 2 3 4 5)])
      ((secondDraw k recipient 2 3 4 5).post ((firstDraw k 2 3).post (initial k))) := by
  have hf1 : OutputFresh (firstDraw k 2 3) (initial k) := by
    norm_num [OutputFresh, firstDraw, RecipientGame.withSalts, resolve, first, initial,
      DepositData.post, deposit, note, St.empty, St.leaves, Note.cm, Prim, Funded.Prim, Fin.ext_iff]
    all_goals (simp only [Fin.ext_iff]; norm_num; simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)
  have hn1 : ¬ NullifierHit (firstDraw k 2 3).out1 [(false, 1)] := by
    norm_num [NullifierHit, firstDraw, RecipientGame.withSalts, resolve, first, Note.nf, Note.cm,
      Prim, Funded.Prim, Fin.ext_iff]
    all_goals (simp only [Fin.ext_iff]; norm_num; simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)
  have hn2 : ¬ NullifierHit (firstDraw k 2 3).out2 [(false, 1)] := by
    norm_num [NullifierHit, firstDraw, RecipientGame.withSalts, resolve, first, Note.nf, Note.cm,
      Prim, Funded.Prim, Fin.ext_iff]
    all_goals (simp only [Fin.ext_iff]; norm_num; simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)
  have hf2 : OutputFresh (secondDraw k recipient 2 3 4 5) ((firstDraw k 2 3).post (initial k)) := by
    norm_num [OutputFresh, secondDraw, firstDraw, RecipientGame.withSalts, resolve, first, second,
      initial, TransferData.post, DepositData.post, deposit, note, St.empty, St.leaves,
      Note.cm, Prim, Funded.Prim, Fin.ext_iff]
    all_goals (simp only [Fin.ext_iff]; norm_num; simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)
  have hg1 := (guard_iff _ _).mpr
    ⟨(deterministic_withSalts (P := Prim k) _ _ 2 3).mpr (first_deterministic k), hf1⟩
  have hg2 := (guard_iff _ _).mpr
    ⟨(deterministic_withSalts (P := Prim k) _ _ 4 5).mpr (second_deterministic k recipient 2 3 hf1 hn1 hn2), hf2⟩
  simpa [List.append_assoc, firstDraw, secondDraw] using
    Run.step (Run.step (setup_run k) (Step.transfer hg1)) (Step.transfer hg2)

theorem good_draw_in_support (k : Nat) (recipient : Bool) :
    [firstDraw k 2 3, secondDraw k recipient 2 3 4 5] ∈
      support (sampleWorld [] (world k recipient)) := by
  simp only [world, sampleWorld, mem_support_bind_iff, mem_support_uniformSample,
    true_and, support_pure, Set.mem_singleton_iff]
  exact ⟨2, 3, [secondDraw k recipient 2 3 4 5],
    ⟨4, 5, [], rfl, rfl⟩, rfl⟩

theorem published_chain (k : Nat) (recipient : Bool) :
    some (runObserverView (accepted_chain k recipient)) ∈
      support (publish (fun _ => True) (setup k) (world k recipient)) := by
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨_, good_draw_in_support k recipient, (RecipientGame.guardedLog_of_run (accepted_chain k recipient)).symm⟩

theorem ballast_collision_first_accepted (k : Nat) :
    (firstDraw k 1 3).guard (initial k) := by
  apply (guard_iff _ _).mpr
  refine ⟨(deterministic_withSalts (P := Prim k) _ _ 1 3).mpr (first_deterministic k), ?_⟩
  norm_num [OutputFresh, firstDraw, RecipientGame.withSalts, resolve, first, initial,
    DepositData.post, deposit, note, St.empty, St.leaves, Note.cm, Prim, Funded.Prim, Fin.ext_iff]
  all_goals (simp only [Fin.ext_iff]; norm_num; simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)

theorem ballast_collision_later_rejected (k : Nat) (recipient : Bool) :
    RecipientGame.runChecked (initial k)
      [Tx.transfer (firstDraw k 1 3), Tx.transfer (secondDraw k recipient 1 3 4 5)] = none := by
  have hb : ¬ (secondDraw k recipient 1 3 4 5).guard ((firstDraw k 1 3).post (initial k)) := by
    simp [TransferData.guard, secondDraw, firstDraw, RecipientGame.withSalts, resolve, resolveNote,
      output, first, second, TransferData.post, St.fresh, TransferData.nf1, Note.nf,
      Note.cm, TransferData.nf2, note, Prim, Funded.Prim]
  simp [RecipientGame.runChecked, RecipientGame.stepChecked, ballast_collision_first_accepted, hb]

theorem nontrivial_bound
    (observer : OracleComp (PoolGame.observerSpec (gamePrim (Prim 24))) Bool) :
    advantage (fun _ => True) (setup 24) (adversary 24 observer) ≤ 7 / 32 := by
  convert concrete_advantage_le 24 observer using 1
  norm_num

end LeanShieldedPool.ChainGame.Chain
