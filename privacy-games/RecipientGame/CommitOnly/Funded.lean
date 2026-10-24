import RecipientGame.CommitOnly.Validity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.CommitOnly.Funded
open GameCorrespondence CommitROM CommitROM.Model ROMCommit

abbrev Prim (k : Nat) := Rejection.Funded.Prim k
abbrev H (k : Nat) := Model.Table (Prim k) 3

def note (k : Nat) (amount : Nat) (owner : Bool) (s : Fin 8) : Note (Prim k) :=
  ⟨(),amount,owner,⟨s.val,by have := s.isLt; omega⟩⟩

def deposit (k : Nat) : DepositData (Prim k) := ⟨note k 2 false 0,()⟩
def setup (k : Nat) : List (Tx (Prim k)) := [.deposit (deposit k)]

def transfer (k : Nat) (recipient : Bool) : TransferData (Prim k) :=
  ⟨false,note k 2 false 0,note k 0 false 1,note k 1 recipient 2,note k 1 recipient 3,1⟩

def world (k : Nat) (recipient : Bool) : World (Prim k) 3 1 :=
  ⟨[⟨transfer k recipient,by simp [transfer,note]⟩],by simp⟩
def emptyWorld (k : Nat) : World (Prim k) 3 1 := ⟨[],by simp⟩

abbrev hp (k : Nat) := (Prim k).derivePub
abbrev hn (k : Nat) := fun x : (Prim k).SpendKey × (Prim k).Commitment => (Prim k).nullify x.2 x.1
noncomputable def initial (k : Nat) (hc : H k) : St (commitPrim (Prim k) 3 hc) :=
  (⟨ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k).note,()⟩ : DepositData _).post
    (St.empty _ (fun _ => True))

def fundedCm (k : Nat) (hc : H k) : (Prim k).Commitment :=
  hc (((),⟨2,by omega⟩,false),⟨0,by omega⟩)
def ballastCm (k : Nat) (hc : H k) : (Prim k).Commitment :=
  hc (((),⟨0,by omega⟩,false),⟨1,by omega⟩)

theorem setup_run (k : Nat) (hc : H k) :
    Run (P := commitPrim (Prim k) 3 hc) (fun _ => True)
      ((setup k).map (ROMCommit.rebaseTx (hp k) (hn k) hc)) (initial k hc) := by
  apply Run.step Run.empty
  apply Step.deposit
  norm_num [DepositData.guard, setup, deposit, note, initial, ROMCommit.rebaseTx,
    ROMCommit.rebaseNote, St.empty, St.leaves, U128, maxU128]

theorem deterministic_guard (k : Nat) (hc : H k) (recipient : Bool)
    (h : fundedCm k hc ≠ ballastCm k hc) :
    Rejection.DeterministicGuard (ROMCommit.rebaseTransfer (hp k) (hn k) hc (transfer k recipient))
      (initial k hc) := by
  norm_num [Rejection.DeterministicGuard, ROMCommit.rebaseTransfer, ROMCommit.rebaseNote,
    transfer, initial, deposit, note, DepositData.post, St.rootInWindow, St.pushWindow,
    rootWindow, St.empty, Note.ownedBy, Note.isBallast, St.inTreeAt, St.leaves,
    St.fresh, TransferData.nf1, TransferData.nf2, Note.nf, Note.cm, U128, maxU128,
    hp, hn, Prim, Rejection.Funded.Prim, oraclePrim] at *
  exact h

theorem valid_funded (k : Nat) (hc : H k) (h : fundedCm k hc ≠ ballastCm k hc) :
    Valid (fun _ => True) (setup k) (hp k) (hn k) hc (world k false) (world k true) := by
  refine ⟨initial k hc,setup_run k hc,?_,?_⟩
  all_goals
    exact ⟨deterministic_guard k hc _ h,fun _ _ => trivial⟩

theorem valid_empty (k : Nat) (hc : H k) :
    Valid (fun _ => True) (setup k) (hp k) (hn k) hc (emptyWorld k) (emptyWorld k) :=
  ⟨initial k hc,setup_run k hc,True.intro,True.intro⟩

abbrev adversary (k : Nat) : ROMCommit.Adversary (Prim k) 3 1 where
  State := Unit
  choose := do
    let c ← ROMCommit.cmNote (cap := 3) (note k 2 false 0)
    let d ← ROMCommit.cmNote (cap := 3) (note k 0 false 1)
    if c = d then pure (emptyWorld k,emptyWorld k,())
    else pure (world k false,world k true,())
  guess := fun _ _ => pure false

theorem run_choose (k : Nat) (hc : H k) :
    run (WithdrawGame.ROM.answers (hp k) (hn k)) hc (adversary k).choose =
      pure (if fundedCm k hc = ballastCm k hc then (emptyWorld k,emptyWorld k,())
        else (world k false,world k true,())) := by
  simp only [adversary, run, simulateQ_bind]
  have h₁ := ROMCommit.run_cmNote (cap := 3) (hp k) (hn k) hc (note k 2 false 0)
  have h₂ := ROMCommit.run_cmNote (cap := 3) (hp k) (hn k) hc (note k 0 false 1)
  unfold run at h₁ h₂
  rw [h₁, pure_bind,h₂,pure_bind]
  simp [note,Note.cm,ROMCommit.rebaseNote,oraclePrim,fundedCm,ballastCm]
  split <;> simp_all

theorem query_bound (k : Nat) : QueryBound (adversary k) 2 0 := by
  constructor
  · apply isQueryBoundP_bind (n := 1) (m := 1) (cmNote_bound _)
    intro c _
    apply (isQueryBoundP_bind (n := 1) (m := 0) (cmNote_bound _) ?_).mono (by omega)
    intro d _
    split <;> trivial
  · intros; simp [adversary]

theorem supported_validity (k : Nat) :
    SupportedValidity (fun _ => True) (setup k) (adversary k) := by
  intro hc x hx
  rw [run_choose] at hx
  by_cases h : fundedCm k hc = ballastCm k hc
  · simp only [h,if_true,support_pure,Set.mem_singleton_iff] at hx
    subst x
    exact valid_empty k hc
  · simp only [h,if_false,support_pure,Set.mem_singleton_iff] at hx
    subst x
    exact valid_funded k hc h

theorem validity_zero (k : Nat) :
    validityFailureProbability (fun _ => True) (setup k) (adversary k) = 0 :=
  validityFailure_eq_zero _ _ _ (supported_validity k)

theorem privacy_bound (k : Nat) :
    advantage (fun _ => True) (setup k) (adversary k) ≤ 40 / (k+8 : ℝ) := by
  have h := advantage_le_of_supportedValidity _ _ _ 2 0 (query_bound k) (supported_validity k)
  simp only [setup,List.length_singleton,Prim,Rejection.Funded.Prim,Fintype.card_fin] at h
  convert h using 1 <;> norm_num
  all_goals first | rfl | ring

theorem fallback_probability (k : Nat) :
    Pr[fun hc : H k => fundedCm k hc = ballastCm k hc | $ᵗ (H k)] =
      (k+8 : ℝ≥0∞)⁻¹ := by
  simpa only [fundedCm,ballastCm,Prim,Rejection.Funded.Prim,Fintype.card_fin,Nat.cast_add,
    Nat.cast_ofNat] using
    WithdrawGame.ROM.keymap_pair_collision (K := (Prim k).Commitment)
      ((((),⟨2,by omega⟩,false),⟨0,by omega⟩) : Message (Prim k) 3 × (Prim k).Salt)
      (((),⟨0,by omega⟩,false),⟨1,by omega⟩)
      (by intro h; have hh := congrArg (fun x : Message (Prim k) 3 × (Prim k).Salt => x.1.2.1.val) h; norm_num at hh)

theorem legal (k : Nat) (hc : H k) :
    RecipientPair (worldBack (hp k) (hn k) hc (world k false).val)
      (worldBack (hp k) (hn k) hc (world k true).val) := by
  simp [RecipientPair,projectWorld,PoolGame.LegalChallenge,PoolGame.RecipientOnly,
    transferWitness,worldBack,world,ROMCommit.rebaseTransfer,ROMCommit.rebaseNote,transfer,note]

theorem moves_value (k : Nat) (recipient : Bool) :
    (transfer k recipient).in1.amount = 2 ∧ (transfer k recipient).out1.amount = 1 ∧
      (transfer k recipient).out2.amount = 1 ∧ (transfer k recipient).snapshot = 1 := by
  trivial

def passingTable (k : Nat) : H k := fun x => x.2

theorem funded_guard (k : Nat) (recipient : Bool) :
    (ROMCommit.rebaseTransfer (hp k) (hn k) (passingTable k) (transfer k recipient)).guard
      (initial k (passingTable k)) := by
  norm_num [TransferData.guard,ROMCommit.rebaseTransfer,ROMCommit.rebaseNote,transfer,
    initial,deposit,note,DepositData.post,St.rootInWindow,St.pushWindow,rootWindow,
    St.empty,Note.ownedBy,Note.isBallast,St.inTreeAt,St.leaves,St.fresh,TransferData.nf1,
    TransferData.nf2,Note.nf,Note.cm,U128,maxU128,hp,hn,Prim,Rejection.Funded.Prim,
    oraclePrim,passingTable,Fin.ext_iff]
  simp only [Fin.ext_iff]
  norm_num

theorem funded_run (k : Nat) (recipient : Bool) :
    Run (P := commitPrim (Prim k) 3 (passingTable k)) (fun _ => True)
      (((setup k).map (ROMCommit.rebaseTx (hp k) (hn k) (passingTable k))) ++
        [Tx.transfer (ROMCommit.rebaseTransfer (hp k) (hn k) (passingTable k) (transfer k recipient))])
      ((ROMCommit.rebaseTransfer (hp k) (hn k) (passingTable k) (transfer k recipient)).post
        (initial k (passingTable k))) :=
  Run.step (setup_run k (passingTable k)) (Step.transfer (funded_guard k recipient))

theorem rejection_bound (k : Nat) :
    rejectionProbability (fun _ => True) (setup k) (adversary k) ≤ 32/(k+8 : ℝ) := by
  have hr := rejection_le_validity_add_collision (fun _ => True) (setup k) (adversary k)
  rw [validity_zero,zero_add] at hr
  have hc := collisionProbability_le (setup k) (adversary k) 2 0 (query_bound k)
  have hh := hr.trans hc
  simp only [setup,List.length_singleton,Prim,Rejection.Funded.Prim,Fintype.card_fin] at hh
  convert hh using 1 <;> norm_num
  all_goals first | rfl | ring

theorem small_terms :
    (24 : ℝ)/65536 < 1/1000 ∧ (8 : ℝ)/65536 < 1/1000 ∧
    (40 : ℝ)/65536 < 1/1000 ∧
    advantage (fun _ => True) (setup 65528) (adversary 65528) < 1/1000 ∧
    rejectionProbability (fun _ => True) (setup 65528) (adversary 65528) < 1/1000 := by
  have h := privacy_bound 65528
  have hr := rejection_bound 65528
  norm_num at h hr ⊢
  constructor <;> linarith

end LeanShieldedPool.RecipientGame.CommitOnly.Funded
