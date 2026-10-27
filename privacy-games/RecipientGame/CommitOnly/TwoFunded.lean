import RecipientGame.CommitOnly.CollisionValidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.CommitOnly.TwoFunded
open GameCorrespondence CommitROM CommitROM.Model ROMCommit
abbrev Prim (k : Nat) := Rejection.Funded.Prim k
abbrev H (k : Nat) := Model.Table (Prim k) 2
abbrev hp (k : Nat) := (Prim k).derivePub
abbrev hn (k : Nat) := fun x : (Prim k).SpendKey × (Prim k).Commitment => (Prim k).nullify x.2 x.1
abbrev note := Rejection.Funded.note
abbrev deposit := Rejection.Funded.deposit
abbrev setup := Rejection.Funded.setup
abbrev transfer := Rejection.Funded.transfer

def coord (k : Nat) (s : Fin 8) : Message (Prim k) 2 × (Prim k).Salt :=
  (((),1,false),⟨s.val,by have := s.isLt; omega⟩)
def inputs (k : Nat) := [coord k 0,coord k 1]

theorem inputs_nodup (k : Nat) : (inputs k).Nodup := by
  simp [inputs,coord,Fin.ext_iff]

noncomputable def initial (k : Nat) (hc : H k) : St (commitPrim (Prim k) 2 hc) :=
  (⟨ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 1).note,()⟩ : DepositData _).post
    ((⟨ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 0).note,()⟩ : DepositData _).post
      (St.empty _ (fun _ => True)))

def world (k : Nat) (r : Bool) : World (Prim k) 2 1 :=
  ⟨[⟨transfer k r,by simp [transfer,Rejection.Funded.transfer,note,Rejection.Funded.note]⟩],by simp⟩

def guess (k : Nat) (log : List (PoolGame.Event (gamePrim (Prim k)))) : OracleComp (Spec (Prim k) 2) Bool := do
  let c ← cmNote (cap := 2) (note k false 2)
  match log with
  | [_,_,.transfer _ _ out _] => pure (decide (c ≠ out))
  | _ => pure false

abbrev adversary (k : Nat) : ROMCommit.Adversary (Prim k) 2 1 where
  State := Unit
  choose := pure (world k false,world k true,())
  guess := fun _ => guess k

theorem query_bound (k : Nat) : QueryBound (adversary k) 0 1 := by
  constructor
  · simp [adversary]
  · intro s log
    apply (isQueryBoundP_bind (n := 1) (m := 0) (cmNote_bound _) ?_).mono (by omega)
    intro c _
    split <;> simp

theorem setup_run (k : Nat) (hc : H k) (h : hc (coord k 0) ≠ hc (coord k 1)) :
    Run (P := commitPrim (Prim k) 2 hc) (fun _ => True)
      ((setup k).map (rebaseTx (hp k) (hn k) hc)) (initial k hc) := by
  let d0 : DepositData (commitPrim (Prim k) 2 hc) := ⟨ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 0).note,()⟩
  let d1 : DepositData (commitPrim (Prim k) 2 hc) := ⟨ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 1).note,()⟩
  have h0 : d0.guard (St.empty _ (fun _ => True)) := by
    norm_num [d0,d1,DepositData.guard,setup,deposit,Rejection.Funded.setup,Rejection.Funded.deposit,
      note,Rejection.Funded.note,initial,rebaseTx,ROMCommit.rebaseNote,St.empty,St.leaves,U128,maxU128]
  have h1 : d1.guard (d0.post (St.empty _ (fun _ => True))) := by
    norm_num [d0,d1,DepositData.guard,DepositData.post,setup,deposit,Rejection.Funded.setup,
      Rejection.Funded.deposit,note,Rejection.Funded.note,initial,rebaseTx,ROMCommit.rebaseNote,
      St.empty,St.leaves,Note.cm,U128,maxU128,oraclePrim,hp,hn,Prim,Rejection.Funded.Prim]
    exact h.symm
  exact Run.step (Run.step Run.empty (Step.deposit h0)) (Step.deposit h1)

theorem deterministic_guard (k : Nat) (hc : H k) (r : Bool)
    (h : hc (coord k 0) ≠ hc (coord k 1)) :
    Rejection.DeterministicGuard (rebaseTransfer (hp k) (hn k) hc (transfer k r)) (initial k hc) := by
  norm_num [Rejection.DeterministicGuard,rebaseTransfer,ROMCommit.rebaseNote,transfer,Rejection.Funded.transfer,
    initial,deposit,Rejection.Funded.deposit,note,Rejection.Funded.note,DepositData.post,
    St.rootInWindow,St.pushWindow,rootWindow,St.empty,Note.ownedBy,Note.isBallast,St.inTreeAt,
    St.leaves,St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,U128,maxU128,
    hp,hn,Prim,Rejection.Funded.Prim,oraclePrim]
  exact h

theorem valid_on (k : Nat) : ValidOn (inputs k) (fun _ => True) (setup k) (adversary k) := by
  intro hc hg x hx
  simp only [adversary,run,simulateQ_pure,support_pure,Set.mem_singleton_iff] at hx
  subst x
  have h : hc (coord k 0) ≠ hc (coord k 1) := by simpa [inputs] using hg
  refine ⟨initial k hc,setup_run k hc h,?_,?_⟩
  all_goals exact ⟨deterministic_guard k hc _ h,fun _ _ => trivial⟩


noncomputable def old_wellFormed (k : Nat) (hc : H k) (hg : ((inputs k).map hc).Nodup) :
    Rejection.WellFormedAdversary (P := commitPrim (Prim k) 2 hc) (fun _ => True)
      ((setup k).map (rebaseTx (hp k) (hn k) hc)) (legacyAt (adversary k) hc) 2 where
  initial := initial k hc
  setup_run := setup_run k hc (by simpa [inputs] using hg)
  leaf_bound := by simp [initial,DepositData.post,St.empty]
  worlds := by
    intro x hx
    simp only [legacyAt,adversary,run,simulateQ_pure,pure_bind,support_pure,Set.mem_singleton_iff] at hx
    subst x
    have h : hc (coord k 0) ≠ hc (coord k 1) := by simpa [inputs] using hg
    exact ⟨⟨deterministic_guard k hc false h,fun _ _ => trivial⟩,
      ⟨deterministic_guard k hc true h,fun _ _ => trivial⟩⟩

theorem validity_bound (k : Nat) :
    validityFailureProbability (fun _ => True) (setup k) (adversary k) ≤ 1/(k+8 : ℝ) := by
  have h := validityFailure_le_birthday (inputs k) (inputs_nodup k) _ _ _ (valid_on k)
  simp only [inputs,List.length_cons,List.length_nil,Prim,Rejection.Funded.Prim,Fintype.card_fin] at h
  apply h.trans_eq
  norm_num
  field_simp

theorem privacy_bound (k : Nat) :
    advantage (fun _ => True) (setup k) (adversary k) ≤ (101 : ℝ)/(2*(k+8)) := by
  have h := advantage_le_birthday (inputs k) (inputs_nodup k) _ _ _ 0 1 (query_bound k) (valid_on k)
  simp only [inputs,List.length_cons,List.length_nil,setup,Rejection.Funded.setup,
    Prim,Rejection.Funded.Prim,Fintype.card_fin] at h
  apply h.trans_eq
  push_cast
  field_simp
  ring

theorem rejection_bound (k : Nat) :
    rejectionProbability (fun _ => True) (setup k) (adversary k) ≤ 41/(k+8 : ℝ) := by
  have h := rejection_le_validity_add_collision (fun _ => True) (setup k) (adversary k)
  have hv := validity_bound k
  have hc := collisionProbability_le (setup k) (adversary k) 0 1 (query_bound k)
  simp only [setup,Rejection.Funded.setup,List.length_cons,List.length_nil,Prim,
    Rejection.Funded.Prim,Fintype.card_fin] at hc
  norm_num at hc
  have he : (28 : ℝ)/(k+8)+12/(k+8) = 40/(k+8) := by ring
  rw [he] at hc
  calc
    _ ≤ 1/(k+8 : ℝ) + 40/(k+8 : ℝ) := h.trans (add_le_add hv hc)
    _ = _ := by ring

theorem legal (k : Nat) (hc : H k) :
    RecipientPair (worldBack (hp k) (hn k) hc (world k false).val)
      (worldBack (hp k) (hn k) hc (world k true).val) := by
  simp [RecipientPair,projectWorld,PoolGame.LegalChallenge,PoolGame.RecipientOnly,
    transferWitness,worldBack,world,rebaseTransfer,ROMCommit.rebaseNote,transfer,Rejection.Funded.transfer,
    note,Rejection.Funded.note]

theorem moves_value (k : Nat) (r : Bool) :
    (setup k).length = 2 ∧ (transfer k r).in1.amount = 1 ∧ (transfer k r).in2.amount = 1 ∧
      (transfer k r).out1.amount = 1 ∧ (transfer k r).out2.amount = 1 ∧ (transfer k r).snapshot = 2 := by
  trivial

end LeanShieldedPool.RecipientGame.CommitOnly.TwoFunded
