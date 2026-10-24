import ChainGame.CommitOnly.CollisionRejection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame.CommitOnly.FundedChain
open GameCorrespondence CommitROM CommitROM.Model RecipientGame.Rejection

abbrev Prim (k : Nat) : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool
  Salt := Fin (k+8)
  Commitment := Fin ((k+8)^4)
  Nullifier := Fin ((k+8)^4)
  derivePub := id
  commit := fun _ _ _ s => ⟨s.val,by
    have h : k+8 ≤ (k+8)^4 := Nat.le_self_pow (by decide : 4 ≠ 0) (k+8)
    exact lt_of_lt_of_le s.isLt h⟩
  nullify := fun c _ => c
abbrev H (k : Nat) := Model.Table (Prim k) 3
abbrev hp (k : Nat) := (Prim k).derivePub
abbrev hn (k : Nat) := fun x : (Prim k).SpendKey × (Prim k).Commitment => (Prim k).nullify x.2 x.1

def note (k : Nat) (a : Nat) (r : Bool) (s : Fin (k+8)) : Note (Prim k) := ⟨(),a,r,s⟩
def deposit (k : Nat) : DepositData (Prim k) := ⟨note k 2 false 0,()⟩
def setup (k : Nat) : List (Tx (Prim k)) := [.deposit (deposit k)]
def first (k : Nat) : Template (Prim k) where
  body := ⟨false,note k 2 false 0,note k 0 false 1,note k 1 false 2,note k 1 false 3,1⟩
def second (k : Nat) (r : Bool) : Template (Prim k) where
  body := ⟨false,note k 1 false 2,note k 1 false 3,note k 1 r 4,note k 1 r 5,3⟩
  input1 := some (0,false)
  input2 := some (0,true)
def world (k : Nat) (r : Bool) : World (Prim k) 3 2 :=
  ⟨[⟨first k,by simp [first,note]⟩,⟨second k r,by simp [second,note]⟩],by simp⟩

noncomputable def initial (k : Nat) (hc : H k) : St (commitPrim (Prim k) 3 hc) :=
  (⟨RecipientGame.ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k).note,()⟩ : DepositData _).post
    (St.empty _ (fun _ => True))
def firstDraw (k : Nat) (hc : H k) (s1 s2 : Fin (k+8)) : TransferData (commitPrim (Prim k) 3 hc) :=
  RecipientGame.withSalts (resolve [] (rebaseTemplate (hp k) (hn k) hc (first k))) s1 s2
def secondDraw (k : Nat) (hc : H k) (r : Bool) (s1 s2 s3 s4 : Fin (k+8)) :
    TransferData (commitPrim (Prim k) 3 hc) :=
  RecipientGame.withSalts (resolve [firstDraw k hc s1 s2] (rebaseTemplate (hp k) (hn k) hc (second k r))) s3 s4

def ballast (k : Nat) (hc : H k) := hc (((),0,false),1)
def funding (k : Nat) (hc : H k) := hc (((),2,false),0)

theorem setup_run (k : Nat) (hc : H k) :
    Run (P := commitPrim (Prim k) 3 hc) (fun _ => True)
      ((setup k).map (RecipientGame.ROMCommit.rebaseTx (hp k) (hn k) hc)) (initial k hc) := by
  apply Run.step Run.empty
  apply Step.deposit
  norm_num [DepositData.guard,setup,deposit,note,initial,RecipientGame.ROMCommit.rebaseTx,
    RecipientGame.ROMCommit.rebaseNote,St.empty,St.leaves,U128,maxU128]

theorem first_deterministic (k : Nat) (hc : H k) (h : funding k hc ≠ ballast k hc) :
    DeterministicGuard (resolve [] (rebaseTemplate (hp k) (hn k) hc (first k))) (initial k hc) := by
  norm_num [DeterministicGuard,resolve,resolveNote,rebaseTemplate,RecipientGame.ROMCommit.rebaseTransfer,
    RecipientGame.ROMCommit.rebaseNote,first,initial,DepositData.post,deposit,note,
    St.rootInWindow,St.pushWindow,rootWindow,St.empty,Note.ownedBy,Note.isBallast,St.inTreeAt,
    St.leaves,St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,U128,maxU128,
    hp,hn,Prim,oraclePrim]
  exact h

theorem second_deterministic (k : Nat) (hc : H k) (r : Bool) (s1 s2 : Fin (k+8))
    (hf : OutputFresh (firstDraw k hc s1 s2) (initial k hc))
    (h1 : ¬NullifierHit (firstDraw k hc s1 s2).out1 [(false,ballast k hc)])
    (h2 : ¬NullifierHit (firstDraw k hc s1 s2).out2 [(false,ballast k hc)]) :
    DeterministicGuard (resolve [firstDraw k hc s1 s2] (rebaseTemplate (hp k) (hn k) hc (second k r)))
      ((firstDraw k hc s1 s2).post (initial k hc)) := by
  have hh1 : hc (((),1,false),s1) ≠ ballast k hc := by
    simpa [NullifierHit,firstDraw,RecipientGame.withSalts,resolve,resolveNote,rebaseTemplate,
      RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,first,note,Note.nf,Note.cm,hp,hn,Prim,oraclePrim] using h1
  have hh2 : hc (((),1,false),s2) ≠ ballast k hc := by
    simpa [NullifierHit,firstDraw,RecipientGame.withSalts,resolve,resolveNote,rebaseTemplate,
      RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,first,note,Note.nf,Note.cm,hp,hn,Prim,oraclePrim] using h2
  have hf' : hc (((),1,false),s1) ≠ funding k hc ∧ hc (((),1,false),s2) ≠ funding k hc ∧
      hc (((),1,false),s1) ≠ hc (((),1,false),s2) := by
    simpa [OutputFresh,firstDraw,RecipientGame.withSalts,resolve,resolveNote,rebaseTemplate,
      RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,first,initial,DepositData.post,
      deposit,note,St.empty,St.leaves,Note.cm,hp,hn,Prim,oraclePrim,funding] using hf
  norm_num [DeterministicGuard,resolve,resolveNote,output,rebaseTemplate,RecipientGame.ROMCommit.rebaseTransfer,
    RecipientGame.ROMCommit.rebaseNote,second,firstDraw,RecipientGame.withSalts,first,initial,TransferData.post,
    DepositData.post,deposit,note,St.rootInWindow,St.pushWindow,rootWindow,St.empty,Note.ownedBy,
    Note.isBallast,St.inTreeAt,St.leaves,St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,
    U128,maxU128,hp,hn,Prim,oraclePrim]
  change (hc (((),1,false),s1) ≠ funding k hc ∧ hc (((),1,false),s1) ≠ ballast k hc) ∧
    (hc (((),1,false),s2) ≠ funding k hc ∧ hc (((),1,false),s2) ≠ ballast k hc) ∧
    hc (((),1,false),s1) ≠ hc (((),1,false),s2)
  exact ⟨⟨hf'.1,hh1⟩,⟨hf'.2.1,hh2⟩,hf'.2.2⟩

theorem world_wellFormed (k : Nat) (hc : H k) (r : Bool) (h : funding k hc ≠ ballast k hc) :
    ChainGame.WellFormed 1 (initial k hc) [] (worldBack (hp k) (hn k) hc (world k r).val) := by
  refine ⟨by simp [rebaseTemplate,first,Backward],by simp [rebaseTemplate,first,Backward],
    first_deterministic k hc h,[(false,ballast k hc)],(fun _ => [(false,ballast k hc)]),
    by simp,(fun _ => by simp),?_⟩
  intro s1 s2
  dsimp only
  intro hf h1 h2
  refine ⟨by simp [rebaseTemplate,second,Backward],by simp [rebaseTemplate,second,Backward],
    second_deterministic k hc r s1 s2 hf h1 h2,[],(fun _ => []),by simp,(fun _ => by simp),?_⟩
  intros
  trivial

def guess (k : Nat) (log : List (PoolGame.Event (gamePrim (Prim k)))) : OracleComp (Spec (Prim k) 3) Bool := do
  let c ← RecipientGame.ROMCommit.cmNote (cap := 3) (note k 1 false 4)
  match log with
  | [_,_,.transfer _ _ out _] => pure (decide (c ≠ out))
  | _ => pure false
abbrev adversary (k : Nat) : Adversary (Prim k) 3 2 where
  State := Unit
  choose := pure (world k false,world k true,())
  guess := fun _ => guess k

theorem query_bound (k : Nat) : QueryBound (adversary k) 0 1 := by
  constructor
  · simp [adversary]
  · intro s log
    apply (isQueryBoundP_bind (n := 1) (m := 0) (RecipientGame.ROMCommit.cmNote_bound _) ?_).mono (by omega)
    intro c _
    split <;> simp

theorem table_valid (k : Nat) (hc : H k) (hi : Function.Injective hc) :
    TableValid (fun _ => True) (setup k) (adversary k) 1 1 hc := by
  have h : funding k hc ≠ ballast k hc := by
    intro he
    have hh := hi he
    have hh' := congrArg (fun x : Message (Prim k) 3 × (Prim k).Salt => x.1.2.1.val) hh
    norm_num at hh'
  refine ⟨initial k hc,setup_run k hc,by simp [initial,DepositData.post,St.empty],?_⟩
  intro x hx
  simp only [adversary,run,simulateQ_pure,support_pure,Set.mem_singleton_iff] at hx
  subst x
  exact ⟨world_wellFormed k hc false h,world_wellFormed k hc true h⟩

theorem validity_zero (k : Nat) :
    validityFailureProbability (fun _ => True) (setup k) (adversary k) 1 1 = 0 := by
  unfold validityFailureProbability
  have he (hc : H k) : ¬ (Function.Injective hc ∧ ¬TableValid (fun _ => True) (setup k) (adversary k) 1 1 hc) :=
    fun h => h.2 (table_valid k hc h.1)
  simp [he]

theorem outside_injective (k : Nat) :
    ∀ token amount owner, 3 ≤ amount → Function.Injective ((Prim k).commit token amount owner) := by
  intro token amount owner _ a b h
  exact Fin.ext (congrArg (fun c : Fin ((k+8)^4) => c.val) h)

theorem nullify_injective (k : Nat) : ∀ key, Function.Injective (fun c => (Prim k).nullify c key) := by
  intro key a b h
  exact h

theorem rejection_bound (k : Nat) :
    rejectionProbability (fun _ => True) (setup k) (adversary k) ≤
      (6*(k+8) : ℝ)*(6*(k+8)-1)/(2*(k+8)^4) + 14/(k+8) := by
  have h := rejection_le_rom_collisions (fun _ => True) (setup k) (adversary k) 1 1
    (outside_injective k) (nullify_injective k)
  rw [validity_zero,zero_add] at h
  apply h.trans_eq
  simp [Message,Prim,Fintype.card_prod,Fintype.card_fin,ChainGame.delta]
  ring

theorem privacy_bound (k : Nat) :
    advantage (fun _ => True) (setup k) (adversary k) ≤
      75/(k+8 : ℝ) + (6*(k+8) : ℝ)*(6*(k+8)-1)/(4*(k+8)^4) := by
  have h := advantage_le_queryBound (fun _ => True) (setup k) (adversary k) 0 1 (query_bound k)
  have hr := rejection_bound k
  have hh := h.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 2)))
  simp only [setup,List.length_singleton,Prim,Fintype.card_fin] at hh
  apply hh.trans_eq
  push_cast
  field_simp
  ring

theorem resolved_inputs_exact (k : Nat) (hc : H k) (r : Bool) (s1 s2 s3 s4 : Fin (k+8)) :
    (secondDraw k hc r s1 s2 s3 s4).in1 = (firstDraw k hc s1 s2).out1 ∧
    (secondDraw k hc r s1 s2 s3 s4).in2 = (firstDraw k hc s1 s2).out2 := by
  constructor <;> rfl

theorem legal (k : Nat) (hc : H k) :
    RecipientPair (worldBack (hp k) (hn k) hc (world k false).val)
      (worldBack (hp k) (hn k) hc (world k true).val) := by
  simp [RecipientPair,Scoped,Backward,worldBack,world,rebaseTemplate,first,second,RecipientOnly,
    PoolGame.RecipientOnly,transferWitness,RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,note]

theorem small_bounds :
    rejectionProbability (fun _ => True) (setup 65528) (adversary 65528) < 1/1000 ∧
    advantage (fun _ => True) (setup 65528) (adversary 65528) < 1/800 := by
  constructor
  · exact (rejection_bound 65528).trans_lt (by norm_num)
  · exact (privacy_bound 65528).trans_lt (by norm_num)

end LeanShieldedPool.ChainGame.CommitOnly.FundedChain
