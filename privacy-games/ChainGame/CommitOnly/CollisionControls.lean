import ChainGame.CommitOnly.FundedChain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame.CommitOnly.CollisionControl
open GameCorrespondence CommitROM CommitROM.Model
abbrev Prim := FundedChain.Prim
abbrev H := FundedChain.H
abbrev hp := FundedChain.hp
abbrev hn := FundedChain.hn
abbrev note := FundedChain.note

def deposit (k : Nat) (s : Fin (k+8)) : DepositData (Prim k) := ⟨note k 1 false s,()⟩
def setup (k : Nat) : List (Tx (Prim k)) := [.deposit (deposit k 0),.deposit (deposit k 1)]
def coord (k : Nat) (s : Fin (k+8)) : Message (Prim k) 3 × (Prim k).Salt := (((),1,false),s)
def emptyWorld (k : Nat) : World (Prim k) 3 0 := ⟨[],by simp⟩
abbrev adversary (k : Nat) : Adversary (Prim k) 3 0 where
  State := Unit
  choose := pure (emptyWorld k,emptyWorld k,())
  guess := fun _ _ => pure false

noncomputable def initial (k : Nat) (hc : H k) : St (commitPrim (Prim k) 3 hc) :=
  (⟨RecipientGame.ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 1).note,()⟩ : DepositData _).post
    ((⟨RecipientGame.ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 0).note,()⟩ : DepositData _).post
      (St.empty _ (fun _ => True)))

theorem setup_run (k : Nat) (hc : H k) (h : hc (coord k 0) ≠ hc (coord k 1)) :
    Run (P := commitPrim (Prim k) 3 hc) (fun _ => True)
      ((setup k).map (RecipientGame.ROMCommit.rebaseTx (hp k) (hn k) hc)) (initial k hc) := by
  let d0 : DepositData (commitPrim (Prim k) 3 hc) := ⟨RecipientGame.ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 0).note,()⟩
  let d1 : DepositData (commitPrim (Prim k) 3 hc) := ⟨RecipientGame.ROMCommit.rebaseNote (hp k) (hn k) hc (deposit k 1).note,()⟩
  have h0 : d0.guard (St.empty _ (fun _ => True)) := by
    norm_num [d0,DepositData.guard,deposit,note,FundedChain.note,RecipientGame.ROMCommit.rebaseNote,
      St.empty,St.leaves,U128,maxU128]
  have h1 : d1.guard (d0.post (St.empty _ (fun _ => True))) := by
    norm_num [d0,d1,DepositData.guard,DepositData.post,deposit,note,FundedChain.note,
      RecipientGame.ROMCommit.rebaseNote,St.empty,St.leaves,Note.cm,U128,maxU128,oraclePrim,
      hp,hn,Prim,FundedChain.Prim,FundedChain.hp,FundedChain.hn]
    exact h.symm
  exact Run.step (Run.step Run.empty (Step.deposit h0)) (Step.deposit h1)

theorem table_valid (k : Nat) (hc : H k) (hi : Function.Injective hc) :
    TableValid (fun _ => True) (setup k) (adversary k) 2 0 hc := by
  have h : hc (coord k 0) ≠ hc (coord k 1) := by
    intro he
    have hh := congrArg (fun x : Message (Prim k) 3 × (Prim k).Salt => x.2.val) (hi he)
    norm_num [coord] at hh
  refine ⟨initial k hc,setup_run k hc h,by simp [initial,DepositData.post,St.empty],?_⟩
  intro x hx
  simp only [adversary,run,simulateQ_pure,support_pure,Set.mem_singleton_iff] at hx
  subst x
  exact ⟨True.intro,True.intro⟩

theorem validity_zero (k : Nat) :
    validityFailureProbability (fun _ => True) (setup k) (adversary k) 2 0 = 0 := by
  unfold validityFailureProbability
  have he (hc : H k) : ¬ (Function.Injective hc ∧ ¬TableValid (fun _ => True) (setup k) (adversary k) 2 0 hc) :=
    fun h => h.2 (table_valid k hc h.1)
  simp [he]

theorem setup_rejected_iff (k : Nat) (hc : H k) :
    (RecipientGame.runChecked (St.empty (commitPrim (Prim k) 3 hc) (fun _ => True))
      ((setup k).map (RecipientGame.ROMCommit.rebaseTx (hp k) (hn k) hc))).isNone = true ↔
      hc (coord k 0) = hc (coord k 1) := by
  classical
  simp [RecipientGame.runChecked,RecipientGame.stepChecked,setup,deposit,note,FundedChain.note,
    RecipientGame.ROMCommit.rebaseTx,RecipientGame.ROMCommit.rebaseNote,DepositData.guard,DepositData.post,
    St.empty,St.leaves,Note.cm,oraclePrim,U128,maxU128,hp,hn,Prim,FundedChain.Prim,
    FundedChain.hp,FundedChain.hn,coord]

theorem rejection_exact (k : Nat) :
    rejectionProbability (fun _ => True) (setup k) (adversary k) = 1/((k+8 : ℝ)^4) := by
  classical
  have he : Pr[= true | do
      let hc ← $ᵗ (H k)
      let d ← atDraws (setup k) (adversary k) (hp k) (hn k) hc
      pure (rejected (fun _ => True) (adversary k) (hp k) (hn k) hc d)] =
      Pr[fun hc : H k => hc (coord k 0) = hc (coord k 1) | $ᵗ (H k)] := by
    simp only [atDraws,adversary,run,simulateQ_pure,pure_bind,bind_assoc,
      emptyWorld,worldBack,List.map_nil,RecipientPair,Scoped,List.forall₂_nil_left_iff,true_and,ite_self,
      if_true,ChainGame.sampleWorld,List.append_nil,rejected]
    rw [probOutput_bind_eq_tsum,probEvent_eq_tsum_ite]
    apply tsum_congr
    intro hc
    rw [probOutput_bind_const,probFailure_eq_zero,tsub_zero,one_mul]
    have hh := setup_rejected_iff k hc
    by_cases h : hc (coord k 0) = hc (coord k 1)
    · have hb := hh.mpr h
      simp only [h,hb,probOutput_pure,ite_true,ite_false,Bool.true_eq_false,mul_one,mul_zero]
    · have hb : (RecipientGame.runChecked (St.empty (commitPrim (Prim k) 3 hc) (fun _ => True))
        ((setup k).map (RecipientGame.ROMCommit.rebaseTx (hp k) (hn k) hc))).isNone = false :=
        Bool.eq_false_iff.mpr (fun he => h (hh.mp he))
      simp only [h,hb,probOutput_pure,ite_true,ite_false,Bool.true_eq_false,mul_one,mul_zero]
  unfold rejectionProbability
  change (Pr[= true | do
    let hc ← $ᵗ H k
    let d ← atDraws (setup k) (adversary k) (hp k) (hn k) hc
    pure (rejected (fun _ => True) (adversary k) (hp k) (hn k) hc d)]).toReal = _
  rw [he,WithdrawGame.ROM.keymap_pair_collision (coord k 0) (coord k 1) (by
    intro hh; have hv := congrArg (fun x : Message (Prim k) 3 × (Prim k).Salt => x.2.val) hh
    norm_num [coord] at hv)]
  simp only [Prim,FundedChain.Prim,Fintype.card_fin,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,one_div]
  norm_num [ENNReal.toReal_add,ENNReal.toReal_pow]

theorem dropping_table_collision_false (k : Nat) :
    ¬ rejectionProbability (fun _ => True) (setup k) (adversary k) ≤
      validityFailureProbability (fun _ => True) (setup k) (adversary k) 2 0 +
      ChainGame.delta 2 0 0 (k+8) (k+8) := by
  rw [rejection_exact,validity_zero]
  simp only [ChainGame.delta,Nat.mul_zero,Nat.zero_mul,Nat.cast_zero,zero_div,add_zero]
  exact not_le.mpr (by positivity)

theorem invalid_setup_rejection (k : Nat) :
    rejectionProbability (fun _ => False) (setup k) (adversary k) = 1 := by
  unfold rejectionProbability
  simp [atDraws,adversary,run,simulateQ_pure,emptyWorld,worldBack,RecipientPair,Scoped,
    ChainGame.sampleWorld,rejected,RecipientGame.runChecked,RecipientGame.stepChecked,setup,deposit,DepositData.guard,
    RecipientGame.ROMCommit.rebaseTx,St.empty,probOutput_bind_const]

theorem dropping_validity_false :
    ¬ rejectionProbability (fun _ => False) (setup 65528) (adversary 65528) ≤
      (6*(65528+8) : ℝ)*(6*(65528+8)-1)/(2*(65528+8)^4) +
      ChainGame.delta 2 0 0 (65528+8) (65528+8) := by
  rw [invalid_setup_rejection]
  norm_num [ChainGame.delta]

end LeanShieldedPool.ChainGame.CommitOnly.CollisionControl
