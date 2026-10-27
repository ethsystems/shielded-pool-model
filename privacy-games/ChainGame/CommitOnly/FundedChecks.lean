import ChainGame.CommitOnly.FundedChain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame.CommitOnly.FundedChain
open GameCorrespondence CommitROM CommitROM.Model RecipientGame.Rejection

def passingTable (k : Nat) : H k := fun x => (Prim k).commit () 0 false x.2

theorem first_guard (k : Nat) :
    (firstDraw k (passingTable k) 2 3).guard (initial k (passingTable k)) := by
  norm_num [TransferData.guard,firstDraw,RecipientGame.withSalts,resolve,resolveNote,rebaseTemplate,
    RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,first,initial,DepositData.post,
    deposit,note,St.rootInWindow,St.pushWindow,rootWindow,St.empty,Note.ownedBy,Note.isBallast,
    St.inTreeAt,St.leaves,St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,U128,maxU128,
    hp,hn,Prim,oraclePrim,passingTable,Fin.ext_iff]
  all_goals (simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)

theorem second_guard (k : Nat) (r : Bool) :
    (secondDraw k (passingTable k) r 2 3 4 5).guard
      ((firstDraw k (passingTable k) 2 3).post (initial k (passingTable k))) := by
  norm_num [TransferData.guard,secondDraw,firstDraw,RecipientGame.withSalts,resolve,resolveNote,output,rebaseTemplate,
    RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,first,second,initial,DepositData.post,TransferData.post,
    deposit,note,St.rootInWindow,St.pushWindow,rootWindow,St.empty,Note.ownedBy,Note.isBallast,
    St.inTreeAt,St.leaves,St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,U128,maxU128,
    hp,hn,Prim,oraclePrim,passingTable,Fin.ext_iff]
  all_goals (simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)

theorem accepted_chain (k : Nat) (r : Bool) :
    Run (P := commitPrim (Prim k) 3 (passingTable k)) (fun _ => True)
      (((setup k).map (RecipientGame.ROMCommit.rebaseTx (hp k) (hn k) (passingTable k))) ++
        [Tx.transfer (firstDraw k (passingTable k) 2 3),
          Tx.transfer (secondDraw k (passingTable k) r 2 3 4 5)])
      ((secondDraw k (passingTable k) r 2 3 4 5).post
        ((firstDraw k (passingTable k) 2 3).post (initial k (passingTable k)))) := by
  simpa [List.append_assoc] using
    Run.step (Run.step (setup_run k (passingTable k)) (Step.transfer (first_guard k)))
      (Step.transfer (second_guard k r))

theorem sampled_chain_support (k : Nat) (hc : H k) (r : Bool) (s1 s2 s3 s4 : Fin (k+8)) :
    [firstDraw k hc s1 s2,secondDraw k hc r s1 s2 s3 s4] ∈
      support (ChainGame.sampleWorld [] (worldBack (hp k) (hn k) hc (world k r).val)) := by
  simp only [world,worldBack,List.map_cons,List.map_nil,ChainGame.sampleWorld,mem_support_bind_iff,
    mem_support_uniformSample,true_and,support_pure,Set.mem_singleton_iff]
  exact ⟨s1,s2,[secondDraw k hc r s1 s2 s3 s4],⟨s3,s4,[],rfl,rfl⟩,rfl⟩

theorem ballast_hit_first_accepted (k : Nat) :
    (firstDraw k (passingTable k) 1 3).guard (initial k (passingTable k)) := by
  norm_num [TransferData.guard,firstDraw,RecipientGame.withSalts,resolve,resolveNote,rebaseTemplate,
    RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,first,initial,DepositData.post,
    deposit,note,St.rootInWindow,St.pushWindow,rootWindow,St.empty,Note.ownedBy,Note.isBallast,
    St.inTreeAt,St.leaves,St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,U128,maxU128,
    hp,hn,Prim,oraclePrim,passingTable,Fin.ext_iff]
  all_goals (simp (disch := omega) only [Nat.mod_eq_of_lt]; norm_num)

theorem ballast_hit_second_rejected (k : Nat) (r : Bool) :
    RecipientGame.runChecked (initial k (passingTable k))
      [Tx.transfer (firstDraw k (passingTable k) 1 3),
        Tx.transfer (secondDraw k (passingTable k) r 1 3 4 5)] = none := by
  have hb : ¬ (secondDraw k (passingTable k) r 1 3 4 5).guard
      ((firstDraw k (passingTable k) 1 3).post (initial k (passingTable k))) := by
    norm_num [TransferData.guard,secondDraw,firstDraw,RecipientGame.withSalts,resolve,resolveNote,output,rebaseTemplate,
      RecipientGame.ROMCommit.rebaseTransfer,RecipientGame.ROMCommit.rebaseNote,first,second,initial,DepositData.post,TransferData.post,
      deposit,note,St.rootInWindow,St.pushWindow,rootWindow,St.empty,Note.ownedBy,Note.isBallast,
      St.inTreeAt,St.leaves,St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,U128,maxU128,
      hp,hn,Prim,oraclePrim,passingTable,Fin.ext_iff]

  simp [RecipientGame.runChecked,RecipientGame.stepChecked,ballast_hit_first_accepted,hb]

abbrev Draw (k : Nat) := (hc : H k) × CommitOnly.Draw (adversary k) (hp k) (hn k) hc
noncomputable def draws (k : Nat) : ProbComp (Draw k) := do
  let hc ← $ᵗ H k
  let d ← atDraws (setup k) (adversary k) (hp k) (hn k) hc
  pure ⟨hc,d⟩
noncomputable def Rejected {k : Nat} (d : Draw k) : Prop :=
  rejected (fun _ => True) (adversary k) (hp k) (hn k) d.1 d.2 = true
noncomputable def fundedPassProbability (k : Nat) : ℝ :=
  (Pr[fun d => ¬Rejected d | draws k]).toReal

set_option linter.constructorNameAsVariable false in
theorem all_draws_funded (k : Nat) (d : Draw k) (hd : d ∈ support (draws k)) :
    ∃ b txs, d.2 = some ((),b,txs) ∧ txs.length = 3 := by
  simp only [draws,support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hd
  obtain ⟨hc,_,x,hx,rfl⟩ := hd
  simp only [atDraws,adversary,run,simulateQ_pure,pure_bind] at hx
  have hl := legal k hc
  dsimp [hp,hn,Prim] at hl
  simp only [hl,if_true,support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hx
  obtain ⟨b,_,sampled,hs,rfl⟩ := hx
  refine ⟨b,_,rfl,?_⟩
  have he := resolves_length (sampleWorld_resolves [] _ sampled hs)
  cases b <;> simp [setup,worldBack,world] at he ⊢ <;> exact he

theorem rejected_probability (k : Nat) :
    (Pr[Rejected | draws k]).toReal = rejectionProbability (fun _ => True) (setup k) (adversary k) := by
  unfold rejectionProbability
  have he := probEvent_bind_pure_comp (draws k)
    (fun x => rejected (fun _ => True) (adversary k) (hp k) (hn k) x.1 x.2)
    (fun b => b = true)
  simp only [Function.comp_def,probEvent_eq_eq_probOutput] at he
  change (Pr[fun x => rejected (fun _ => True) (adversary k) (hp k) (hn k) x.1 x.2 = true | draws k]).toReal = _
  rw [← he]
  simp only [draws,bind_assoc,pure_bind]

theorem funded_pass_lower_bound (k : Nat) :
    1 - ((6*(k+8) : ℝ)*(6*(k+8)-1)/(2*(k+8)^4) + 14/(k+8)) ≤ fundedPassProbability k := by
  have hc := congrArg ENNReal.toReal (probEvent_compl (draws k) Rejected)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),rejected_probability] at hc
  simp only [probFailure_eq_zero,tsub_zero,ENNReal.toReal_one] at hc
  unfold fundedPassProbability
  linarith [rejection_bound k]

theorem funded_pass_large : 999/1000 < fundedPassProbability 65528 := by
  have h := funded_pass_lower_bound 65528
  norm_num at h
  linarith

theorem nullifier_hit_in_game (k : Nat) : ∃ d ∈ support (draws k), Rejected d := by
  let hc := passingTable k
  let txs := (setup k).map (RecipientGame.ROMCommit.rebaseTx (hp k) (hn k) hc) ++
    [Tx.transfer (firstDraw k hc 1 3),Tx.transfer (secondDraw k hc false 1 3 4 5)]
  refine ⟨⟨hc,some ((),false,txs)⟩,?_,?_⟩
  · simp only [draws,mem_support_bind_iff,mem_support_uniformSample,true_and,support_pure,Set.mem_singleton_iff]
    refine ⟨hc,_,?_,rfl⟩
    simp only [atDraws,adversary,run,simulateQ_pure,pure_bind]
    have hl := legal k hc
    dsimp [hp,hn,Prim] at hl
    simp only [hl,if_true,mem_support_bind_iff,mem_support_uniformSample,true_and,support_pure,Set.mem_singleton_iff]
    refine ⟨false,[firstDraw k hc 1 3,secondDraw k hc false 1 3 4 5],sampled_chain_support k hc false 1 3 4 5,?_⟩
    rfl
  · have hr := RecipientGame.runChecked_complete (setup_run k hc)
    change (RecipientGame.runChecked (St.empty (commitPrim (Prim k) 3 hc) (fun _ => True)) txs).isNone = true
    rw [RecipientGame.runChecked_append,hr,Option.bind_some,ballast_hit_second_rejected]
    rfl

end LeanShieldedPool.ChainGame.CommitOnly.FundedChain
