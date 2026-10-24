import RecipientGame.CommitOnly.Funded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.RecipientGame.CommitOnly.Control
open GameCorrespondence CommitROM CommitROM.Model ROMCommit

abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Bool
  Salt := Fin 64
  Commitment := Fin 16777216
  Nullifier := Fin 16777216
  derivePub := id
  commit := fun _ _ _ _ => 0
  nullify := fun c _ => c
abbrev H := Model.Table Prim 2
abbrev hp := Prim.derivePub
abbrev hn := fun x : Prim.SpendKey × Prim.Commitment => Prim.nullify x.2 x.1

def note (owner : Bool) (salt : Prim.Salt) : Note Prim := ⟨(),0,owner,salt⟩
def deposit : DepositData Prim := ⟨{ note false 0 with amount := 1 },()⟩
def setup : List (Tx Prim) := [.deposit deposit]
noncomputable def initial (hc : H) : St (commitPrim Prim 2 hc) :=
  (⟨ROMCommit.rebaseNote hp hn hc deposit.note,()⟩ : DepositData _).post
    (St.empty _ (fun _ => True))

def transfer (recipient : Bool) : TransferData Prim :=
  ⟨false,deposit.note,note false 1,note recipient 2,{ note true 3 with amount := 1 },1⟩
def world (recipient : Bool) : World Prim 2 1 :=
  ⟨[⟨transfer recipient,by simp [transfer,deposit,note]⟩],by simp⟩

def scan : List Prim.Salt → OracleComp (Spec Prim 2) (List Prim.Commitment)
  | [] => pure []
  | s :: ss => do
    let c ← ROMCommit.cmNote (cap := 2) (note false s)
    let cs ← scan ss
    pure (c :: cs)

noncomputable def allSalts : List Prim.Salt := Finset.univ.toList

noncomputable def guess (log : List (PoolGame.Event (gamePrim Prim))) : OracleComp (Spec Prim 2) Bool := do
  let cs ← scan allSalts
  match log with
  | [.deposit _, .transfer _ _ c _] => pure (decide (c ∉ cs))
  | _ => pure false

noncomputable abbrev adversary : ROMCommit.Adversary Prim 2 1 where
  State := Unit
  choose := pure (world false,world true,())
  guess := fun _ => guess

def coord (owner : Bool) (salt : Prim.Salt) : Message Prim 2 × Prim.Salt :=
  (((),0,owner),salt)

def fundedCoord (owner : Bool) (salt : Prim.Salt) : Message Prim 2 × Prim.Salt :=
  (((),1,owner),salt)

theorem setup_run (hc : H) :
    Run (fun _ => True) (setup.map (ROMCommit.rebaseTx hp hn hc)) (initial hc) := by
  apply Run.step Run.empty
  apply Step.deposit
  norm_num [DepositData.guard,setup,deposit,note,initial,ROMCommit.rebaseTx,
    ROMCommit.rebaseNote,St.empty,St.leaves,U128,maxU128]

theorem run_scan (hc : H) (ss : List Prim.Salt) :
    run (WithdrawGame.ROM.answers hp hn) hc (scan ss) = pure (ss.map (fun s => hc (coord false s))) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [scan,run,simulateQ_bind,simulateQ_pure] at ih ⊢
    have hh := ROMCommit.run_cmNote (cap := 2) hp hn hc (note false s)
    unfold run at hh
    rw [hh,pure_bind,ih,pure_bind]
    rfl

theorem scan_bound (ss : List Prim.Salt) :
    (scan ss).IsQueryBoundP (CommitROM.charged (C := Prim.Commitment) (aux := WithdrawGame.ROM.hashSpec Prim)) ss.length := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    apply (isQueryBoundP_bind (n := 1) (m := ss.length) (cmNote_bound _) ?_).mono (by simp; omega)
    intro c _
    simpa only [bind_pure_comp,isQueryBoundP_map_iff] using ih

theorem query_bound : QueryBound adversary 0 64 := by
  constructor
  · trivial
  · intro state log
    apply (isQueryBoundP_bind (n := allSalts.length) (m := 0) (scan_bound allSalts) ?_).mono
      (by simp [allSalts,Prim])
    intro cs _
    cases log with
    | nil => trivial
    | cons e es =>
        cases e <;> cases es with
        | nil => trivial
        | cons e es => cases e <;> cases es <;> trivial

theorem legal (hc : H) : RecipientPair (worldBack hp hn hc (world false).val)
    (worldBack hp hn hc (world true).val) := by
  simp [RecipientPair,projectWorld,PoolGame.LegalChallenge,PoolGame.RecipientOnly,
    transferWitness,worldBack,world,ROMCommit.rebaseTransfer,ROMCommit.rebaseNote,transfer,deposit,note]

def sampled (hc : H) (b : Bool) (s t : Prim.Salt) : TransferData (commitPrim Prim 2 hc) :=
  withSalts (ROMCommit.rebaseTransfer hp hn hc (transfer b)) s t

theorem sampled_guard (hc : H) (b : Bool) (s t : Prim.Salt)
    (hi : Function.Injective hc) (_hs : s ≠ t) :
    (sampled hc b s t).guard (initial hc) := by
  have hin : hc (fundedCoord false 0) ≠ hc (coord false 1) := by
    intro h
    have he := congrArg (fun x : Message Prim 2 × Prim.Salt => x.1.2.1) (hi h)
    norm_num [coord,fundedCoord,Fin.ext_iff] at he
  have hfirst : hc (coord b s) ≠ hc (fundedCoord false 0) := by
    intro h
    have he := congrArg (fun x : Message Prim 2 × Prim.Salt => x.1.2.1) (hi h)
    norm_num [coord,fundedCoord,Fin.ext_iff] at he
  have hsecond : hc (fundedCoord true t) ≠ hc (fundedCoord false 0) := by
    intro h
    have he := congrArg (fun x : Message Prim 2 × Prim.Salt => x.1.2.2) (hi h)
    simp [fundedCoord] at he
  have hout : hc (coord b s) ≠ hc (fundedCoord true t) := by
    intro h
    have he := congrArg (fun x : Message Prim 2 × Prim.Salt => x.1.2.1) (hi h)
    norm_num [coord,fundedCoord,Fin.ext_iff] at he
  norm_num [sampled,withSalts,ROMCommit.rebaseTransfer,ROMCommit.rebaseNote,
    transfer,deposit,note,initial,DepositData.post,TransferData.guard,St.empty,
    St.rootInWindow,St.pushWindow,rootWindow,St.inTreeAt,Note.ownedBy,Note.isBallast,
    St.fresh,TransferData.nf1,TransferData.nf2,Note.nf,Note.cm,St.leaves,U128,maxU128,
    hp,hn,Prim,oraclePrim,coord,fundedCoord] at *
  exact ⟨hin,hfirst,hsecond,hout⟩

theorem guess_correct (hc : H) (b : Bool) (s t : Prim.Salt)
    (hi : Function.Injective hc) :
    run (WithdrawGame.ROM.answers hp hn) hc
      (guess [.deposit (hc (fundedCoord false 0)), .transfer (hc (fundedCoord false 0)) (hc (coord false 1)) (hc (coord b s)) (hc (fundedCoord true t))]) =
      pure b := by
  unfold guess
  simp only [run,simulateQ_bind]
  have hh := run_scan hc allSalts
  unfold run at hh
  rw [hh,pure_bind]
  have hm : hc (coord b s) ∈ allSalts.map (fun z => hc (coord false z)) ↔ b = false := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨a,_,ha⟩
      have he := congrArg (fun x : Message Prim 2 × Prim.Salt => x.1.2.2) (hi ha)
      exact he.symm
    · intro hb
      subst b
      exact ⟨s,by simp [allSalts],rfl⟩
  cases b <;> simp [hm]

def draw (hc : H) (b : Bool) (s t : Prim.Salt) : ROMCommit.Draw adversary hp hn hc :=
  some ((),b,setup.map (ROMCommit.rebaseTx hp hn hc) ++ [Tx.transfer (sampled hc b s t)])

noncomputable def tapes : ProbComp (H × Bool × Prim.Salt × Prim.Salt) := do
  let hc ← $ᵗ H
  let b ← $ᵗ Bool
  let s ← $ᵗ Prim.Salt
  let t ← $ᵗ Prim.Salt
  pure (hc,b,s,t)

theorem atDraws_eq (hc : H) :
    atDraws setup adversary hp hn hc = (do
      let b ← $ᵗ Bool
      let s ← $ᵗ Prim.Salt
      let t ← $ᵗ Prim.Salt
      pure (draw hc b s t)) := by
  simp only [atDraws,adversary,run,simulateQ_pure,pure_bind,legal,if_true]
  apply bind_congr
  intro b
  cases b <;> simp [worldBack,world,sampleWorld,draw,sampled]

theorem experiment_eq : experiment (fun _ => True) setup adversary = (do
    let x ← tapes
    ROMCommit.checkedResponse (fun _ => True) adversary hp hn x.1 (draw x.1 x.2.1 x.2.2.1 x.2.2.2)) := by
  change ($ᵗ H >>= fun hc => atDraws setup adversary hp hn hc >>=
    ROMCommit.checkedResponse (fun _ => True) adversary hp hn hc) = _
  simp only [atDraws_eq,tapes,bind_assoc,pure_bind]

theorem rejection_eq : rejectionProbability (fun _ => True) setup adversary =
    (Pr[fun x => ROMCommit.rejected (fun _ => True) adversary hp hn x.1
      (draw x.1 x.2.1 x.2.2.1 x.2.2.2) = true | tapes]).toReal := by
  unfold rejectionProbability
  change (Pr[= true | do
    let hc ← $ᵗ H
    let d ← atDraws setup adversary hp hn hc
    pure (ROMCommit.rejected (fun _ => True) adversary hp hn hc d)]).toReal = _
  have he := probEvent_bind_pure_comp tapes
    (fun x => ROMCommit.rejected (fun _ => True) adversary hp hn x.1
      (draw x.1 x.2.1 x.2.2.1 x.2.2.2)) (fun b => b = true)
  simp only [Function.comp_def,probEvent_eq_eq_probOutput] at he
  rw [← he]
  simp only [atDraws_eq,tapes,bind_assoc,pure_bind]

theorem rejected_good (hc : H) (b : Bool) (s t : Prim.Salt)
    (hi : Function.Injective hc) (hs : s ≠ t) :
    ROMCommit.rejected (fun _ => True) adversary hp hn hc (draw hc b s t) = false := by
  have hd := runChecked_complete (setup_run hc)
  simp only [ROMCommit.rejected,draw,runChecked_append,hd,Option.bind_some]
  simp [runChecked,stepChecked,sampled_guard hc b s t hi hs]

theorem response_good (hc : H) (b : Bool) (s t : Prim.Salt) (hi : Function.Injective hc) :
    ROMCommit.response adversary hp hn hc (draw hc b s t) = pure true := by
  change (do
    let g ← run (WithdrawGame.ROM.answers hp hn) hc
      (guess [.deposit (hc (fundedCoord false 0)), .transfer (hc (fundedCoord false 0)) (hc (coord false 1))
        (hc (coord b s)) (hc (fundedCoord true t))])
    pure (b == g)) = pure true
  rw [guess_correct hc b s t hi,pure_bind]
  simp

theorem checkedResponse_good (hc : H) (b : Bool) (s t : Prim.Salt)
    (hi : Function.Injective hc) (hs : s ≠ t) :
    ROMCommit.checkedResponse (fun _ => True) adversary hp hn hc (draw hc b s t) = pure true := by
  simp only [ROMCommit.checkedResponse,rejected_good hc b s t hi hs,Bool.false_eq_true,if_false]
  exact response_good hc b s t hi

def Bad (x : H × Bool × Prim.Salt × Prim.Salt) : Prop :=
  ¬Function.Injective x.1 ∨ x.2.2.1 = x.2.2.2

noncomputable def badProbability : ℝ≥0∞ := Pr[Bad | tapes]

theorem failure_le_bad : Pr[= false | experiment (fun _ => True) setup adversary] ≤ badProbability := by
  rw [experiment_eq,← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_probEvent
  intro x _ hx
  have hh : Function.Injective x.1 ∧ x.2.2.1 ≠ x.2.2.2 := by simpa [Bad] using hx
  rw [checkedResponse_good _ _ _ _ hh.1 hh.2]
  simp

theorem rejection_le_bad : rejectionProbability (fun _ => True) setup adversary ≤ badProbability.toReal := by
  rw [rejection_eq]
  apply ENNReal.toReal_mono (by unfold badProbability; finiteness)
  apply probEvent_mono
  intro x _ hx
  by_contra hb
  have hh : Function.Injective x.1 ∧ x.2.2.1 ≠ x.2.2.2 := by simpa [Bad] using hb
  rw [rejected_good _ _ _ _ hh.1 hh.2] at hx
  cases hx

theorem bad_bound : badProbability ≤ (256*255 : ℝ≥0∞)/16777216 + 1/64 := by
  unfold badProbability Bad
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add
  · have he : Pr[fun x : H × Bool × Prim.Salt × Prim.Salt => ¬Function.Injective x.1 | tapes] =
        Pr[fun hc : H => ¬Function.Injective hc | $ᵗ H] := by
      change Pr[(fun hc : H => ¬Function.Injective hc) ∘ Prod.fst | tapes] = _
      rw [← probEvent_bind_pure_comp tapes Prod.fst (fun hc => ¬Function.Injective hc)]
      simp only [tapes,bind_assoc,pure_bind]
      conv_rhs => rw [← bind_pure ($ᵗ H)]
      apply probEvent_bind_congr
      intro hc _
      simp only [Function.comp_def,probEvent_bind_const,probFailure_eq_zero,tsub_zero,one_mul]
    rw [he]
    simpa only [Model.Message,Prim,Fintype.card_prod,Fintype.card_unit,Fintype.card_fin,
      Fintype.card_bool,Nat.mul_one,Nat.one_mul, Nat.reduceMul,Nat.reduceSub,Nat.cast_ofNat,show (256 : ℝ≥0∞)*255=65280 by norm_num] using
      (WithdrawGame.ROM.keymap_collision_bound (I := Message Prim 2 × Prim.Salt) (K := Prim.Commitment))
  · have he : Pr[fun x : H × Bool × Prim.Salt × Prim.Salt => x.2.2.1 = x.2.2.2 | tapes] = 1/64 := by
      simp only [tapes]
      rw [probEvent_bind_of_const ($ᵗ H) (r := 1/64)]
      · simp
      · intro hc _
        rw [probEvent_bind_of_const ($ᵗ Bool) (r := 1/64)]
        · simp
        · intro b _
          rw [probEvent_bind_of_const ($ᵗ Prim.Salt) (r := 1/64)]
          · simp
          · intro s _
            simp only [bind_pure_comp,probEvent_map,Function.comp_def]
            rw [show (fun t : Prim.Salt => s = t) = (fun t => t = s) from funext (fun t => propext eq_comm)]
            simp only [probEvent_eq_eq_probOutput,probOutput_uniformSample,Fintype.card_fin]
            norm_num
    exact le_of_eq he

theorem bad_real_bound : badProbability.toReal ≤ 1/25 := by
  have h := ENNReal.toReal_mono (by finiteness) bad_bound
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at h
  norm_num [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_inv] at h
  linarith

theorem attacker_advantage : 23/50 ≤ advantage (fun _ => True) setup adversary := by
  have hf := ENNReal.toReal_mono (by unfold badProbability; finiteness) failure_le_bad
  have hb := bad_real_bound
  have hs := congrArg ENNReal.toReal
    (probOutput_true_add_false (experiment (fun _ => True) setup adversary))
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hs
  simp only [probFailure_eq_zero,tsub_zero,ENNReal.toReal_one] at hs
  unfold advantage
  have hab := le_abs_self ((Pr[= true | experiment (fun _ => True) setup adversary]).toReal - 1/2)
  linarith

theorem query_attack_breaks_perfect_hiding : 0 < advantage (fun _ => True) setup adversary := by
  have h := attacker_advantage
  linarith

theorem dropping_guess_query_charge_false :
    ¬advantage (fun _ => True) setup adversary ≤
      (2*1 : ℝ)*(0+0+4*1+6*1)/Fintype.card Prim.Salt +
        rejectionProbability (fun _ => True) setup adversary / 2 := by
  have ha := attacker_advantage
  have hr := rejection_le_bad.trans bad_real_bound
  have hc : (Fintype.card Prim.Salt : ℝ) = 64 := rfl
  rw [hc]
  norm_num
  linarith

abbrev so (hc : H) := unifFwdAnswerImpl (QueryImpl.ofFn hc + WithdrawGame.ROM.answers hp hn)

theorem trace_scan_then (hc : H) (ss : List Prim.Salt) (f : List Prim.Commitment → Bool) :
    trace (so hc) (do let cs ← scan ss; pure (f cs)) =
      pure (f (ss.map (fun s => hc (coord false s))),ss) := by
  induction ss generalizing f with
  | nil => rfl
  | cons s ss ih =>
    simp only [scan,bind_assoc,pure_bind]
    change trace (so hc) (liftM ((Spec Prim 2).query (.inr (.inl (coord false s)))) >>=
      fun c => do let cs ← scan ss; pure (f (c::cs))) = _
    rw [trace_query_bind]
    change (do
      let c ← pure (hc (coord false s))
      let z ← trace (so hc) (do let cs ← scan ss; pure (f (c::cs)))
      pure (z.1,[s] ++ z.2)) = _
    simp only [pure_bind,ih,List.map_cons,List.singleton_append]

theorem trace_guess (hc : H) (fund a b c d : Prim.Commitment) :
    trace (so hc) (adversary.guess () [.deposit fund, .transfer a b c d]) =
      pure (decide (c ∉ allSalts.map (fun s => hc (coord false s))),allSalts) :=
  trace_scan_then hc allSalts (fun cs => decide (c ∉ cs))

theorem challenge_salt_in_trace (hc : H) (b : Bool) (s t : Prim.Salt)
    (z : Bool × List Prim.Salt)
    (hz : z ∈ support (trace (so hc) (adversary.guess ()
      [.deposit (hc (fundedCoord false 0)), .transfer (hc (fundedCoord false 0)) (hc (coord false 1)) (hc (coord b s)) (hc (fundedCoord true t))]))) :
    s ∈ z.2 := by
  rw [trace_guess] at hz
  simp only [support_pure,Set.mem_singleton_iff] at hz
  subst z
  simp [allSalts]

theorem query_bound_zero_false : ¬QueryBound adversary 0 0 := by
  intro h
  let hc : H := fun _ => 0
  have ht := trace_length_bound (so hc) (adversary.guess () [.deposit 0, .transfer 0 0 0 0]) 0
    (h.2 () [.deposit 0, .transfer 0 0 0 0])
  rw [trace_guess] at ht
  have hh := ht (decide (0 ∉ allSalts.map (fun s => hc (coord false s))),allSalts) (by simp)
  simp [allSalts,Prim] at hh

end LeanShieldedPool.RecipientGame.CommitOnly.Control
