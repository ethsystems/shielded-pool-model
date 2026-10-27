import RecipientGame.ROMCommit.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.RecipientGame.ROMCommit
open GameCorrespondence CommitROM CommitROM.Model
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Finite P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Model.Table P cap)] [SampleableType (Message P cap → P.Commitment)]

def projected (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) (ds : List (BoundedTransfer P cap)) :=
  (ds.map (fun d => transferWitness (rebaseTransfer hp hn hc d.val))).map (witnessBack hp hn hc)

theorem projected_length (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) (ds : List (BoundedTransfer P cap)) :
    (projected hp hn hc ds).length = ds.length := by simp [projected, RecipientGame.projectWorld, worldBack]

theorem sampleWorld_fill {α : Type} (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ds : List (BoundedTransfer P cap)) (f : List (PoolGame.Event (gamePrim P)) → ProbComp α) :
    (do let cs ← run (WithdrawGame.ROM.answers hp hn) hc (commitList (messages ds))
        f (fill hn (projected hp hn hc ds) cs)) =
      (do let sampled ← RecipientGame.sampleWorld (worldBack hp hn hc ds)
          f ((observerView (sampled.map Tx.transfer)).map (eventBack hp hn hc))) := by
  induction ds generalizing f with
  | nil => simp [messages, commitList, projected, worldBack, RecipientGame.projectWorld,
      RecipientGame.sampleWorld, fill, observerView, events, run, simulateQ_pure]
  | cons d ds ih =>
    simp only [messages, List.flatMap_cons, List.cons_append, List.nil_append]
    simp only [worldBack, List.map_cons, RecipientGame.sampleWorld, bind_assoc]
    rw [run_commitList_cons]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro s₁
    rw [run_commitList_cons]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro s₂
    let e : PoolGame.Event (gamePrim P) := .transfer
      (hn (d.val.key,(rebaseNote hp hn hc d.val.in1).cm))
      (hn (d.val.key,(rebaseNote hp hn hc d.val.in2).cm))
      (hc ((d.val.out1.token,⟨d.val.out1.amount,d.property.1⟩,d.val.out1.ownerPubkey),s₁))
      (hc ((d.val.out2.token,⟨d.val.out2.amount,d.property.2⟩,d.val.out2.ownerPubkey),s₂))
    change (do let cs ← run (WithdrawGame.ROM.answers hp hn) hc (commitList (messages ds))
               f (e :: fill hn (projected hp hn hc ds) cs)) = _
    rw [ih (fun log => f (e :: log))]
    apply bind_congr; intro sampled
    simp [e, observerView, events, RecipientGame.withSalts, rebaseTransfer, rebaseNote,
      gameEvent, Tx.event, TransferData.nf1, TransferData.nf2, Note.nf, Note.cm,
      oraclePrim, eventBack, d.property.1, d.property.2]
    rfl

theorem run_reduction_choose (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) :
    run (WithdrawGame.ROM.answers hp hn) hc (reduction setup adv hn).choose = (by
      classical
      exact do
        let (l,r,s) ← run (WithdrawGame.ROM.answers hp hn) hc adv.choose
        let log := (observerView (setup.map (rebaseTx hp hn hc))).map (eventBack hp hn hc)
        let wl := projected hp hn hc l.val
        let wr := projected hp hn hc r.val
        if PoolGame.LegalChallenge wl wr then do
          let b ← $ᵗ Bool
          let ds := if b then r else l
          pure (⟨messages ds.val,by rw [messages_length]; exact Nat.mul_le_mul_left 2 ds.property⟩,
            some (s,b,log,wl))
        else pure (⟨[],by simp⟩,none)) := by
  classical
  unfold reduction
  simp only [run, simulateQ_bind, simulateQ_pure]
  apply bind_congr; intro x
  have hh := run_history hp hn hc setup
  have hl := run_witnesses hp hn hc x.1.val
  have hr := run_witnesses hp hn hc x.2.1.val
  unfold run at hh hl hr
  rw [hh, pure_bind, hl, pure_bind, hr, pure_bind]
  change simulateQ _ (if PoolGame.LegalChallenge (projected hp hn hc x.1.val) (projected hp hn hc x.2.1.val)
    then _ else _) = _
  split
  · simp only [simulateQ_bind, simulateQ_pure]
    have hb := run_coins (M := Message P cap) (WithdrawGame.ROM.answers hp hn) hc ($ᵗ Bool)
    unfold run at hb
    rw [hb]
    rfl
  · rfl

theorem reduction_real_eq (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    batchReal (WithdrawGame.ROM.answers hp hn) (reduction setup adv hn) =
      (do let hc ← $ᵗ (Model.Table P cap); atUnguarded setup adv hp hn hc) := by
  classical
  unfold batchReal
  apply bind_congr; intro hc
  rw [run_reduction_choose]
  simp only [atUnguarded, atDraws, bind_assoc]
  apply bind_congr; intro x
  have he : PoolGame.LegalChallenge (projected hp hn hc x.1.val) (projected hp hn hc x.2.1.val) ↔
      RecipientGame.RecipientPair (worldBack hp hn hc x.1.val) (worldBack hp hn hc x.2.1.val) :=
    by simpa [projected, RecipientGame.RecipientPair, RecipientGame.projectWorld, worldBack, List.map_map, Function.comp_def] using
      recipient_back_iff hp hn hc (RecipientGame.projectWorld (worldBack hp hn hc x.1.val))
        (RecipientGame.projectWorld (worldBack hp hn hc x.2.1.val))
  by_cases hl : PoolGame.LegalChallenge (projected hp hn hc x.1.val) (projected hp hn hc x.2.1.val)
  · simp only [hl, he.mp hl, if_true, bind_assoc, pure_bind]
    apply bind_congr; intro b
    have hf (cs : List P.Commitment) :
        fill hn (projected hp hn hc x.1.val) cs =
          fill hn (projected hp hn hc (if b then x.2.1 else x.1).val) cs := by
      cases b
      · rfl
      · exact fill_recipient hn hl cs
    simp only [reduction, run, simulateQ_bind, simulateQ_pure, hf]
    change (do let cs ← run (WithdrawGame.ROM.answers hp hn) hc (commitList (messages (if b then x.2.1 else x.1).val))
               let g ← run (WithdrawGame.ROM.answers hp hn) hc (adv.guess x.2.2
                 ((observerView (setup.map (rebaseTx hp hn hc))).map (eventBack hp hn hc) ++
                   fill hn (projected hp hn hc (if b then x.2.1 else x.1).val) cs))
               pure (b == g)) = _
    rw [sampleWorld_fill hp hn hc (if b then x.2.1 else x.1).val
      (fun log => do
        let g ← run (WithdrawGame.ROM.answers hp hn) hc (adv.guess x.2.2
          ((observerView (setup.map (rebaseTx hp hn hc))).map (eventBack hp hn hc) ++ log))
        pure (b == g))]
    have hw : worldBack hp hn hc (if b then x.2.1 else x.1).val =
        if b then worldBack hp hn hc x.2.1.val else worldBack hp hn hc x.1.val := by cases b <;> rfl
    rw [hw]
    apply bind_congr; intro sampled
    simp only [response, RecipientGame.observerView_append, List.map_append]
  · simp only [hl, he.not.mp hl, if_false, pure_bind, response, commitList, run, simulateQ_pure]
    exact run_coins (WithdrawGame.ROM.answers hp hn) hc ($ᵗ Bool)

end LeanShieldedPool.RecipientGame.ROMCommit
