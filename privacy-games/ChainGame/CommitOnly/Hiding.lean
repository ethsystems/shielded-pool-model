import ChainGame.CommitOnly.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal OracleComp.DeferredSampling

namespace LeanShieldedPool.ChainGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model
open RecipientGame.ROMCommit (rebaseTx witnesses history messages fill projected projected_length messages_length run_history run_witnesses)
variable {P : PrimSpec} {cap n : Nat}
variable [SampleableType P.Salt] [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Finite P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Model.Table P cap)] [SampleableType (Message P cap → P.Commitment)]

theorem body_worldBack (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ts : List (BoundedTemplate P cap)) :
    (worldBack hp hn hc ts).map Template.body = RecipientGame.ROMCommit.worldBack hp hn hc (bodies ts) := by
  simp [worldBack, bodies, RecipientGame.ROMCommit.worldBack, rebaseTemplate]

theorem sampleWorld_fill {α : Type} (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ts : List (BoundedTemplate P cap)) (f : List (PoolGame.Event (gamePrim P)) → ProbComp α) :
    (do let cs ← run (WithdrawGame.ROM.answers hp hn) hc (commitList (messages (bodies ts)))
        f (rewrite hn ts [] (fill hn (projected hp hn hc (bodies ts)) cs))) =
      (do let sampled ← ChainGame.sampleWorld [] (worldBack hp hn hc ts)
          f ((observerView (sampled.map Tx.transfer)).map (eventBack hp hn hc))) := by
  rw [RecipientGame.ROMCommit.sampleWorld_fill hp hn hc (bodies ts)
    (fun log => f (rewrite hn ts [] log))]
  symm
  rw [sampleWorld_static (worldBack hp hn hc ts) []
    (fun log => f (log.map (eventBack hp hn hc)))]
  simp only [body_worldBack, commitmentHistory, List.map_nil]
  apply bind_congr
  intro ds
  rw [rewrite_back]

theorem run_reduction_choose (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) :
    run (WithdrawGame.ROM.answers hp hn) hc (reduction setup adv hn).choose = (by
      classical
      exact do
        let (l,r,s) ← run (WithdrawGame.ROM.answers hp hn) hc adv.choose
        let log := (observerView (setup.map (rebaseTx hp hn hc))).map (eventBack hp hn hc)
        let wl := projected hp hn hc (bodies l.val)
        let wr := projected hp hn hc (bodies r.val)
        if Aligned l.val r.val ∧ PoolGame.LegalChallenge wl wr then do
          let b ← $ᵗ Bool
          let ds := if b then r else l
          pure (⟨messages (bodies ds.val),by rw [messages_length, bodies_length]; exact Nat.mul_le_mul_left 2 ds.property⟩,
            some (s,b,log,wl,l.val))
        else pure (⟨[],by simp⟩,none)) := by
  classical
  unfold reduction
  simp only [run, simulateQ_bind, simulateQ_pure]
  apply bind_congr; intro x
  have hh := run_history hp hn hc setup
  have hl := run_witnesses hp hn hc (bodies x.1.val)
  have hr := run_witnesses hp hn hc (bodies x.2.1.val)
  unfold run at hh hl hr
  rw [hh, pure_bind, hl, pure_bind, hr, pure_bind]
  change simulateQ _ (if Aligned x.1.val x.2.1.val ∧ PoolGame.LegalChallenge (projected hp hn hc (bodies x.1.val)) (projected hp hn hc (bodies x.2.1.val))
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
  have he := recipient_back_iff hp hn hc x.1.val x.2.1.val
  by_cases hl : Aligned x.1.val x.2.1.val ∧ PoolGame.LegalChallenge (projected hp hn hc (bodies x.1.val)) (projected hp hn hc (bodies x.2.1.val))
  · simp only [hl, true_and, he.mpr hl, if_true, bind_assoc, pure_bind]
    apply bind_congr; intro b
    have hf (cs : List P.Commitment) :
        rewrite hn x.1.val [] (fill hn (projected hp hn hc (bodies x.1.val)) cs) =
          rewrite hn (if b then x.2.1 else x.1).val []
            (fill hn (projected hp hn hc (bodies (if b then x.2.1 else x.1).val)) cs) := by
      cases b
      · rfl
      · rw [RecipientGame.ROMCommit.fill_recipient hn hl.2]
        exact rewrite_recipient hp hn hc x.1.val x.2.1.val hl.1 hl.2 [] _
    simp only [reduction, run, simulateQ_bind, simulateQ_pure, hf]
    change (do let cs ← run (WithdrawGame.ROM.answers hp hn) hc (commitList (messages (bodies (if b then x.2.1 else x.1).val)))
               let g ← run (WithdrawGame.ROM.answers hp hn) hc (adv.guess x.2.2
                 ((observerView (setup.map (rebaseTx hp hn hc))).map (eventBack hp hn hc) ++
                   rewrite hn (if b then x.2.1 else x.1).val [] (fill hn (projected hp hn hc (bodies (if b then x.2.1 else x.1).val)) cs)))
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
  · simp only [hl, true_and, he.not.mpr hl, if_false, pure_bind, response, commitList, run, simulateQ_pure]
    exact run_coins (WithdrawGame.ROM.answers hp hn) hc ($ᵗ Bool)

end LeanShieldedPool.ChainGame.CommitOnly
