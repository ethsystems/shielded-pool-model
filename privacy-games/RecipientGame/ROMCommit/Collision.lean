import RecipientGame.ROMCommit.Security
import CommitROM.Collision

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.ROMCommit
open GameCorrespondence CommitROM CommitROM.Model
variable {P : PrimSpec} {cap n : Nat}

def outputs : List (PoolGame.Event (gamePrim P)) → List P.Commitment
  | [] => []
  | .deposit c :: es => c :: outputs es
  | .transfer _ _ c₁ c₂ :: es => c₁ :: c₂ :: outputs es
  | .withdraw _ :: es => outputs es

theorem outputs_append (xs ys : List (PoolGame.Event (gamePrim P))) :
    outputs (xs ++ ys) = outputs xs ++ outputs ys := by
  induction xs with
  | nil => rfl
  | cons e es ih => cases e <;> simp [outputs, ih]

theorem outputs_length_le (es : List (PoolGame.Event (gamePrim P))) :
    (outputs es).length ≤ 2*es.length := by
  induction es with
  | nil => simp [outputs]
  | cons e es ih => cases e <;> simp only [outputs, List.length_cons] <;> omega

theorem view_length (txs : List (Tx P)) : (observerView txs).length = txs.length := by
  simp [observerView, events]

theorem step_leaves {st st' : St P} {tx : Tx P} (h : Step st tx st') :
    st'.leaves = st.leaves ++ outputs (observerView [tx]) := by
  cases h <;> simp [St.leaves, DepositData.post, TransferData.post, WithdrawData.post,
    observerView, events, Tx.event, gameEvent, outputs]

theorem run_leaves {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (h : Run sup txs st) : st.leaves = outputs (observerView txs) := by
  induction h with
  | empty => rfl
  | step hr hs ih => rw [step_leaves hs, ih, RecipientGame.observerView_append, outputs_append]

theorem collision_old_congr {C : Type} (old old' cs : List C)
    (h : ∀ c, c ∈ old ↔ c ∈ old') : CommitROM.Collision old cs ↔ CommitROM.Collision old' cs := by
  induction cs generalizing old old' with
  | nil => rfl
  | cons c cs ih =>
    simp only [CommitROM.Collision, h c]
    rw [ih (c :: old) (c :: old') (by intro x; simp only [List.mem_cons, h x])]

theorem collision_fill (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (ws : List (PoolGame.TransferWitness (gamePrim P))) (cs old : List P.Commitment) :
    CommitROM.Collision old (outputs (fill hn ws cs)) → CommitROM.Collision old cs := by
  induction ws generalizing cs old with
  | nil => simp [fill, outputs, CommitROM.Collision]
  | cons w ws ih =>
    cases cs with
    | nil => simp [fill, outputs, CommitROM.Collision]
    | cons c₁ cs => cases cs with
      | nil => simp [fill, outputs, CommitROM.Collision]
      | cons c₂ cs =>
        simp only [fill, outputs, CommitROM.Collision]
        exact fun h => h.imp id (fun h => h.imp id (ih cs (c₂ :: c₁ :: old)))

theorem collision_iff_outputs (st : St P) (ds : List (TransferData P)) :
    Rejection.Collision st ds ↔ CommitROM.Collision st.leaves (outputs (observerView (ds.map Tx.transfer))) := by
  classical
  induction ds generalizing st with
  | nil => rfl
  | cons d ds ih =>
    simp only [Rejection.Collision, ih]
    have ht : (d.post st).leaves = st.leaves ++ [d.out1.cm,d.out2.cm] := by
      simp [TransferData.post, St.leaves]
    rw [ht, collision_old_congr (st.leaves ++ [d.out1.cm,d.out2.cm])
      (d.out2.cm :: d.out1.cm :: st.leaves) _ (by intro c; simp; tauto)]
    change (¬Rejection.OutputFresh d st ∨ _) ↔
      (d.out1.cm ∈ st.leaves ∨ d.out2.cm ∈ d.out1.cm :: st.leaves ∨ _)
    simp only [Rejection.OutputFresh, not_and_or, not_not, List.mem_cons]
    tauto

def oldCommitments (setup : List (Tx P)) (adv : Adversary P cap n)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) : (reduction setup adv hn).State → List P.Commitment
  | none => []
  | some (_,_,log,_) => outputs (log.take setup.length)

theorem oldCommitments_bound (setup : List (Tx P)) (adv : Adversary P cap n)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (s : (reduction setup adv hn).State) :
    (oldCommitments setup adv hn s).length ≤ 2*setup.length := by
  cases s with
  | none => simp [oldCommitments]
  | some x => exact (outputs_length_le _).trans (Nat.mul_le_mul_left 2 (List.length_take_le _ _))

noncomputable def collisionReduction (setup : List (Tx P)) (adv : Adversary P cap n)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    BatchAdversary (Message P cap) P.Salt P.Commitment (WithdrawGame.ROM.hashSpec P) (2*n) := by
  classical
  exact {
    State := (reduction setup adv hn).State
    choose := (reduction setup adv hn).choose
    guess := fun s cs => match s with
      | none => pure false
      | some (_,_,_,wl) => pure (decide (CommitROM.Collision
          (oldCommitments setup adv hn s) (outputs (fill hn wl cs)))) }

noncomputable def collisionDraw (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (hc : Model.Table P cap) : Draw adv hp hn hc → Bool := by
  classical
  exact fun d => match d with
  | none => false
  | some (_,_,txs) => decide (CommitROM.Collision
      (outputs ((observerView (txs.take setup.length)).map (eventBack hp hn hc)))
      (outputs ((observerView (txs.drop setup.length)).map (eventBack hp hn hc))))

variable [SampleableType P.Salt] [Finite P.Token] [Finite P.PubKey] [Fintype P.Salt]
  [Fintype P.Commitment] [Nonempty P.Commitment] [SampleableType P.Commitment]
  [SampleableType (Model.Table P cap)] [SampleableType (Message P cap → P.Commitment)]

theorem collisionReduction_le (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    Pr[= true | batchReal (WithdrawGame.ROM.answers hp hn) (collisionReduction setup adv hn)] ≤
      Pr[= true | batchReal (WithdrawGame.ROM.answers hp hn)
        (collisionTest (reduction setup adv hn) (oldCommitments setup adv hn))] := by
  classical
  unfold batchReal
  apply probOutput_bind_mono; intro hc _
  apply probOutput_bind_mono; intro x _
  apply probOutput_bind_mono; intro cs _
  cases hs : x.2 with
  | none => simp [collisionReduction, collisionTest, hs, run, simulateQ_pure]
  | some s =>
    simp only [collisionReduction, collisionTest, hs, run, simulateQ_pure]
    by_cases ht : CommitROM.Collision (oldCommitments setup adv hn (some s)) (outputs (fill hn s.2.2.2 cs))
    · simp [ht, collision_fill hn s.2.2.2 cs _ ht]
    · simp [ht]

theorem collisionReduction_eq (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    batchReal (WithdrawGame.ROM.answers hp hn) (collisionReduction setup adv hn) = (do
      let hc ← $ᵗ (Model.Table P cap)
      let d ← atDraws setup adv hp hn hc
      pure (collisionDraw setup adv hp hn hc d)) := by
  classical
  unfold batchReal
  apply bind_congr; intro hc
  change (run (WithdrawGame.ROM.answers hp hn) hc (reduction setup adv hn).choose >>= _) = _
  rw [run_reduction_choose]
  dsimp only [collisionReduction, reduction]
  simp only [atDraws, bind_assoc]
  apply bind_congr; intro x
  have he : PoolGame.LegalChallenge (projected hp hn hc x.1.val) (projected hp hn hc x.2.1.val) ↔
      RecipientGame.RecipientPair (worldBack hp hn hc x.1.val) (worldBack hp hn hc x.2.1.val) := by
    simpa [projected, RecipientGame.RecipientPair, RecipientGame.projectWorld, worldBack, List.map_map, Function.comp_def] using
      recipient_back_iff hp hn hc (RecipientGame.projectWorld (worldBack hp hn hc x.1.val))
        (RecipientGame.projectWorld (worldBack hp hn hc x.2.1.val))
  by_cases hl : PoolGame.LegalChallenge (projected hp hn hc x.1.val) (projected hp hn hc x.2.1.val)
  · simp only [hl, he.mp hl, if_true, bind_assoc, pure_bind]
    apply bind_congr; intro b
    have hf (cs : List P.Commitment) : fill hn (projected hp hn hc x.1.val) cs =
        fill hn (projected hp hn hc (if b then x.2.1 else x.1).val) cs := by
      cases b
      · rfl
      · exact fill_recipient hn hl cs
    have hlog : (List.map (eventBack hp hn hc) (observerView (setup.map (rebaseTx hp hn hc)))).length = setup.length := by
      simp [view_length]
    simp only [collisionReduction, oldCommitments, run, simulateQ_pure, hf]
    rw [← hlog, List.take_length]
    change (do
      let cs ← run (WithdrawGame.ROM.answers hp hn) hc (commitList (messages (if b then x.2.1 else x.1).val))
      pure (decide (CommitROM.Collision
        (outputs ((observerView (setup.map (rebaseTx hp hn hc))).map (eventBack hp hn hc)))
        (outputs (fill hn (projected hp hn hc (if b then x.2.1 else x.1).val) cs))))) = _
    rw [sampleWorld_fill hp hn hc (if b then x.2.1 else x.1).val
      (fun log => pure (decide (CommitROM.Collision
        (outputs ((observerView (setup.map (rebaseTx hp hn hc))).map (eventBack hp hn hc))) (outputs log))))]
    have hw : worldBack hp hn hc (if b then x.2.1 else x.1).val =
        if b then worldBack hp hn hc x.2.1.val else worldBack hp hn hc x.1.val := by cases b <;> rfl
    rw [hw]
    apply bind_congr; intro sampled
    simp only [pure_bind, collisionDraw]
    have hlen : (setup.map (rebaseTx hp hn hc)).length = setup.length := List.length_map _
    rw [← hlen, List.take_left, List.drop_left]
  · simp [hl, he.not.mp hl, collisionReduction, collisionDraw, commitList, run, simulateQ_pure]

theorem atCollision_le (setup : List (Tx P)) (adv : Adversary P cap n)
    (hp : P.SpendKey → P.PubKey) (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (qc qg : Nat) (hq : QueryBound adv qc qg) :
    (Pr[= true | do
      let hc ← $ᵗ (Model.Table P cap)
      let d ← atDraws setup adv hp hn hc
      pure (collisionDraw setup adv hp hn hc d)]).toReal ≤
      (2*n : ℝ)*(qc+4*setup.length+6*n)/Fintype.card P.Salt +
        (2*n : ℝ)*(2*setup.length+2*n)/Fintype.card P.Commitment := by
  have h := batch_collision_le (WithdrawGame.ROM.answers hp hn) (reduction setup adv hn)
    (oldCommitments setup adv hn) (2*setup.length) (qc+4*setup.length+4*n)
    (oldCommitments_bound setup adv hn) (reduction_bound setup adv hn qc qg hq).1
  have hr := ENNReal.toReal_mono (by finiteness)
    (collisionReduction_le setup adv hp hn)
  rw [collisionReduction_eq] at hr
  refine hr.trans (h.trans_eq ?_)
  push_cast
  ring

end LeanShieldedPool.RecipientGame.ROMCommit
