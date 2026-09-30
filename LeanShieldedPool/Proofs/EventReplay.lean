import LeanShieldedPool.Statements.L4B
import LeanShieldedPool.Draft.NonVacuity

/-! Promoted 2026-09-15 from Draft/EventLog.lean (worker bd-2sz). -/

namespace LeanShieldedPool

variable {P : PrimSpec}

theorem replay_append_event (log : List (Event P)) (event : Event P) :
    replay (log ++ [event]) = replayStep (replay log) event := by
  simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem Step.replay_event {st st' : St P} {tx : Tx P}
    (hs : Step st tx st') :
    replayStep (st.leaves, st.nullifiers) tx.event = (st'.leaves, st'.nullifiers) := by
  cases hs <;>
    simp only [Tx.event, replayStep, DepositData.post, TransferData.post,
      WithdrawData.post, St.leaves, List.map_append, List.map_cons, List.map_nil]

/-- Every accepted history can reconstruct both public lists from its logs alone. -/
theorem Run.replay_events {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) : replay (events txs) = (st.leaves, st.nullifiers) := by
  induction hr with
  | empty => rfl
  | step hr hs ih =>
      simp only [events, List.map_append, List.map_cons, List.map_nil] at ih ⊢
      rw [replay_append_event, ih]
      exact hs.replay_event

theorem eventReplayFaithful_proof (P : PrimSpec) : eventReplayFaithful P :=
  fun _ _ _ hr => hr.replay_events

theorem Run.replay_leaves {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) : replayLeaves (events txs) = st.leaves :=
  congrArg Prod.fst hr.replay_events

theorem Run.replay_nullifiers {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run sup txs st) : replayNullifiers (events txs) = st.nullifiers :=
  congrArg Prod.snd hr.replay_events

namespace EventLogNonVacuity

open NonVacuity

abbrev w1 : WithdrawData Toy := ⟨(), t0.out1, (), 3⟩

theorem deposit_guard : d0.guard st0 := by
  norm_num [DepositData.guard, St.empty, St.leaves, U128, maxU128]

theorem transfer_guard : t0.guard (d0.post st0) := by
  norm_num [TransferData.guard, TransferData.nf1, TransferData.nf2, Note.nf, Note.cm,
    Note.ownedBy, Note.isBallast, St.rootInWindow, St.inTreeAt, St.fresh, St.leaves,
    St.empty, St.pushWindow, rootWindow, DepositData.post, U128, maxU128]

theorem withdraw_guard : w1.guard (t0.post (d0.post st0)) := by
  norm_num [WithdrawData.guard, WithdrawData.nf, TransferData.post,
    TransferData.nf1, TransferData.nf2, Note.nf, Note.cm, Note.ownedBy,
    St.rootInWindow, St.inTreeAt, St.fresh, St.leaves, St.empty, St.pushWindow,
    rootWindow, DepositData.post, U128, maxU128, bump]

theorem all_operations_run :
    Run (fun _ => True) [.deposit d0, .transfer t0, .withdraw w1]
      (w1.post (t0.post (d0.post st0))) :=
  Run.step (Run.step (Run.step Run.empty (Step.deposit deposit_guard))
    (Step.transfer transfer_guard)) (Step.withdraw withdraw_guard)

theorem concrete_events :
    events [.deposit d0, .transfer t0, .withdraw w1] =
      [.deposit 5, .transfer 5 1 10 11, .withdraw 10] := rfl

theorem concrete_replay :
    replay (P := Toy) [.deposit 5, .transfer 5 1 10 11, .withdraw 10] =
      ([5, 10, 11], [10, 5, 1]) := rfl

/-- A deposit, transfer with ballast, and withdrawal witness a nonempty accepted log. -/
theorem replay_nonVacuity :
    ∃ (txs : List (Tx Toy)) (st : St Toy),
      Run (fun _ => True) txs st ∧ txs ≠ [] ∧
      replay (events txs) = (st.leaves, st.nullifiers) ∧
      replay (events txs) = ([5, 10, 11], [10, 5, 1]) := by
  exact ⟨_, _, all_operations_run, List.cons_ne_nil _ _,
    all_operations_run.replay_events, concrete_replay⟩

end EventLogNonVacuity

#print axioms Run.replay_events
#print axioms eventReplayFaithful_proof

end LeanShieldedPool
