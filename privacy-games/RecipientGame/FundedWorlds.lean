import RecipientGame.Rejection

namespace LeanShieldedPool.FundedWorlds

open GameCorrespondence RecipientGame OracleComp

variable {P : PrimSpec}

theorem empty_transfer_guard_false (sup : P.Token → Prop) (d : TransferData P) :
    ¬ d.guard (St.empty P sup) := by
  intro h
  have hm := h.2.2.2.1
  simp [St.inTreeAt, St.leaves, St.empty] at hm

theorem nonempty_transfer_only_rejected (sup : P.Token → Prop)
    (d : TransferData P) (ds : List (TransferData P)) :
    runChecked (St.empty P sup) ((d :: ds).map Tx.transfer) = none := by
  simp [runChecked, stepChecked, empty_transfer_guard_false]

theorem nonempty_world_not_realizable (sup : P.Token → Prop)
    (ws : List (PoolGame.TransferWitness (gamePrim P)))
    (log : List (PoolGame.Event (gamePrim P))) (hne : ws ≠ []) :
    ¬ RealizesWorld sup ws log := by
  rintro ⟨ds, st, run, hws, _⟩
  cases ds with
  | nil => exact hne hws.symm
  | cons d ds =>
    have h := runChecked_complete run
    rw [nonempty_transfer_only_rejected] at h
    cases h

theorem old_world_realization_false :
    ¬ RealizesWorld (fun _ => True) [SaltCollision.world]
      [SaltCollision.world.toEvent 2 3] :=
  nonempty_world_not_realizable _ _ _ (by simp)

theorem funded_world_has_realization :
    ∃ ds : List (TransferData SaltCollision.primitives), ∃ st,
      Run (fun _ => True) ([Tx.deposit SaltCollision.deposit] ++ ds.map Tx.transfer) st ∧
      ds.map transferWitness = [SaltCollision.world] ∧
      observerView ([Tx.deposit SaltCollision.deposit] ++ ds.map Tx.transfer) =
        [.deposit 0, SaltCollision.world.toEvent 2 3] := by
  exact SaltCollision.funded_world_has_realization

theorem funded_quarter_bound_false
    (observer : OracleComp (PoolGame.observerSpec (gamePrim SaltCollision.primitives)) Bool) :
    ¬ (rejectionProbability (fun _ => True) [Tx.deposit SaltCollision.deposit]
      (Rejection.Fixture.adversary observer) ≤ 1 / 4) := by
  rw [Rejection.Fixture.rejection_eq_five_eighths]
  norm_num

end LeanShieldedPool.FundedWorlds

#print axioms LeanShieldedPool.FundedWorlds.empty_transfer_guard_false
#print axioms LeanShieldedPool.FundedWorlds.nonempty_transfer_only_rejected
#print axioms LeanShieldedPool.FundedWorlds.nonempty_world_not_realizable
#print axioms LeanShieldedPool.FundedWorlds.old_world_realization_false
#print axioms LeanShieldedPool.FundedWorlds.funded_world_has_realization
#print axioms LeanShieldedPool.FundedWorlds.funded_quarter_bound_false
