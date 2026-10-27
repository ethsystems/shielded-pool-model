import RecipientGame.ROMCommit.Rejection
import CommitROM.Controls

set_option autoImplicit false
set_option relaxedAutoImplicit false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.RecipientGame.ROMCommit.Control
open GameCorrespondence CommitROM CommitROM.Model

/-- The chosen finite amount domain matches the frozen amount guard at this cap. -/
theorem u128_iff_amount_lt (a : Nat) : U128 a ↔ a < 2^128 := by
  unfold U128 maxU128
  omega

/-- Generic commitment control: the actual guess-phase trace includes every possible salt. -/
theorem challenge_salt_in_trace (h : Bool × Bool → Bool) (cm salt : Bool) :
    ∀ z ∈ support (CommitROM.trace
      (unifFwdAnswerImpl (QueryImpl.ofFn h + CommitROM.Control.other))
      (CommitROM.Control.adversary.guess () cm)), salt ∈ z.2 := by
  rw [CommitROM.Control.trace_queries]
  simpa only [support_pure, Set.mem_singleton_iff, forall_eq] using
    CommitROM.Control.challenge_salt_queried salt

/-- Removing the generic commitment game's query charge yields a false statement. -/
theorem dropping_query_charge_false :
    ¬ CommitROM.advantage CommitROM.Control.other CommitROM.Control.adversary ≤
      (0 : ℝ) / Fintype.card Bool := CommitROM.Control.zero_query_bound_false

/-- A separate salt-disclosure experiment exceeds the one-query, eight-salt allowance. -/
theorem disclosed_salt_bound_false :
    ¬ |(Pr[= true | CommitROM.Control.disclosed]).toReal - 1/2| ≤
      (1 : ℝ) / Fintype.card (Fin 8) := CommitROM.Control.disclosed_bound_false

abbrev Prim : PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Bool
  SpendKey := Unit
  Salt := Bool
  Commitment := Bool
  Nullifier := Bool
  derivePub := fun _ => false
  commit := fun _ _ _ _ => false
  nullify := fun c _ => c

/-- Uniform-table averaging does not give a spread premise for each table realization. -/
theorem constant_table_not_spread :
    ¬ Rejection.CommitmentSpread (P := oraclePrim Prim 1 (fun _ => false)
      (fun x => x.2) (fun _ => false)) 2 := by
  intro h
  have hp := h.point_bound (⟨(),0,false,false⟩ : Note (oraclePrim Prim 1 (fun _ => false)
      (fun x => x.2) (fun _ => false))) false
  norm_num [oraclePrim, Prim] at hp

end LeanShieldedPool.RecipientGame.ROMCommit.Control
