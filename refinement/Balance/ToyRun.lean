import Balance.NonVacuity
import Refinement.NonVacuity

/-!
# Token balances: `refineB_run` with every premise instantiated

The toy pool `ToyRun.X` (address 99) on its history: an admin call, a reverted `setVerifier`, a
deposit of 3 of token 5 from funder 7, a transfer, and a withdrawal of 3 to recipient 8. The token
chain is the honest `BalanceToy.KH`. Every premise of `refineB_run` holds, so the external pool
balance equals the model's balance field and the live note value: both are 0 at the end, after 3 was
deposited and 3 withdrawn.

The toy verifier accepts only fixed witnesses. The instance shows the premises are jointly
satisfiable; it says nothing about the deployed pool or any real token.
-/

namespace LeanShieldedPool.Refine.BalanceToyRun

open LeanShieldedPool LeanShieldedPool.Refine BalanceToy

theorem hinjT : Function.Injective Toy.E.tok := fun _ _ h => h

/-- The two readings on the toy pool: its verifier binds the funder to 7, and its owner calls
have empty traces. -/
theorem hRd : PoolCallReadings ToyRun.X where
  deposit_funder := fun {_ _ _ _ _ fund _ _ _ _} _ hx => by
    obtain ⟨-, -, -, ⟨-, -, -, -, hf, -⟩, -⟩ := hx
    have e : fund = 7 := hf
    rw [e]
    decide
  owner_quiet := fun {_ c tr _} _ hx ho => by
    cases c <;> first
      | exact False.elim hx
      | (obtain ⟨h, -⟩ := hx; rw [h]; rfl)
      | simp only [Call.isOwner, Bool.false_eq_true] at ho

/-- After the withdrawal: the pool holds 0 of token 5, recipient 8 holds 3. -/
def w3 : Nat → Nat → Nat := fun t a =>
  if t = 5 ∧ a = 99 then 0 else if t = 5 ∧ a = 8 then 3 else w1 t a

theorem quiet (w : Nat → Nat → Nat) (c : Call) : KH.OnExec w c [] w := by
  intro t a
  simp only [debits, tokenCalls, List.filter_nil, List.map_nil, List.sum_nil, add_zero, credits]

theorem m4 : KH.OnExec w1 (.withdraw 39 5 3 8 96) [.transfer 5 8 3] w3 := by
  intro t a
  by_cases ht : t = 5 <;> by_cases h8 : a = 8 <;> by_cases h99 : a = 99 <;> subst_vars <;>
    simp_all [w3, w1, wInit, debits, credits, tokenCalls, Ext.isNested, Ext.debit, Ext.credit] <;>
    (try split_ifs) <;> omega

theorem accN : AcceptedB ToyRun.X KH ToyRun.hist ToyRun.σ3 w3 := by
  have e1 : ToyRun.X.Exec (Storage.genesis 1 2 3) (.addSupportedToken 5) [] ToyRun.σa := ⟨rfl, rfl⟩
  have e2 : ToyRun.X.Exec ToyRun.σa (.deposit 7 9 5 3 7 0 0) [.transferFrom 5 7 99 3] ToyRun.σ1 :=
    ⟨rfl, by decide, rfl, ⟨rfl, rfl, rfl, rfl, rfl, by decide⟩, by unfold Canonical; decide,
      rfl, rfl⟩
  have e3 : ToyRun.X.Exec ToyRun.σ1 (.transfer 9 26 39 46 9 0) [] ToyRun.σ2 :=
    ⟨by decide, rfl, rfl, Or.inl (by decide), by decide, by decide, by decide,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨1, by decide, by decide, by decide⟩, rfl, rfl, rfl,
        rfl, by show (3 : Nat) ≤ 2 ^ 128 - 1; decide, Nat.zero_le _,
        by show (3 : Nat) ≤ 2 ^ 128 - 1; decide, Nat.zero_le _, rfl⟩,
      by unfold Canonical; decide, rfl, rfl⟩
  have e4 : ToyRun.X.Exec ToyRun.σ2 (.withdraw 39 5 3 8 96) [.transfer 5 8 3] ToyRun.σ3 :=
    ⟨by decide, by decide, Or.inl (by decide),
      ⟨rfl, rfl, rfl, rfl, rfl, ⟨3, by decide, by decide, by decide⟩, rfl,
        by show (3 : Nat) ≤ 2 ^ 128 - 1; decide⟩,
      by unfold Canonical; decide, rfl, rfl⟩
  have a1 : AcceptedB ToyRun.X KH ([] ++ [Call.addSupportedToken 5]) ToyRun.σa wInit :=
    AcceptedB.snoc AcceptedB.nil e1 (quiet wInit _)
  have a1' : AcceptedB ToyRun.X KH ([] ++ [Call.addSupportedToken 5]) ToyRun.σa wInit :=
    AcceptedB.fail a1 (show ToyRun.X.Fail ToyRun.σa (.setVerifier 0) ToyRun.σa from rfl)
      (show KH.OnFail wInit (.setVerifier 0) wInit from rfl)
  have a2 : AcceptedB ToyRun.X KH ([] ++ [Call.addSupportedToken 5] ++ [.deposit 7 9 5 3 7 0 0])
      ToyRun.σ1 w1 :=
    AcceptedB.snoc a1' e2 (show KH.OnExec wInit (.deposit 7 9 5 3 7 0 0) [.transferFrom 5 7 99 3] w1
      from m1)
  have a3 : AcceptedB ToyRun.X KH ([] ++ [Call.addSupportedToken 5] ++ [.deposit 7 9 5 3 7 0 0] ++
      [.transfer 9 26 39 46 9 0]) ToyRun.σ2 w1 :=
    AcceptedB.snoc a2 e3 (quiet w1 _)
  have a4 : AcceptedB ToyRun.X KH ([] ++ [Call.addSupportedToken 5] ++ [.deposit 7 9 5 3 7 0 0] ++
      [.transfer 9 26 39 46 9 0] ++ [.withdraw 39 5 3 8 96]) ToyRun.σ3 w3 :=
    AcceptedB.snoc a3 e4 m4
  exact a4

theorem sN : NoSelfWithdraw ToyRun.X ToyRun.hist := by
  intro nf tok amt rcpt root hm
  simp only [ToyRun.hist, List.mem_cons, reduceCtorEq, Call.withdraw.injEq, List.not_mem_nil, or_false,
      false_or] at hm
  obtain ⟨-, -, -, rfl, -⟩ := hm
  decide

/-- **Non-vacuity of `refineB_run`.** Every premise instantiated on the toy history with the
honest chain; the conclusion holds outright. -/
theorem refineB_run_toy : ∃ txs st, txs.map eraseSnap = txsOf ToyRun.ext ToyRun.hist ∧
    Run' (supOf Toy.E ToyRun.hist) txs st ∧
    RepP Toy.H Toy.E (supOf Toy.E ToyRun.hist) (ghostLeaves ToyRun.hist) ToyRun.σ3 st ∧
    (∀ t, KH.bal w3 (Toy.E.tok t) ToyRun.X.self = st.balance t) ∧
    (∀ t, KH.bal w3 (Toy.E.tok t) ToyRun.X.self = liveValue st t) :=
  refineB_run ToyRun.hG0 ToyRun.hRB ToyRun.hEnv ToyRun.hD ToyRun.hTP ToyRun.hWP ToyRun.hA ToyRun.hC ToyRun.hinj hinjT hRd
    (kh_startX ToyRun.X rfl) (kh_nodX ToyRun.X rfl) (kh_nocX ToyRun.X rfl) (kh_rbX ToyRun.X) accN ToyRun.hC1 sN
    ToyRun.hEx ToyRun.hTL ToyRun.hTH ToyRun.hcr

/-- The model state's balance of token 5 is the pool's external balance, 0, and the recipient
holds 3. -/
theorem toy_balance : ∃ st : St Toy.P, st.balance (5 : Nat) = 0 ∧ KH.bal w3 5 8 = 3 := by
  obtain ⟨_, st, _, _, _, hb, _⟩ := refineB_run_toy
  refine ⟨st, ?_, by decide⟩
  rw [← hb (5 : Nat)]
  decide

end LeanShieldedPool.Refine.BalanceToyRun

#print axioms LeanShieldedPool.Refine.BalanceToyRun.refineB_run_toy
#print axioms LeanShieldedPool.Refine.BalanceToyRun.toy_balance
