import Balance.Basic

/-!
# Token balances: worked instance and controls

* `worked_two_ops`: a two-operation history (deposit, a reverted withdraw, withdraw) on a toy pool
  with an honest token chain. Every premise holds; the pool's external balance equals the ledger
  (1), and the recipient holds 2.
* Control (a) `fake_token_breaks_eq`: a token whose `transferFrom` reports success and moves
  nothing. Every premise except `NoOutsideDebit` holds, and `NoOutsideDebit` fails; the equation
  fails (pool 0, ledger 3). `eq_needs_noOutsideDebit`: the equation does not follow without it.
* Control (b) `no_rollback_breaks_eq`: a reverted deposit whose token pull is not rolled back.
  Every premise except `TokenRollback` holds, and `TokenRollback` fails; the equation fails on a
  history with only a failed call (pool 3, ledger 0). `eq_needs_rollback`: the same, general.
  The pool balance rises here, so this counterexample does not break W9's lower bound.
* Positive control: `withdraw_balance` is unchanged; `refineB_w9` uses it through
  `withdraw_balanceP`.
* Self-withdrawal `self_withdraw_breaks_eq`: a source reading plus a toy accounting result. By
  source reading the contract's recipient check permits the pool as recipient
  (`ShieldedPool.sol:257` rejects only a zero recipient). On the toy pool `XT` with the honest
  chain, a withdrawal to the pool leaves the external pool balance above the calldata ledger, so
  the equation needs `NoSelfWithdraw`; the lower bound that W9 uses still holds. This is no
  executed production withdrawal and no theft: the tokens stay in the pool.
-/

namespace LeanShieldedPool.Refine.BalanceToy

open LeanShieldedPool LeanShieldedPool.Refine

/-- Toy pool at address 99: only the shape of the token calls is constrained. -/
def ExT : Storage → Call → List Ext → Storage → Prop
  | _, .deposit _ _ tok amt fund _ _, tr, _ => fund ≠ 99 ∧ tr = [.transferFrom tok fund 99 amt]
  | _, .withdraw _ tok amt rcpt _, tr, _ => tr = [.transfer tok rcpt amt]
  | _, _, tr, _ => tr = []

/-- Toy pool; a reverted call leaves storage unchanged. -/
def XT : Contract where
  Exec := ExT
  Fail := fun σ _ σ' => σ' = σ
  Verified := fun _ _ _ => True
  self := 99
  pinnedVerifier := 1
  genesis := Storage.genesis 1 2 3

theorem hTC : TokenCallFacts XT where
  deposit := fun {_ _ _ tok amt fund _ _ tr _} _ hx => by
    obtain ⟨-, h⟩ := hx
    rw [h]
    rfl
  deposit_funder := fun _ hx => by
    obtain ⟨h, -⟩ := hx
    exact h
  withdraw := fun {_ _ tok amt rcpt _ tr _} _ hx => by
    have h : tr = [.transfer tok rcpt amt] := hx
    rw [h]
    rfl
  transfer := fun {_ _ _ _ _ _ _ tr _} _ hx => by
    have h : tr = [] := hx
    rw [h]
    rfl
  owner := fun {_ c tr _} _ hx ho => by
    cases c <;> first
      | (have h : tr = [] := hx; rw [h]; rfl)
      | simp only [Call.isOwner, Bool.false_eq_true] at ho

/-- Initial balances: the funder 7 holds 10 of every token; the pool 99 holds nothing. -/
def wInit : Nat → Nat → Nat := fun _ a => if a = 7 then 10 else 0

/-- **Honest token chain.** Each successful pool call moves every balance by exactly its stated
deltas; reverts roll back; outside transactions leave the pool alone. -/
def KH : Chain where
  World := Nat → Nat → Nat
  bal := fun w => w
  w0 := wInit
  OnExec := fun w _ tr w' => ∀ t a, w' t a + debits 99 a t tr = w t a + credits a t tr
  OnFail := fun w _ w' => w' = w
  Outside := fun w w' => ∀ t, w' t 99 = w t 99

theorem kh_startX (X : Contract) (hs : X.self = 99) : PoolStartsEmpty X KH := fun t => by
  rw [hs]
  rfl

theorem kh_nodX (X : Contract) (hs : X.self = 99) : NoOutsideDebit X KH where
  call := fun {_ _ tr _ w w'} _ _ hw t => by
    have e := hw t 99
    rw [hs]
    show w t 99 + credits 99 t tr ≤ w' t 99 + debits 99 99 t tr
    omega
  outside := fun {w w'} ho t => by
    have e := ho t
    rw [hs]
    show w t 99 ≤ w' t 99
    omega

theorem kh_nocX (X : Contract) (hs : X.self = 99) : NoOutsideCredit X KH where
  call := fun {_ _ tr _ w w'} _ _ hw t => by
    have e := hw t 99
    rw [hs]
    show w' t 99 + debits 99 99 t tr ≤ w t 99 + credits 99 t tr
    omega
  outside := fun {w w'} ho t => by
    have e := ho t
    rw [hs]
    show w' t 99 ≤ w t 99
    omega

theorem kh_rbX (X : Contract) : TokenRollback X KH := fun {_ _ _ w w'} _ _ hw t => by
  have e : w' = w := hw
  rw [e]

theorem kh_start : PoolStartsEmpty XT KH := kh_startX XT rfl
theorem kh_nod : NoOutsideDebit XT KH := kh_nodX XT rfl
theorem kh_noc : NoOutsideCredit XT KH := kh_nocX XT rfl
theorem kh_rb : TokenRollback XT KH := kh_rbX XT

/-! ## Worked instance: a two-operation history -/

def g : Storage := Storage.genesis 1 2 3

/-- Deposit 3 of token 5 from funder 7. -/
def dep : Call := .deposit 0 9 5 3 7 0 0

/-- A withdrawal of 50 that reverts. -/
def badW : Call := .withdraw 9 5 50 8 9

/-- Withdraw 2 of token 5 to recipient 8. -/
def wd : Call := .withdraw 9 5 2 8 9

def hist2 : List Call := [dep, wd]

/-- After the deposit: funder 7 holds 7 of token 5, the pool 3. -/
def w1 : Nat → Nat → Nat := fun t a =>
  if t = 5 ∧ a = 7 then 7 else if t = 5 ∧ a = 99 then 3 else wInit t a

/-- After the withdrawal: the pool holds 1 of token 5, recipient 8 holds 2. -/
def w2 : Nat → Nat → Nat := fun t a =>
  if t = 5 ∧ a = 99 then 1 else if t = 5 ∧ a = 8 then 2 else w1 t a

theorem m1 : KH.OnExec wInit dep [.transferFrom 5 7 99 3] w1 := by
  intro t a
  by_cases ht : t = 5 <;> by_cases h7 : a = 7 <;> by_cases h99 : a = 99 <;> subst_vars <;>
    simp_all [w1, wInit, debits, credits, tokenCalls, Ext.isNested, Ext.debit, Ext.credit] <;>
    (try split_ifs) <;> omega

theorem m2 : KH.OnExec w1 wd [.transfer 5 8 2] w2 := by
  intro t a
  by_cases ht : t = 5 <;> by_cases h8 : a = 8 <;> by_cases h99 : a = 99 <;> subst_vars <;>
    simp_all [w2, w1, wInit, debits, credits, tokenCalls, Ext.isNested, Ext.debit, Ext.credit] <;>
    (try split_ifs) <;> omega

theorem acc2 : AcceptedB XT KH hist2 g w2 := by
  have e1 : XT.Exec g dep [.transferFrom 5 7 99 3] g := ⟨by decide, rfl⟩
  have e2 : XT.Exec g wd [.transfer 5 8 2] g := rfl
  have a1 : AcceptedB XT KH ([] ++ [dep]) g w1 := AcceptedB.snoc AcceptedB.nil e1 m1
  have a1' : AcceptedB XT KH ([] ++ [dep]) g w1 :=
    AcceptedB.fail a1 (show XT.Fail g badW g from rfl) (show KH.OnFail w1 badW w1 from rfl)
  have a2 : AcceptedB XT KH (([] ++ [dep]) ++ [wd]) g w2 := AcceptedB.snoc a1' e2 m2
  exact a2

theorem c1_2 : NoSetVerifier hist2 := by
  intro c hc v
  simp only [hist2, dep, wd, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> intro he <;> cases he

theorem s2 : NoSelfWithdraw XT hist2 := by
  intro nf tok amt rcpt root hm
  simp only [hist2, dep, wd, List.mem_cons, reduceCtorEq, Call.withdraw.injEq, List.not_mem_nil,
      or_false, false_or] at hm
  obtain ⟨-, -, -, rfl, -⟩ := hm
  decide

/-- **Worked instance.** Every premise of `bal_eq_ledger` holds on the two-operation history
(with a reverted call between): the pool's external balance equals the calldata ledger, which is
1, and the recipient received 2. -/
theorem worked_two_ops :
    KH.bal w2 5 XT.self = ledger hist2 5 ∧ ledger hist2 5 = 1 ∧ KH.bal w2 5 8 = 2 :=
  ⟨bal_eq_ledger hTC kh_start kh_nod kh_noc kh_rb acc2 c1_2 s2 5, by decide, by decide⟩

/-! ## Control (a): a token that reports success without moving funds -/

/-- The token's `transferFrom` reports success and moves nothing (the deposit's chain state is
unchanged); every other call moves exactly its stated deltas. -/
def KF : Chain where
  World := Nat → Nat → Nat
  bal := fun w => w
  w0 := wInit
  OnExec := fun w c tr w' => match c with
    | .deposit .. => w' = w
    | _ => ∀ t a, w' t a + debits 99 a t tr = w t a + credits a t tr
  OnFail := fun w _ w' => w' = w
  Outside := fun w w' => ∀ t, w' t 99 = w t 99

theorem kf_noc : NoOutsideCredit XT KF where
  call := fun {_ c tr _ w w'} hr hx hw t => by
    cases c
    case deposit s cm tok amt fund att pay =>
      have htc := hTC.deposit hr hx
      have e : w' = w := hw
      rw [deposit_debits_none htc (hTC.deposit_funder hr hx), e]
      omega
    all_goals
      have e := hw t 99
      show w' t 99 + debits 99 99 t tr ≤ w t 99 + credits 99 t tr
      omega
  outside := fun {w w'} ho t => by
    have e := ho t
    show w' t 99 ≤ w t 99
    omega

theorem kf_rb : TokenRollback XT KF := fun {_ _ _ w w'} _ _ hw t => by
  have e : w' = w := hw
  rw [e]

theorem reach_g : Reach XT g := ⟨[], Accepted.nil, fun _ h => absurd h List.not_mem_nil⟩

/-- **Control (a).** The fake token satisfies every premise but `NoOutsideDebit`, violates that
one, and breaks the equation and the lower bound on a one-deposit history. -/
theorem fake_token_breaks_eq :
    TokenCallFacts XT ∧ PoolStartsEmpty XT KF ∧ NoOutsideCredit XT KF ∧ TokenRollback XT KF ∧
      NoSetVerifier [dep] ∧ NoSelfWithdraw XT [dep] ∧
      AcceptedB XT KF [dep] g wInit ∧ ¬ NoOutsideDebit XT KF ∧
      KF.bal wInit 5 XT.self ≠ ledger [dep] 5 ∧ ¬ ledger [dep] 5 ≤ KF.bal wInit 5 XT.self := by
  have e1 : XT.Exec g dep [.transferFrom 5 7 99 3] g := ⟨by decide, rfl⟩
  refine ⟨hTC, fun _ => rfl, kf_noc, kf_rb, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · intro c hc v
    rw [List.mem_singleton] at hc
    subst hc
    intro he
    simp only [dep, reduceCtorEq] at he
  · intro nf tok amt rcpt root hm
    rw [List.mem_singleton] at hm
    simp only [dep, reduceCtorEq] at hm
  · have a : AcceptedB XT KF ([] ++ [dep]) g wInit := AcceptedB.snoc (K := KF) AcceptedB.nil e1
      (show KF.OnExec wInit dep [.transferFrom 5 7 99 3] wInit from rfl)
    exact a
  · intro hND
    have := hND.call reach_g e1 (w := wInit) (w' := wInit) rfl 5
    exact absurd this (by decide)

/-- Without `NoOutsideDebit` the equation does not follow from the other premises. -/
theorem eq_needs_noOutsideDebit : ¬ ∀ (X : Contract) (K : Chain) (h : List Call) (σ : Storage)
    (w : K.World), TokenCallFacts X → PoolStartsEmpty X K → NoOutsideCredit X K →
    TokenRollback X K → AcceptedB X K h σ w → NoSetVerifier h → NoSelfWithdraw X h →
    ∀ t, K.bal w t X.self = ledger h t := by
  intro hall
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9, -⟩ := fake_token_breaks_eq
  exact h9 (hall XT KF [dep] g wInit h1 h2 h3 h4 h7 h5 h6 5)

/-! ## Control (b): a failed call that is not rolled back -/

/-- The honest chain, except that a reverted call may leave any chain state. -/
def KR : Chain where
  World := Nat → Nat → Nat
  bal := fun w => w
  w0 := wInit
  OnExec := fun w _ tr w' => ∀ t a, w' t a + debits 99 a t tr = w t a + credits a t tr
  OnFail := fun _ _ _ => True
  Outside := fun w w' => ∀ t, w' t 99 = w t 99

theorem kr_nod : NoOutsideDebit XT KR where
  call := fun {_ _ tr _ w w'} _ _ hw t => by
    have e := hw t 99
    show w t 99 + credits 99 t tr ≤ w' t 99 + debits 99 99 t tr
    omega
  outside := fun {w w'} ho t => by
    have e := ho t
    show w t 99 ≤ w' t 99
    omega

theorem kr_noc : NoOutsideCredit XT KR where
  call := fun {_ _ tr _ w w'} _ _ hw t => by
    have e := hw t 99
    show w' t 99 + debits 99 99 t tr ≤ w t 99 + credits 99 t tr
    omega
  outside := fun {w w'} ho t => by
    have e := ho t
    show w' t 99 ≤ w t 99
    omega

/-- **Control (b).** A deposit reverts after its token pull; the pull is not rolled back. Every
premise but `TokenRollback` holds, that one fails, and the equation fails on the history that
holds only the failed call. The pool balance rises (3 above a ledger of 0), so W9's lower bound
still holds on this history. -/
theorem no_rollback_breaks_eq :
    TokenCallFacts XT ∧ PoolStartsEmpty XT KR ∧ NoOutsideDebit XT KR ∧ NoOutsideCredit XT KR ∧
      NoSetVerifier [] ∧ NoSelfWithdraw XT [] ∧
      AcceptedB XT KR [] g w1 ∧ ¬ TokenRollback XT KR ∧
      KR.bal w1 5 XT.self ≠ ledger [] 5 ∧ ¬ KR.bal w1 5 XT.self ≤ ledger [] 5 := by
  have a : AcceptedB XT KR [] g w1 := AcceptedB.fail (c := dep) AcceptedB.nil rfl trivial
  refine ⟨hTC, fun _ => rfl, kr_nod, kr_noc, fun _ h => absurd h List.not_mem_nil,
    fun _ _ _ _ _ h => absurd h List.not_mem_nil, a, ?_, by decide, by decide⟩
  intro hRB
  have := @hRB g dep g wInit w1 reach_g rfl trivial 5
  exact absurd this (by decide)

/-- Without `TokenRollback` the equation does not follow from the other premises. -/
theorem eq_needs_rollback : ¬ ∀ (X : Contract) (K : Chain) (h : List Call) (σ : Storage)
    (w : K.World), TokenCallFacts X → PoolStartsEmpty X K → NoOutsideDebit X K →
    NoOutsideCredit X K → AcceptedB X K h σ w → NoSetVerifier h → NoSelfWithdraw X h →
    ∀ t, K.bal w t X.self = ledger h t := by
  intro hall
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9, -⟩ := no_rollback_breaks_eq
  exact h9 (hall XT KR [] g w1 h1 h2 h3 h4 h7 h5 h6 5)

/-! ## Self-withdrawal: a source reading and a toy accounting result -/

/-- Withdraw 3 of token 5 to the pool itself. By source reading the contract's recipient check
permits this (`ShieldedPool.sol:257` rejects only a zero recipient). -/
def wdSelf : Call := .withdraw 9 5 3 99 9

theorem mSelf : KH.OnExec w1 wdSelf [.transfer 5 99 3] w1 := by
  intro t a
  simp only [debits, tokenCalls, Ext.isNested, Bool.not_false, List.filter_cons_of_pos,
      List.filter_nil, List.map_cons, Ext.debit, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, credits, Ext.credit]

/-- **Self-withdrawal (toy).** On the toy pool `XT` with the honest chain and every premise but
`NoSelfWithdraw`, the pool keeps the 3 it paid to itself while the calldata ledger drops to 0: the
equation fails, and the lower bound that W9 uses still holds. A toy accounting result, not an
executed production withdrawal. -/
theorem self_withdraw_breaks_eq :
    AcceptedB XT KH [dep, wdSelf] g w1 ∧ NoSetVerifier [dep, wdSelf] ∧
      ¬ NoSelfWithdraw XT [dep, wdSelf] ∧
      KH.bal w1 5 XT.self ≠ ledger [dep, wdSelf] 5 ∧
      ledger [dep, wdSelf] 5 ≤ KH.bal w1 5 XT.self := by
  have e1 : XT.Exec g dep [.transferFrom 5 7 99 3] g := ⟨by decide, rfl⟩
  have e2 : XT.Exec g wdSelf [.transfer 5 99 3] g := rfl
  have a1 : AcceptedB XT KH ([] ++ [dep]) g w1 := AcceptedB.snoc AcceptedB.nil e1 m1
  have a2 : AcceptedB XT KH (([] ++ [dep]) ++ [wdSelf]) g w1 := AcceptedB.snoc a1 e2 mSelf
  have hC1 : NoSetVerifier [dep, wdSelf] := by
    intro c hc v
    simp only [dep, wdSelf, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> intro he <;> cases he
  refine ⟨a2, hC1, fun hS => ?_, by decide,
    ledger_le_bal hTC kh_nod kh_rb a2 hC1 5⟩
  exact hS 9 5 3 99 9 (List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl

end LeanShieldedPool.Refine.BalanceToy

/-! Axiom census. -/
#print axioms LeanShieldedPool.Refine.AcceptedB.accepted
#print axioms LeanShieldedPool.Refine.TokenCallFacts.of_posts
#print axioms LeanShieldedPool.Refine.deposit_credits_pool
#print axioms LeanShieldedPool.Refine.withdraw_debits_pool
#print axioms LeanShieldedPool.Refine.withdraw_credits_recipient
#print axioms LeanShieldedPool.Refine.ledger_le_bal
#print axioms LeanShieldedPool.Refine.bal_le_ledger
#print axioms LeanShieldedPool.Refine.bal_eq_ledger
#print axioms LeanShieldedPool.Refine.Run'.balance_eq
#print axioms LeanShieldedPool.Refine.modelBal_txsOf
#print axioms LeanShieldedPool.Refine.refineB_run
#print axioms LeanShieldedPool.Refine.refineB_w9
#print axioms LeanShieldedPool.Refine.BalanceToy.worked_two_ops
#print axioms LeanShieldedPool.Refine.BalanceToy.fake_token_breaks_eq
#print axioms LeanShieldedPool.Refine.BalanceToy.eq_needs_noOutsideDebit
#print axioms LeanShieldedPool.Refine.BalanceToy.no_rollback_breaks_eq
#print axioms LeanShieldedPool.Refine.BalanceToy.eq_needs_rollback
#print axioms LeanShieldedPool.Refine.BalanceToy.self_withdraw_breaks_eq
#print axioms LeanShieldedPool.Refine.withdraw_balance
#print axioms LeanShieldedPool.Refine.withdraw_balanceP
