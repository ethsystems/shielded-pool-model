import Refinement.ProvenanceRefine

/-!
# Token balances from named A10 deltas

`Storage` holds no token balances, and `refineP_valueConservation` concludes an identity about
the model's accounting fields only. This file adds the external token balances as a parameter
(`Chain.bal w tok a`: `IERC20(tok).balanceOf(a)` in chain state `w`), computes the stated delta
of each token call from its arguments (`Ext.credit`, `Ext.debit`: accounting definitions, not
token behavior), and proves by induction over accepted histories, reverted calls and outside
transactions included, that the pool's external balance equals the calldata ledger (`ledger`)
and hence the model's `st.balance`.

Premises, by name:
* `TokenCallFacts`: the token calls each pool call makes. Deposit, withdraw and transfer come from
  the existing posts (D6/X2, W10, X1); `deposit_funder` and `owner` are source readings
  (`PoolCallReadings`).
* `PoolStartsEmpty`: the pool holds no token at genesis.
* `NoOutsideDebit`: the pool's net balance change across each successful pool call is at least
  what its token calls state, and outside transactions never decrease it (no fee, no negative
  rebase, no outside debit).
* `NoOutsideCredit`: the converse bound (no positive rebase; also no donation to the pool).
* `TokenRollback`: a reverted pool call leaves the pool's token balances unchanged.
* `NoSelfWithdraw`: no withdrawal of the history names the pool as recipient (the contract does
  not reject it, `ShieldedPool.sol` withdraw checks only `recipient != 0`).

The stated deltas: a deposit's token call states a credit to the pool (`deposit_credits_pool`);
a withdrawal's states a debit of the pool (`withdraw_debits_pool`) and a credit to its recipient
(`withdraw_credits_recipient`). The balance premises constrain only the pool's address, and only
its aggregate net change per call, so no recipient balance and no single transfer is
established. They quantify over every token word and every matching chain transition, not only
supported tokens or jointly reachable chain states: their scope is broader than A10's.

`ledger_le_bal` needs only `NoOutsideDebit` and `TokenRollback`; `bal_eq_ledger` needs all of the
above. None is discharged here: no deployed token is shown to obey A10, and no contract premise
is checked against real ERC-20 state.

`refineB_run` and `refineB_w9` use the global tree premises of `refineP_run` (`TreeLink`, `TreeHyp`);
`Balance/PathLocal.lean` restates them on the path-local premises.
-/

namespace LeanShieldedPool.Refine

variable {P : PrimSpec}

/-! ## The external ledger -/

/-- The chain outside the pool's storage. `bal w tok a` is `IERC20(tok).balanceOf(a)` in chain
state `w`. The step relations are uninterpreted, like `Contract.Exec`; the premises below
constrain the pool's balances across them. -/
structure Chain where
  World : Type
  /-- The external balance function. -/
  bal : World → Nat → Nat → Nat
  /-- The chain state right after the pool's constructor. -/
  w0 : World
  /-- `OnExec w c tr w'`: across the successful top-level pool call `c` with external trace
  `tr`, the chain state moves from `w` to `w'`. -/
  OnExec : World → Call → List Ext → World → Prop
  /-- `OnFail w c w'`: the chain state after the reverted top-level pool call `c`. -/
  OnFail : World → Call → World → Prop
  /-- `Outside w w'`: a transaction that does not call the pool. -/
  Outside : World → World → Prop

/-- Accepted histories with the chain state beside the storage. A successful call moves both;
a reverted call leaves the history unchanged; an outside transaction moves only the chain. -/
inductive AcceptedB (X : Contract) (K : Chain) : List Call → Storage → K.World → Prop where
  | nil : AcceptedB X K [] X.genesis K.w0
  | snoc {h : List Call} {σ σ' : Storage} {w w' : K.World} {c : Call} {tr : List Ext} :
      AcceptedB X K h σ w → X.Exec σ c tr σ' → K.OnExec w c tr w' →
        AcceptedB X K (h ++ [c]) σ' w'
  | fail {h : List Call} {σ σ' : Storage} {w w' : K.World} {c : Call} :
      AcceptedB X K h σ w → X.Fail σ c σ' → K.OnFail w c w' → AcceptedB X K h σ' w'
  | outside {h : List Call} {σ : Storage} {w w' : K.World} :
      AcceptedB X K h σ w → K.Outside w w' → AcceptedB X K h σ w'

/-- Forgetting the chain state gives an `Accepted` history. -/
theorem AcceptedB.accepted {X : Contract} {K : Chain} {h : List Call} {σ : Storage}
    {w : K.World} (hb : AcceptedB X K h σ w) : Accepted X h σ := by
  induction hb with
  | nil => exact Accepted.nil
  | snoc _ hx _ ih => exact Accepted.snoc ih hx
  | fail _ hf _ ih => exact Accepted.fail ih hf
  | outside _ _ ih => exact ih

/-! ## The named A10 deltas -/

/-- **Stated credit of one token call** to holder `a` in token `t`: the amount `amt` that a
`transferFrom(src, dst, amt)` or `transfer(dst, amt)` on token `t` names for `dst`. An accounting
definition over the call's arguments; it constrains no balance. -/
def Ext.credit (a t : Nat) : Ext → Nat
  | .transferFrom tok _ dst amt => if tok = t ∧ dst = a then amt else 0
  | .transfer tok dst amt => if tok = t ∧ dst = a then amt else 0
  | .nested _ => 0

/-- **Stated debit of one token call** from holder `a` in token `t`: `transferFrom` names `src`
and `transfer` names its caller, the pool `self`, for `amt`. An accounting definition over the
call's arguments; it constrains no balance. -/
def Ext.debit (self a t : Nat) : Ext → Nat
  | .transferFrom tok src _ amt => if tok = t ∧ src = a then amt else 0
  | .transfer tok _ amt => if tok = t ∧ self = a then amt else 0
  | .nested _ => 0

/-- The credits the token calls of a trace state for holder `a` in token `t`. -/
def credits (a t : Nat) (tr : List Ext) : Nat := ((tokenCalls tr).map (Ext.credit a t)).sum

/-- The debits the token calls of a trace state for holder `a` in token `t`. -/
def debits (self a t : Nat) (tr : List Ext) : Nat := ((tokenCalls tr).map (Ext.debit self a t)).sum

theorem credits_nil {tr : List Ext} (htc : tokenCalls tr = []) (a t : Nat) :
    credits a t tr = 0 := by
  simp only [credits, htc, List.map_nil, List.sum_nil]

theorem debits_nil {tr : List Ext} (htc : tokenCalls tr = []) (self a t : Nat) :
    debits self a t tr = 0 := by
  simp only [debits, htc, List.map_nil, List.sum_nil]

/-- **Deposit credits the pool** (stated): the deposit's token call states a credit of `amt` of
`tok` to the pool. -/
theorem deposit_credits_pool {tr : List Ext} {tok fund self amt : Nat}
    (htc : tokenCalls tr = [.transferFrom tok fund self amt]) (t : Nat) :
    credits self t tr = if tok = t then amt else 0 := by
  simp only [credits, htc, List.map_cons, Ext.credit, and_true, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]

/-- The deposit's token call debits the pool nothing when the funder is not the pool. -/
theorem deposit_debits_none {tr : List Ext} {tok fund self amt : Nat}
    (htc : tokenCalls tr = [.transferFrom tok fund self amt]) (hf : fund ≠ self) (t : Nat) :
    debits self self t tr = 0 := by
  simp only [debits, htc, List.map_cons, Ext.debit, hf, and_false, ↓reduceIte, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]

/-- **Withdrawal debits the pool** (stated): the withdrawal's token call states a debit of `amt`
of `tok` from the pool. -/
theorem withdraw_debits_pool {tr : List Ext} {tok rcpt self amt : Nat}
    (htc : tokenCalls tr = [.transfer tok rcpt amt]) (t : Nat) :
    debits self self t tr = if tok = t then amt else 0 := by
  simp only [debits, htc, List.map_cons, Ext.debit, and_true, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]

/-- **Withdrawal names the recipient's credit** (stated): the withdrawal's token call states a
credit of `amt` of `tok` to the recipient. Accounting only: no `Chain.bal` occurs here and no
premise constrains the recipient's balance, so the recipient's actual credit stays A10 (W10). -/
theorem withdraw_credits_recipient {tr : List Ext} {tok rcpt amt : Nat}
    (htc : tokenCalls tr = [.transfer tok rcpt amt]) (t : Nat) :
    credits rcpt t tr = if tok = t then amt else 0 := by
  simp only [credits, htc, List.map_cons, Ext.credit, and_true, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]

/-- The withdrawal credits the pool nothing when the recipient is not the pool. -/
theorem withdraw_credits_none {tr : List Ext} {tok rcpt self amt : Nat}
    (htc : tokenCalls tr = [.transfer tok rcpt amt]) (hr : rcpt ≠ self) (t : Nat) :
    credits self t tr = 0 := by
  simp only [credits, htc, List.map_cons, Ext.credit, hr, and_false, ↓reduceIte, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]

/-! ## Premises -/

/-- Pool calls that move tokens. -/
def Call.pays : Call → Bool
  | .deposit .. => true
  | .withdraw .. => true
  | _ => false

/-- **The pool's token calls, per call kind**, on reachable states. -/
structure TokenCallFacts (X : Contract) : Prop where
  /-- D6 and X2 (`DepositPost.token_calls`). -/
  deposit : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' →
    tokenCalls tr = [.transferFrom tok fund X.self amt]
  /-- The funding address is not the pool (`PoolCallReadings.deposit_funder`). -/
  deposit_funder : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' → fund ≠ X.self
  /-- W10 (`WithdrawPost.token_calls`). -/
  withdraw : ∀ {σ nf tok amt rcpt root tr σ'}, Reach X σ →
    X.Exec σ (.withdraw nf tok amt rcpt root) tr σ' → tokenCalls tr = [.transfer tok rcpt amt]
  /-- X1, transfer calls no token (`TransferPost.no_effects`). -/
  transfer : ∀ {σ n0 n1 c0 c1 root pay tr σ'}, Reach X σ →
    X.Exec σ (.transfer n0 n1 c0 c1 root pay) tr σ' → tokenCalls tr = []
  /-- Owner calls call no token (`PoolCallReadings.owner_quiet`). -/
  owner : ∀ {σ c tr σ'}, Reach X σ → X.Exec σ c tr σ' → c.isOwner = true → tokenCalls tr = []

/-- **Two source readings** that `TokenCallFacts` adds to the existing posts. -/
structure PoolCallReadings (X : Contract) : Prop where
  /-- `deposit` reverts unless `msg.sender == fundingAddress` (`ShieldedPool.sol:149`), and the
  pool never calls its own `deposit`. -/
  deposit_funder : ∀ {σ s c tok amt fund att pay tr σ'}, Reach X σ →
    X.Exec σ (.deposit s c tok amt fund att pay) tr σ' → fund ≠ X.self
  /-- The owner functions write one slot and call no token (`ShieldedPool.sol:293-340`). -/
  owner_quiet : ∀ {σ c tr σ'}, Reach X σ → X.Exec σ c tr σ' → c.isOwner = true →
    tokenCalls tr = []

/-- The token-call facts follow from the existing posts and the two readings. -/
theorem TokenCallFacts.of_posts {H : Nat → Nat → Nat} {X : Contract} (hD : DepositPost H X)
    (hTP : TransferPost H X) (hWP : WithdrawPost X) (hRd : PoolCallReadings X) :
    TokenCallFacts X where
  deposit := hD.token_calls
  deposit_funder := hRd.deposit_funder
  withdraw := hWP.token_calls
  transfer := fun hr hx => by rw [hTP.no_effects hr hx]; rfl
  owner := hRd.owner_quiet

/-- A call that pays nothing makes no token call. -/
theorem TokenCallFacts.quiet {X : Contract} (hTC : TokenCallFacts X) {σ σ' : Storage} {c : Call}
    {tr : List Ext} (hr : Reach X σ) (hx : X.Exec σ c tr σ') (hp : c.pays = false) :
    tokenCalls tr = [] := by
  cases c with
  | deposit => simp only [Call.pays, Bool.true_eq_false] at hp
  | withdraw => simp only [Call.pays, Bool.true_eq_false] at hp
  | transfer => exact hTC.transfer hr hx
  | addSupportedToken => exact hTC.owner hr hx rfl
  | removeSupportedToken => exact hTC.owner hr hx rfl
  | setAttestationRegistry => exact hTC.owner hr hx rfl
  | transferOwnership => exact hTC.owner hr hx rfl
  | setVerifier => exact hTC.owner hr hx rfl

/-- **From zero pool balance.** -/
def PoolStartsEmpty (X : Contract) (K : Chain) : Prop := ∀ t, K.bal K.w0 t X.self = 0

/-- **No outside debit.** Across a successful pool call from a reachable state, the pool's
balance in each token rises at least by the stated credits and falls at most by the stated
debits of the call's token calls: no fee, negative rebase, hook debit, or success reported
without the credit. No transaction outside the pool debits the pool. The bound is on the pool's
aggregate net change per call, not on each transfer, and it quantifies over every token word and
every matching chain transition, so its scope is broader than A10's supported tokens. Board
row A10 (TOKENS). -/
structure NoOutsideDebit (X : Contract) (K : Chain) : Prop where
  call : ∀ {σ c tr σ' w w'}, Reach X σ → X.Exec σ c tr σ' → K.OnExec w c tr w' → ∀ t,
    K.bal w t X.self + credits X.self t tr ≤ K.bal w' t X.self + debits X.self X.self t tr
  outside : ∀ {w w'}, K.Outside w w' → ∀ t, K.bal w t X.self ≤ K.bal w' t X.self

/-- **No outside credit.** The converse bound: the pool gains no more than the stated
credits and loses at least the stated debits; no transaction outside the pool credits it (no
positive rebase, no donation). Same scope as `NoOutsideDebit`. Board row A10 (TOKENS)
plus no donation. -/
structure NoOutsideCredit (X : Contract) (K : Chain) : Prop where
  call : ∀ {σ c tr σ' w w'}, Reach X σ → X.Exec σ c tr σ' → K.OnExec w c tr w' → ∀ t,
    K.bal w' t X.self + debits X.self X.self t tr ≤ K.bal w t X.self + credits X.self t tr
  outside : ∀ {w w'}, K.Outside w w' → ∀ t, K.bal w' t X.self ≤ K.bal w t X.self

/-- **Failed calls roll back** the pool's token balances. Board rows A10 ("revert
failed transfers"), A11 and REF. -/
def TokenRollback (X : Contract) (K : Chain) : Prop :=
  ∀ {σ c σ' w w'}, Reach X σ → X.Fail σ c σ' → K.OnFail w c w' → ∀ t,
    K.bal w' t X.self = K.bal w t X.self

/-- No withdrawal of the history names the pool as recipient. By source reading the contract's
recipient check permits the pool (`ShieldedPool.sol:257` rejects only a zero recipient). -/
def NoSelfWithdraw (X : Contract) (h : List Call) : Prop :=
  ∀ nf tok amt rcpt root, Call.withdraw nf tok amt rcpt root ∈ h → rcpt ≠ X.self

/-! ## The calldata ledger and the induction -/

/-- The pool's balance change for one call, from its calldata: a deposit adds `amt` of `tok`,
a withdrawal subtracts it (truncated, like the model's `drop`). -/
def Call.ledgerStep (t b : Nat) : Call → Nat
  | .deposit _ _ tok amt _ _ _ => if tok = t then b + amt else b
  | .withdraw _ tok amt _ _ => if tok = t then b - amt else b
  | .transfer .. => b
  | .addSupportedToken _ => b
  | .removeSupportedToken _ => b
  | .setAttestationRegistry _ => b
  | .transferOwnership _ => b
  | .setVerifier _ => b

/-- The calldata ledger of a history: the pool's balance of token `t` the history implies. -/
def ledger (h : List Call) (t : Nat) : Nat := h.foldl (fun b c => c.ledgerStep t b) 0

theorem ledger_snoc (h : List Call) (c : Call) (t : Nat) :
    ledger (h ++ [c]) t = c.ledgerStep t (ledger h t) := by
  simp only [ledger, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem Call.ledgerStep_quiet {c : Call} (hp : c.pays = false) (t b : Nat) :
    c.ledgerStep t b = b := by
  cases c <;> first | rfl | simp only [Call.pays, Bool.true_eq_false] at hp

/-- **Induction, lower bound.** Under no outside debit and rollback, the pool's external balance
covers the calldata ledger in every accepted history. Zero start is not needed. -/
theorem ledger_le_bal {X : Contract} {K : Chain} (hTC : TokenCallFacts X)
    (hND : NoOutsideDebit X K) (hRB : TokenRollback X K)
    {h : List Call} {σ : Storage} {w : K.World} (hb : AcceptedB X K h σ w) :
    NoSetVerifier h → ∀ t, ledger h t ≤ K.bal w t X.self := by
  induction hb with
  | nil => intro _ t; exact Nat.zero_le _
  | @snoc h0 σ0 σ1 w0 w1 c tr hb0 hx hw ih =>
    intro hC1 t
    have hC0 : NoSetVerifier h0 := fun c' hc' => hC1 c' (List.mem_append_left _ hc')
    have hreach : Reach X σ0 := ⟨h0, hb0.accepted, hC0⟩
    have ih' := ih hC0 t
    have hst := hND.call hreach hx hw t
    rw [ledger_snoc]
    cases c
    case deposit s cm tok amt fund att pay =>
      have htc := hTC.deposit hreach hx
      rw [deposit_credits_pool htc, deposit_debits_none htc (hTC.deposit_funder hreach hx)] at hst
      show (if tok = t then ledger h0 t + amt else ledger h0 t) ≤ _
      split_ifs at hst ⊢ <;> omega
    case withdraw nf tok amt rcpt root =>
      have htc := hTC.withdraw hreach hx
      rw [withdraw_debits_pool htc] at hst
      show (if tok = t then ledger h0 t - amt else ledger h0 t) ≤ _
      split_ifs at hst ⊢ <;> omega
    all_goals
      have htc := hTC.quiet hreach hx rfl
      rw [credits_nil htc, debits_nil htc] at hst
      show ledger h0 t ≤ K.bal w1 t X.self
      omega
  | @fail h0 σ0 σ1 w0 w1 c hb0 hf hw ih =>
    intro hC1 t
    have hreach : Reach X σ0 := ⟨h0, hb0.accepted, hC1⟩
    rw [hRB hreach hf hw t]
    exact ih hC1 t
  | @outside h0 σ0 w0 w1 hb0 ho ih =>
    intro hC1 t
    exact Nat.le_trans (ih hC1 t) (hND.outside ho t)

/-- **Induction, upper bound.** From zero pool balance, under no outside credit, rollback and no
self-withdrawal, the calldata ledger covers the pool's external balance. -/
theorem bal_le_ledger {X : Contract} {K : Chain} (hTC : TokenCallFacts X)
    (hz : PoolStartsEmpty X K) (hNC : NoOutsideCredit X K) (hRB : TokenRollback X K)
    {h : List Call} {σ : Storage} {w : K.World} (hb : AcceptedB X K h σ w) :
    NoSetVerifier h → NoSelfWithdraw X h → ∀ t, K.bal w t X.self ≤ ledger h t := by
  induction hb with
  | nil => intro _ _ t; rw [hz t]; exact Nat.zero_le _
  | @snoc h0 σ0 σ1 w0 w1 c tr hb0 hx hw ih =>
    intro hC1 hS t
    have hC0 : NoSetVerifier h0 := fun c' hc' => hC1 c' (List.mem_append_left _ hc')
    have hS0 : NoSelfWithdraw X h0 := fun nf tok amt rcpt root hm =>
      hS nf tok amt rcpt root (List.mem_append_left _ hm)
    have hreach : Reach X σ0 := ⟨h0, hb0.accepted, hC0⟩
    have ih' := ih hC0 hS0 t
    have hst := hNC.call hreach hx hw t
    rw [ledger_snoc]
    cases c
    case deposit s cm tok amt fund att pay =>
      have htc := hTC.deposit hreach hx
      rw [deposit_credits_pool htc, deposit_debits_none htc (hTC.deposit_funder hreach hx)] at hst
      show _ ≤ (if tok = t then ledger h0 t + amt else ledger h0 t)
      split_ifs at hst ⊢ <;> omega
    case withdraw nf tok amt rcpt root =>
      have htc := hTC.withdraw hreach hx
      have hr : rcpt ≠ X.self :=
        hS nf tok amt rcpt root (List.mem_append_right _ (List.mem_singleton_self _))
      rw [withdraw_debits_pool htc, withdraw_credits_none htc hr] at hst
      show _ ≤ (if tok = t then ledger h0 t - amt else ledger h0 t)
      split_ifs at hst ⊢ <;> omega
    all_goals
      have htc := hTC.quiet hreach hx rfl
      rw [credits_nil htc, debits_nil htc] at hst
      show K.bal w1 t X.self ≤ ledger h0 t
      omega
  | @fail h0 σ0 σ1 w0 w1 c hb0 hf hw ih =>
    intro hC1 hS t
    have hreach : Reach X σ0 := ⟨h0, hb0.accepted, hC1⟩
    rw [hRB hreach hf hw t]
    exact ih hC1 hS t
  | @outside h0 σ0 w0 w1 hb0 ho ih =>
    intro hC1 hS t
    exact Nat.le_trans (hNC.outside ho t) (ih hC1 hS t)

/-- **The accounting equation (ledger form).** From zero pool balance, under the named deltas,
rollback and no self-withdrawal, the pool's external balance equals the calldata ledger in every
accepted history, reverted calls and outside transactions included. -/
theorem bal_eq_ledger {X : Contract} {K : Chain} (hTC : TokenCallFacts X)
    (hz : PoolStartsEmpty X K) (hND : NoOutsideDebit X K) (hNC : NoOutsideCredit X K)
    (hRB : TokenRollback X K) {h : List Call} {σ : Storage} {w : K.World}
    (hb : AcceptedB X K h σ w) (hC1 : NoSetVerifier h) (hS : NoSelfWithdraw X h) (t : Nat) :
    K.bal w t X.self = ledger h t :=
  Nat.le_antisymm (bal_le_ledger hTC hz hNC hRB hb hC1 hS t) (ledger_le_bal hTC hND hRB hb hC1 t)

/-! ## The model's balance field is the calldata ledger -/

open Classical in
/-- The model's balance change for one operation (`DepositData.post`, `WithdrawData.post`). -/
noncomputable def _root_.LeanShieldedPool.Tx.balStep (t : P.Token) (b : Nat) : Tx P → Nat
  | .deposit d => if t = d.note.token then b + d.note.amount else b
  | .transfer _ => b
  | .withdraw d => if t = d.note.token then b - d.note.amount else b

/-- The model balance a list of operations implies. -/
noncomputable def modelBal (txs : List (Tx P)) (t : P.Token) : Nat :=
  txs.foldl (fun b tx => tx.balStep t b) 0

theorem modelBal_append (l₁ l₂ : List (Tx P)) (t : P.Token) :
    modelBal (l₁ ++ l₂) t = l₂.foldl (fun b tx => tx.balStep t b) (modelBal l₁ t) := by
  simp only [modelBal, List.foldl_append]

/-- In every `Step'` run the balance field is `modelBal` of the run. -/
theorem Run'.balance_eq {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (hr : Run' sup txs st) (t : P.Token) : st.balance t = modelBal txs t := by
  induction hr with
  | empty => rfl
  | @step txs st st' tx _ hs ih =>
    rw [modelBal_append, ← ih]
    cases hs with
    | deposit _ => rfl
    | transfer _ => rfl
    | withdraw _ => rfl

theorem balStep_eraseSnap (t : P.Token) (b : Nat) (tx : Tx P) :
    (eraseSnap tx).balStep t b = tx.balStep t b := by
  cases tx <;> rfl

theorem modelBal_eraseSnap (txs : List (Tx P)) (t : P.Token) :
    modelBal (txs.map eraseSnap) t = modelBal txs t := by
  simp only [modelBal, List.foldl_map, balStep_eraseSnap]

open Classical in
/-- **The model balance of the extracted operations is the calldata ledger**, through D4 and W5
(the public token and amount are the witness note's) and an injective token encoding. -/
theorem modelBal_txsOf {C : Circuits P} {E : Enc P} {Incl : Nat → Nat → Prop}
    {ext : Extractor P} (hC : CircuitFacts E C Incl) (hinjT : Function.Injective E.tok)
    {h : List Call} (hEx : ExtractedWitnesses C ext h) (t : P.Token) :
    modelBal (txsOf ext h) t = ledger h (E.tok t) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h c ih =>
    have hEx0 : ExtractedWitnesses C ext h := fun c' hc' => hEx c' (List.mem_append_left _ hc')
    have hc : c.extractOK C ext := hEx c (List.mem_append_right _ (List.mem_singleton_self _))
    rw [txsOf_snoc, modelBal_append, ledger_snoc, ← ih hEx0]
    generalize modelBal (txsOf ext h) t = L
    cases c with
    | deposit s cm tok amt fund att pay =>
      have hd : C.deposit [cm, tok, amt, fund, att, pay] (ext.deposit [cm, tok, amt, fund, att, pay]) :=
        hc
      obtain ⟨-, htok, hamt⟩ := hC.d_commitment _ _ hd
      have htok' : tok = E.tok (ext.deposit [cm, tok, amt, fund, att, pay]).note.token := htok
      have hamt' : amt = (ext.deposit [cm, tok, amt, fund, att, pay]).note.amount := hamt
      show (if t = (ext.deposit [cm, tok, amt, fund, att, pay]).note.token
        then L + (ext.deposit [cm, tok, amt, fund, att, pay]).note.amount else L) =
        (if tok = E.tok t then L + amt else L)
      by_cases ht : t = (ext.deposit [cm, tok, amt, fund, att, pay]).note.token
      · rw [if_pos ht, if_pos (by rw [htok', ht]), ← hamt']
      · rw [if_neg ht, if_neg (fun he => ht (hinjT (he.symm.trans htok')))]
    | withdraw nf tok amt rcpt root =>
      have hd : C.withdraw [nf, tok, amt, rcpt, root] (ext.withdraw [nf, tok, amt, rcpt, root]) :=
        hc
      obtain ⟨htok, hamt⟩ := hC.w_public _ _ hd
      have htok' : tok = E.tok (ext.withdraw [nf, tok, amt, rcpt, root]).note.token := htok
      have hamt' : amt = (ext.withdraw [nf, tok, amt, rcpt, root]).note.amount := hamt
      show (if t = (ext.withdraw [nf, tok, amt, rcpt, root]).note.token
        then L - (ext.withdraw [nf, tok, amt, rcpt, root]).note.amount else L) =
        (if tok = E.tok t then L - amt else L)
      by_cases ht : t = (ext.withdraw [nf, tok, amt, rcpt, root]).note.token
      · rw [if_pos ht, if_pos (by rw [htok', ht]), ← hamt']
      · rw [if_neg ht, if_neg (fun he => ht (hinjT (he.symm.trans htok')))]
    | transfer => rfl
    | addSupportedToken => rfl
    | removeSupportedToken => rfl
    | setAttestationRegistry => rfl
    | transferOwnership => rfl
    | setVerifier => rfl

/-! ## The equation for the model's balance field, and W9 -/

/-- **Accounting equation from stated token deltas.** Every premise of `refineP_run` (with the global
tree premises `TreeLink` and `TreeHyp`), plus the token premises: from zero pool balance, under
the balance premises, rollback and no self-withdrawal, the external pool balance equals the
model's balance field, and so the live note value, in every accepted history. -/
theorem refineB_run {H : Nat → Nat → Nat} {X : Contract} {K : Chain} {C : Circuits P}
    {E : Enc P} {ext : Extractor P} {Incl : Nat → Nat → Prop} {Coll : List Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hinj : Function.Injective E.cm)
    (hinjT : Function.Injective E.tok) (hRd : PoolCallReadings X)
    (hz : PoolStartsEmpty X K) (hND : NoOutsideDebit X K) (hNC : NoOutsideCredit X K)
    (hTR : TokenRollback X K)
    {h : List Call} {σ : Storage} {w : K.World} (hacc : AcceptedB X K h σ w)
    (hC1 : NoSetVerifier h) (hS : NoSelfWithdraw X h) (hEx : ExtractedWitnesses C ext h)
    (hTL : TreeLink H Incl Coll (ghostLeaves h) (inputWords E ext h))
    (hTH : TreeHyp Coll (ghostLeaves h) (inputWords E ext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ txs st, txs.map eraseSnap = txsOf ext h ∧
      Run' (supOf E h) txs st ∧ RepP H E (supOf E h) (ghostLeaves h) σ st ∧
      (∀ t, K.bal w (E.tok t) X.self = st.balance t) ∧
      (∀ t, K.bal w (E.tok t) X.self = liveValue st t) := by
  obtain ⟨txs, st, hE, hr, hR⟩ :=
    refineP_run hG0 hRB hEnv hD hTP hWP hA hC hinj hacc.accepted hC1 hEx hTL hTH hcr
  have hTC := TokenCallFacts.of_posts hD hTP hWP hRd
  have hbal : ∀ t, K.bal w (E.tok t) X.self = st.balance t := fun t => by
    rw [bal_eq_ledger hTC hz hND hNC hTR hacc hC1 hS, hr.balance_eq, ← modelBal_eraseSnap txs t,
      hE, modelBal_txsOf hC hinjT hEx t]
  refine ⟨txs, st, hE, hr, hR, hbal, fun t => ?_⟩
  rw [hbal t,
    balanceIsLiveValue_prov _ txs st hr (cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr)) t]

/-- **W9 corollary: the withdrawal guard is about the external balance.** Every premise of
`refineP_run` (the global tree premises of `refineP_run`), plus the call readings, the injective token encoding,
no outside debit and rollback (no zero start, no-outside-credit or self-withdrawal premise
needed): the model's balance field, its live note value, and every amount `withdraw_balanceP`
bounds by it, are at most the pool's external balance. In particular a withdrawal the model accepts at this state
(`withdrawGuard'`) is covered by the pool's real balance. -/
theorem refineB_w9 {H : Nat → Nat → Nat} {X : Contract} {K : Chain} {C : Circuits P}
    {E : Enc P} {ext : Extractor P} {Incl : Nat → Nat → Prop} {Coll : List Nat → Nat → Prop}
    (hG0 : ConstructorPost X) (hRB : Rollback X) (hEnv : OwnerCallbackFree X)
    (hD : DepositPost H X) (hTP : TransferPost H X) (hWP : WithdrawPost X) (hA : AdminStutter X)
    (hC : CircuitFacts E C Incl) (hinj : Function.Injective E.cm)
    (hinjT : Function.Injective E.tok) (hRd : PoolCallReadings X)
    (hND : NoOutsideDebit X K) (hTR : TokenRollback X K)
    {h : List Call} {σ : Storage} {w : K.World} (hacc : AcceptedB X K h σ w)
    (hC1 : NoSetVerifier h) (hEx : ExtractedWitnesses C ext h)
    (hTL : TreeLink H Incl Coll (ghostLeaves h) (inputWords E ext h))
    (hTH : TreeHyp Coll (ghostLeaves h) (inputWords E ext h))
    (hcr : CryptoHyp P (txsOf ext h)) :
    ∃ txs st, txs.map eraseSnap = txsOf ext h ∧
      Run' (supOf E h) txs st ∧ RepP H E (supOf E h) (ghostLeaves h) σ st ∧
      (∀ t, st.balance t ≤ K.bal w (E.tok t) X.self) ∧
      (∀ t, liveValue st t ≤ K.bal w (E.tok t) X.self) ∧
      (∀ d : WithdrawData P, withdrawGuard' d st →
        d.note.amount ≤ K.bal w (E.tok d.note.token) X.self) ∧
      (∀ d : WithdrawData P, CryptoHyp P (txs ++ [.withdraw d]) → d.note.cm ∈ st.leaves →
        d.note.ownedBy d.key → st.fresh d.nf → d.note.wf →
        d.note.amount ≤ K.bal w (E.tok d.note.token) X.self) := by
  obtain ⟨txs, st, hE, hr, hR⟩ :=
    refineP_run hG0 hRB hEnv hD hTP hWP hA hC hinj hacc.accepted hC1 hEx hTL hTH hcr
  have hTC := TokenCallFacts.of_posts hD hTP hWP hRd
  have hbal : ∀ t, st.balance t ≤ K.bal w (E.tok t) X.self := fun t => by
    rw [hr.balance_eq, ← modelBal_eraseSnap txs t, hE, modelBal_txsOf hC hinjT hEx t]
    exact ledger_le_bal hTC hND hTR hacc hC1 (E.tok t)
  have hcr' : CryptoHyp P txs := cryptoHyp_of_eraseSnap (by rw [hE]; exact hcr)
  refine ⟨txs, st, hE, hr, hR, hbal, fun t => ?_, fun d hg => ?_,
    fun d hc hin ho hf hwf => ?_⟩
  · rw [← balanceIsLiveValue_prov _ txs st hr hcr' t]
    exact hbal t
  · exact Nat.le_trans hg.2.2.2.2.2.2 (hbal _)
  · exact Nat.le_trans (withdraw_balanceP hr d hc hin ho hf hwf) (hbal _)

end LeanShieldedPool.Refine
