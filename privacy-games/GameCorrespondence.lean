import PoolGame.Basic
import LeanShieldedPool.Pool.Events

/-! Observer correspondence and the obstruction to realizing every legal game world. -/

namespace LeanShieldedPool.GameCorrespondence

open OracleComp

abbrev gamePrim (P : LeanShieldedPool.PrimSpec) : PoolGame.PrimSpec where
  Token := P.Token
  Address := P.Address
  PubKey := P.PubKey
  SpendKey := P.SpendKey
  Salt := P.Salt
  Commitment := P.Commitment
  Nullifier := P.Nullifier
  derivePub := P.derivePub
  commit := P.commit
  nullify := P.nullify

variable {P : LeanShieldedPool.PrimSpec}

def gameEvent : LeanShieldedPool.Event P → PoolGame.Event (gamePrim P)
  | .deposit cm => .deposit cm
  | .transfer nf1 nf2 out1 out2 => .transfer nf1 nf2 out1 out2
  | .withdraw nf => .withdraw nf

def observerView (txs : List (Tx P)) : List (PoolGame.Event (gamePrim P)) :=
  (events txs).map gameEvent

def runObserverView {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (_run : Run sup txs st) : List (PoolGame.Event (gamePrim P)) := observerView txs

def transferWitness (d : TransferData P) : PoolGame.TransferWitness (gamePrim P) where
  inCm1 := d.in1.cm
  inCm2 := d.in2.cm
  spendKey1 := d.key
  spendKey2 := d.key
  outToken1 := d.out1.token
  outAmt1 := d.out1.amount
  outPk1 := d.out1.ownerPubkey
  outToken2 := d.out2.token
  outAmt2 := d.out2.amount
  outPk2 := d.out2.ownerPubkey

theorem transfer_event_correspondence (d : TransferData P) :
    gameEvent (Tx.event (.transfer d)) =
      (transferWitness d).toEvent d.out1.salt d.out2.salt := rfl

theorem run_observer_correspondence {sup : P.Token → Prop}
    {txs : List (Tx P)} {st : St P} (run : Run sup txs st) :
    runObserverView run = (events txs).map gameEvent := rfl

def RealizesLog (sup : P.Token → Prop) (log : List (PoolGame.Event (gamePrim P))) : Prop :=
  ∃ txs st, Run sup txs st ∧ observerView txs = log

def RealizesWorld (sup : P.Token → Prop)
    (ws : List (PoolGame.TransferWitness (gamePrim P)))
    (log : List (PoolGame.Event (gamePrim P))) : Prop :=
  ∃ ds : List (TransferData P), ∃ st,
    Run sup (ds.map Tx.transfer) st ∧ ds.map transferWitness = ws ∧
      observerView (ds.map Tx.transfer) = log

theorem realizesWorld_realizesLog {sup : P.Token → Prop}
    {ws : List (PoolGame.TransferWitness (gamePrim P))}
    {log : List (PoolGame.Event (gamePrim P))} (h : RealizesWorld sup ws log) :
    RealizesLog sup log := by
  obtain ⟨ds, st, run, _, view⟩ := h
  exact ⟨ds.map Tx.transfer, st, run, view⟩

/-- Each field is an obligation, not an assumed or proved realization theorem. -/
structure LegalPairCorrespondence [SampleableType P.Salt] (sup : P.Token → Prop)
    (ws₀ ws₁ : List (PoolGame.TransferWitness (gamePrim P))) : Prop where
  left_runs : ∀ log ∈ support (PoolGame.publish ws₀), RealizesWorld sup ws₀ log
  right_runs : ∀ log ∈ support (PoolGame.publish ws₁), RealizesWorld sup ws₁ log

def UniversalLegalCorrespondence [SampleableType P.Salt] (sup : P.Token → Prop) : Prop :=
  ∀ ws₀ ws₁, PoolGame.LegalChallenge ws₀ ws₁ → LegalPairCorrespondence sup ws₀ ws₁

def EventGuard : PoolGame.Event (gamePrim P) → Prop
  | .deposit _ => True
  | .transfer nf1 nf2 out1 out2 => nf1 ≠ nf2 ∧ out1 ≠ out2
  | .withdraw _ => True

theorem step_event_guard {st st' : St P} {tx : Tx P} (h : Step st tx st') :
    EventGuard (gameEvent tx.event) := by
  cases h with
  | deposit _ => trivial
  | withdraw _ => trivial
  | transfer h =>
    dsimp [EventGuard, gameEvent, Tx.event]
    rcases h with ⟨_, _, _, _, _, _, _, hnf, _, _, _, _, _, _, _, _, _, _, hcm⟩
    exact ⟨hnf, hcm⟩

theorem run_events_guard {sup : P.Token → Prop} {txs : List (Tx P)} {st : St P}
    (run : Run sup txs st) : ∀ e ∈ observerView txs, EventGuard e := by
  induction run with
  | empty => simp [observerView, events]
  | @step txs st st' tx _ step ih =>
    intro e he
    simp only [observerView, events, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | rfl
    · exact ih e he
    · exact step_event_guard step

theorem realizesLog_events_guard {sup : P.Token → Prop}
    {log : List (PoolGame.Event (gamePrim P))} (h : RealizesLog sup log) :
    ∀ e ∈ log, EventGuard e := by
  obtain ⟨txs, st, run, rfl⟩ := h
  exact run_events_guard run

theorem duplicate_nullifier_not_realizable (sup : P.Token → Prop)
    (nf : P.Nullifier) (out1 out2 : P.Commitment) :
    ¬ RealizesLog sup [PoolGame.Event.transfer nf nf out1 out2] := by
  intro h
  have he := realizesLog_events_guard h (.transfer nf nf out1 out2) (by simp)
  exact he.1 rfl

def duplicateInput (w : PoolGame.TransferWitness (gamePrim P)) :
    PoolGame.TransferWitness (gamePrim P) :=
  { w with inCm2 := w.inCm1, spendKey2 := w.spendKey1 }

theorem duplicateInput_legal (w : PoolGame.TransferWitness (gamePrim P)) :
    PoolGame.LegalChallenge [duplicateInput w] [duplicateInput w] := by
  simp [PoolGame.LegalChallenge, PoolGame.RecipientOnly]

theorem duplicateInput_no_run (sup : P.Token → Prop)
    (w : PoolGame.TransferWitness (gamePrim P)) (s1 s2 : P.Salt) :
    ¬ RealizesLog sup [(duplicateInput w).toEvent s1 s2] :=
  duplicate_nullifier_not_realizable sup _ _ _

theorem singleton_in_publish_support [SampleableType P.Salt]
    (w : PoolGame.TransferWitness (gamePrim P)) (s1 s2 : P.Salt) :
    [w.toEvent s1 s2] ∈ support (PoolGame.publish [w]) := by
  simp only [PoolGame.publish, bind_pure_comp, mem_support_bind_iff]
  exact ⟨s1, mem_support_uniformSample _, s2, mem_support_uniformSample _, by simp⟩

theorem duplicateInput_no_correspondence [SampleableType P.Salt]
    (sup : P.Token → Prop) (w : PoolGame.TransferWitness (gamePrim P)) :
    ¬ LegalPairCorrespondence sup [duplicateInput w] [duplicateInput w] := by
  intro h
  obtain ⟨s⟩ := (inferInstance : Nonempty P.Salt)
  exact duplicateInput_no_run sup w s s
    (realizesWorld_realizesLog (h.left_runs _ (singleton_in_publish_support _ s s)))

theorem universal_legal_correspondence_false [SampleableType P.Salt]
    (sup : P.Token → Prop) (w : PoolGame.TransferWitness (gamePrim P)) :
    ¬ UniversalLegalCorrespondence sup := by
  intro h
  exact duplicateInput_no_correspondence sup w
    (h _ _ (duplicateInput_legal w))

theorem duplicate_output_not_realizable (sup : P.Token → Prop)
    (nf1 nf2 : P.Nullifier) (out : P.Commitment) :
    ¬ RealizesLog sup [PoolGame.Event.transfer nf1 nf2 out out] := by
  intro h
  have he := realizesLog_events_guard h (.transfer nf1 nf2 out out) (by simp)
  exact he.2 rfl

def duplicateOutputMessage (w : PoolGame.TransferWitness (gamePrim P)) :
    PoolGame.TransferWitness (gamePrim P) :=
  { w with outToken2 := w.outToken1, outAmt2 := w.outAmt1, outPk2 := w.outPk1 }

theorem equal_salt_no_run (sup : P.Token → Prop)
    (w : PoolGame.TransferWitness (gamePrim P)) (s : P.Salt) :
    ¬ RealizesLog sup [(duplicateOutputMessage w).toEvent s s] :=
  duplicate_output_not_realizable sup _ _ _

theorem duplicateOutputMessage_no_correspondence [SampleableType P.Salt]
    (sup : P.Token → Prop) (w : PoolGame.TransferWitness (gamePrim P)) :
    ¬ LegalPairCorrespondence sup [duplicateOutputMessage w] [duplicateOutputMessage w] := by
  intro h
  obtain ⟨s⟩ := (inferInstance : Nonempty P.Salt)
  exact equal_salt_no_run sup w s
    (realizesWorld_realizesLog (h.left_runs _ (singleton_in_publish_support _ s s)))

namespace SaltCollision

abbrev primitives : LeanShieldedPool.PrimSpec where
  Token := Unit
  Address := Unit
  PubKey := Unit
  SpendKey := Unit
  Salt := Fin 4
  Commitment := Fin 4
  Nullifier := Fin 4
  derivePub := fun _ => ()
  commit := fun _ _ _ salt => salt
  nullify := fun cm _ => cm

def note (salt : Fin 4) : Note primitives := ⟨(), 0, (), salt⟩

def deposit : DepositData primitives := ⟨{ note 0 with amount := 1 }, ()⟩

noncomputable def initial : St primitives :=
  deposit.post (St.empty primitives (fun _ => True))

theorem deposit_guard : deposit.guard (St.empty primitives (fun _ => True)) := by
  norm_num [DepositData.guard, deposit, note, St.empty, St.leaves, U128, maxU128]

theorem setup_run : Run (fun _ => True) [Tx.deposit deposit] initial :=
  Run.step Run.empty (Step.deposit deposit_guard)

def transfer : TransferData primitives where
  key := ()
  in1 := deposit.note
  in2 := note 1
  out1 := { note 2 with amount := 1 }
  out2 := note 3
  snapshot := 1

def world : PoolGame.TransferWitness (gamePrim primitives) := transferWitness transfer

theorem transfer_guard : transfer.guard initial := by
  norm_num [TransferData.guard, transfer, initial, deposit, DepositData.post, note,
    St.rootInWindow, St.pushWindow, rootWindow, St.empty, St.inTreeAt,
    Note.ownedBy, Note.isBallast, St.fresh, TransferData.nf1, TransferData.nf2,
    Note.nf, Note.cm, U128, maxU128, St.leaves, primitives, Fin.ext_iff]
  simp only [Fin.ext_iff]
  norm_num

theorem accepted_run :
    Run (fun _ => True) [Tx.deposit deposit, Tx.transfer transfer]
      (transfer.post initial) :=
  Run.step setup_run (Step.transfer transfer_guard)

theorem world_legal : PoolGame.LegalChallenge [world] [world] := by
  simp [PoolGame.LegalChallenge, PoolGame.RecipientOnly]

theorem funded_world_has_realization :
    ∃ ds : List (TransferData primitives), ∃ st,
      Run (fun _ => True) ([Tx.deposit deposit] ++ ds.map Tx.transfer) st ∧
      ds.map transferWitness = [world] ∧
      observerView ([Tx.deposit deposit] ++ ds.map Tx.transfer) =
        [.deposit 0, world.toEvent 2 3] := by
  exact ⟨[transfer], _, accepted_run, rfl, rfl⟩

theorem collision_in_support :
    [world.toEvent 2 2] ∈ support (PoolGame.publish [world]) :=
  singleton_in_publish_support world 2 2

theorem collision_probability_pos :
    0 < Pr[= [world.toEvent 2 2] | PoolGame.publish [world]] :=
  (probOutput_pos_iff _ _).mpr collision_in_support

theorem collision_has_no_run :
    ¬ RealizesLog (fun _ => True) [world.toEvent 2 2] :=
  duplicate_output_not_realizable _ _ _ _

theorem realizable_world_no_correspondence :
    ¬ LegalPairCorrespondence (fun _ => True) [world] [world] := by
  intro h
  exact collision_has_no_run
    (realizesWorld_realizesLog (h.left_runs _ collision_in_support))

end SaltCollision

end LeanShieldedPool.GameCorrespondence

#print axioms LeanShieldedPool.GameCorrespondence.gamePrim
#print axioms LeanShieldedPool.GameCorrespondence.gameEvent
#print axioms LeanShieldedPool.GameCorrespondence.observerView
#print axioms LeanShieldedPool.GameCorrespondence.runObserverView
#print axioms LeanShieldedPool.GameCorrespondence.transferWitness
#print axioms LeanShieldedPool.GameCorrespondence.transfer_event_correspondence
#print axioms LeanShieldedPool.GameCorrespondence.run_observer_correspondence
#print axioms LeanShieldedPool.GameCorrespondence.RealizesLog
#print axioms LeanShieldedPool.GameCorrespondence.RealizesWorld
#print axioms LeanShieldedPool.GameCorrespondence.realizesWorld_realizesLog
#print axioms LeanShieldedPool.GameCorrespondence.LegalPairCorrespondence
#print axioms LeanShieldedPool.GameCorrespondence.UniversalLegalCorrespondence
#print axioms LeanShieldedPool.GameCorrespondence.EventGuard
#print axioms LeanShieldedPool.GameCorrespondence.step_event_guard
#print axioms LeanShieldedPool.GameCorrespondence.run_events_guard
#print axioms LeanShieldedPool.GameCorrespondence.realizesLog_events_guard
#print axioms LeanShieldedPool.GameCorrespondence.duplicate_nullifier_not_realizable
#print axioms LeanShieldedPool.GameCorrespondence.duplicateInput
#print axioms LeanShieldedPool.GameCorrespondence.duplicateInput_legal
#print axioms LeanShieldedPool.GameCorrespondence.duplicateInput_no_run
#print axioms LeanShieldedPool.GameCorrespondence.singleton_in_publish_support
#print axioms LeanShieldedPool.GameCorrespondence.duplicateInput_no_correspondence
#print axioms LeanShieldedPool.GameCorrespondence.universal_legal_correspondence_false
#print axioms LeanShieldedPool.GameCorrespondence.duplicate_output_not_realizable
#print axioms LeanShieldedPool.GameCorrespondence.duplicateOutputMessage
#print axioms LeanShieldedPool.GameCorrespondence.equal_salt_no_run
#print axioms LeanShieldedPool.GameCorrespondence.duplicateOutputMessage_no_correspondence
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.primitives
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.note
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.transfer
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.world
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.transfer_guard
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.accepted_run
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.world_legal
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.funded_world_has_realization
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.collision_in_support
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.collision_probability_pos
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.collision_has_no_run
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.realizable_world_no_correspondence

#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.deposit
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.initial
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.deposit_guard
#print axioms LeanShieldedPool.GameCorrespondence.SaltCollision.setup_run
