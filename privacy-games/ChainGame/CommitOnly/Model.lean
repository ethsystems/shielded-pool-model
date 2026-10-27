import RecipientGame.ROMCommit.Security
import ChainGame.AdaptiveRejection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open OracleComp OracleSpec ENNReal

namespace LeanShieldedPool.ChainGame.CommitOnly
open GameCorrespondence CommitROM CommitROM.Model
variable {P : PrimSpec} {cap n : Nat}

abbrev BoundedTemplate (P : PrimSpec) (cap : Nat) :=
  {t : Template P // t.body.out1.amount < cap ∧ t.body.out2.amount < cap}
abbrev World (P : PrimSpec) (cap n : Nat) :=
  {ts : List (BoundedTemplate P cap) // ts.length ≤ n}

def bodies (ts : List (BoundedTemplate P cap)) : List (RecipientGame.ROMCommit.BoundedTransfer P cap) :=
  ts.map (fun t => ⟨t.val.body,t.property⟩)

theorem bodies_length (ts : List (BoundedTemplate P cap)) : (bodies ts).length = ts.length := by
  simp [bodies]

attribute [simp] bodies_length

def rebaseTemplate (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap) (t : Template P) :
    Template (oraclePrim P cap hp hn hc) :=
  ⟨RecipientGame.ROMCommit.rebaseTransfer hp hn hc t.body,t.input1,t.input2⟩

def worldBack (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ts : List (BoundedTemplate P cap)) : List (Template (oraclePrim P cap hp hn hc)) :=
  ts.map (fun t => rebaseTemplate hp hn hc t.val)

def Aligned (ts us : List (BoundedTemplate P cap)) : Prop :=
  Scoped 0 (ts.map Subtype.val) ∧ Scoped 0 (us.map Subtype.val) ∧
  List.Forall₂ (fun t u => t.val.input1 = u.val.input1 ∧ t.val.input2 = u.val.input2 ∧
    t.val.body.snapshot = u.val.body.snapshot) ts us

theorem scoped_back (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ts : List (BoundedTemplate P cap)) (i : Nat) :
    Scoped i (worldBack hp hn hc ts) ↔ Scoped i (ts.map Subtype.val) := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ih => simpa only [worldBack, List.map_cons, Scoped, rebaseTemplate] using
      and_congr_right (fun _ => and_congr_right (fun _ => ih (i+1)))

theorem recipient_back_iff (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ts us : List (BoundedTemplate P cap)) :
    RecipientPair (worldBack hp hn hc ts) (worldBack hp hn hc us) ↔
      Aligned ts us ∧ PoolGame.LegalChallenge
        (RecipientGame.ROMCommit.projected hp hn hc (bodies ts))
        (RecipientGame.ROMCommit.projected hp hn hc (bodies us)) := by
  have hpair : List.Forall₂ RecipientOnly (worldBack hp hn hc ts) (worldBack hp hn hc us) ↔
      List.Forall₂ (fun t u => t.val.input1 = u.val.input1 ∧ t.val.input2 = u.val.input2 ∧
        t.val.body.snapshot = u.val.body.snapshot) ts us ∧
      PoolGame.LegalChallenge (RecipientGame.ROMCommit.projected hp hn hc (bodies ts))
        (RecipientGame.ROMCommit.projected hp hn hc (bodies us)) := by
    induction ts generalizing us with
    | nil => cases us <;> simp [worldBack, bodies, RecipientGame.ROMCommit.projected, PoolGame.LegalChallenge]
    | cons t ts ih =>
      cases us with
      | nil => simp [worldBack, bodies, RecipientGame.ROMCommit.projected, PoolGame.LegalChallenge]
      | cons u us =>
        simp only [worldBack, bodies, List.map_cons, RecipientGame.ROMCommit.projected,
          PoolGame.LegalChallenge, List.forall₂_cons] at *
        rw [ih]
        change ((_ ∧ _ ∧ _ ∧ _) ∧ (_ ∧ _)) ↔ ((_ ∧ _ ∧ _) ∧ _) ∧ (_ ∧ _)
        tauto
  rw [RecipientPair, scoped_back, scoped_back, hpair]
  simp only [Aligned]
  tauto

def reference (hn : P.SpendKey × P.Commitment → P.Nullifier)
    (history : CommitmentHistory P) (ref : Option OutputRef)
    (key : P.SpendKey) (fallback : P.Nullifier) : P.Nullifier :=
  match ref with
  | none => fallback
  | some (i,slot) => ((history[i]?).map (fun cs => hn (key,if slot then cs.2 else cs.1))).getD fallback

def rewrite (hn : P.SpendKey × P.Commitment → P.Nullifier) :
    List (BoundedTemplate P cap) → CommitmentHistory P →
    List (PoolGame.Event (gamePrim P)) → List (PoolGame.Event (gamePrim P))
  | t :: ts, hist, .transfer n1 n2 c1 c2 :: log =>
      .transfer (reference hn hist t.val.input1 t.val.body.key n1)
        (reference hn hist t.val.input2 t.val.body.key n2) c1 c2 ::
        rewrite hn ts (hist ++ [(c1,c2)]) log
  | _, _, log => log

theorem rewrite_back (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ts : List (BoundedTemplate P cap)) (hist : CommitmentHistory P)
    (log : List (PoolGame.Event (gamePrim (oraclePrim P cap hp hn hc)))) :
    (rewriteLog (worldBack hp hn hc ts) hist log).map (eventBack hp hn hc) =
      rewrite hn ts hist (log.map (eventBack hp hn hc)) := by
  induction ts generalizing hist log with
  | nil => rfl
  | cons t ts ih =>
    cases log with
    | nil => rfl
    | cons e log =>
      cases e <;> simp only [worldBack, List.map_cons, rebaseTemplate, rewriteLog, rewrite, eventBack]
      simp only [worldBack, rebaseTemplate] at ih
      rw [ih]
      rfl

theorem rewrite_recipient (hp : P.SpendKey → P.PubKey)
    (hn : P.SpendKey × P.Commitment → P.Nullifier) (hc : Model.Table P cap)
    (ts us : List (BoundedTemplate P cap)) (ha : Aligned ts us)
    (hl : PoolGame.LegalChallenge (RecipientGame.ROMCommit.projected hp hn hc (bodies ts))
      (RecipientGame.ROMCommit.projected hp hn hc (bodies us)))
    (hist : CommitmentHistory P) (log : List (PoolGame.Event (gamePrim P))) :
    rewrite hn ts hist log = rewrite hn us hist log := by
  obtain ⟨hs,hs',ha⟩ := ha
  clear hs hs'
  induction ha generalizing hist log with
  | nil => rfl
  | @cons t u ts us htu hrest ih =>
    have hh : PoolGame.RecipientOnly
        (RecipientGame.ROMCommit.witnessBack hp hn hc (transferWitness (RecipientGame.ROMCommit.rebaseTransfer hp hn hc t.val.body)))
        (RecipientGame.ROMCommit.witnessBack hp hn hc (transferWitness (RecipientGame.ROMCommit.rebaseTransfer hp hn hc u.val.body))) ∧
        PoolGame.LegalChallenge (RecipientGame.ROMCommit.projected hp hn hc (bodies ts))
          (RecipientGame.ROMCommit.projected hp hn hc (bodies us)) := by
      simpa only [PoolGame.LegalChallenge, RecipientGame.ROMCommit.projected, bodies,
        List.map_cons, List.forall₂_cons] using hl
    have hk : t.val.body.key = u.val.body.key := hh.1.2.2.1
    cases log with
    | nil => rfl
    | cons e log =>
      cases e <;> simp only [rewrite]
      rw [htu.1, htu.2.1, hk, ih hh.2]

theorem sampleWorld_static [SampleableType P.Salt] {α : Type}
    (ts : List (Template P)) (hist : List (TransferData P))
    (f : List (PoolGame.Event (gamePrim P)) → ProbComp α) :
    (do let ds ← sampleWorld hist ts; f (observerView (ds.map Tx.transfer))) =
      (do let ds ← RecipientGame.sampleWorld (ts.map Template.body)
          f (rewriteLog ts (commitmentHistory hist) (observerView (ds.map Tx.transfer)))) := by
  rw [sampleWorld_observer_bind]
  symm
  simpa only [RecipientGame.projectWorld, List.map_map, Function.comp_def] using
    RecipientGame.sampleWorld_observer_bind (ts.map Template.body)
      (fun log => f (rewriteLog ts (commitmentHistory hist) log))

end LeanShieldedPool.ChainGame.CommitOnly
