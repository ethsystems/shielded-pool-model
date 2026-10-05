import LeanShieldedPool.Pool.Tx

/-!
# Event log (spec Section 4.4)

Events expose commitments and nullifiers without note or key witnesses.
Transfer outputs keep public-input order (spec line 234). Encrypted
payloads stay outside the model (SPEC-MAP simplification 8). Atomic
`Step` does not model event timing relative to external calls
(simplification 9), so replay establishes reconstruction from logs only.
-/

namespace LeanShieldedPool

variable {P : PrimSpec}

inductive Event (P : PrimSpec) where
  | deposit (commitment : P.Commitment)
  | transfer (nf1 nf2 : P.Nullifier) (out1 out2 : P.Commitment)
  | withdraw (nullifier : P.Nullifier)

def Tx.event : Tx P → Event P
  | .deposit d => .deposit d.note.cm
  | .transfer d => .transfer d.nf1 d.nf2 d.out1.cm d.out2.cm
  | .withdraw d => .withdraw d.nf

def events (txs : List (Tx P)) : List (Event P) := txs.map Tx.event

/-- Leaves follow insertion order. Nullifier batches are newest first,
matching `St.nullifiers`, with transfer slots kept in public-input order. -/
def replayStep (state : List P.Commitment × List P.Nullifier) :
    Event P → List P.Commitment × List P.Nullifier
  | .deposit cm => (state.1 ++ [cm], state.2)
  | .transfer nf1 nf2 out1 out2 =>
      (state.1 ++ [out1, out2], nf1 :: nf2 :: state.2)
  | .withdraw nf => (state.1, nf :: state.2)

def replay (log : List (Event P)) : List P.Commitment × List P.Nullifier :=
  log.foldl replayStep ([], [])

def replayLeaves (log : List (Event P)) : List P.Commitment := (replay log).1

def replayNullifiers (log : List (Event P)) : List P.Nullifier := (replay log).2

end LeanShieldedPool
