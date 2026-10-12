# Claims

The fifteen proved theorems, each with its Lean name, English, spec
clause and hypothesis. The statement files
`LeanShieldedPool/Statements/L3.lean`, `L4.lean`, `L4B.lean` and
`L5.lean` are the source of truth. The gate checks the type of each
name against `statements/INVENTORY.md`.

## How to read a row

Each claim is a Prop, such as `noDoubleSpend`, and a theorem that proves
it for every `P : PrimSpec` (the opaque hashes and field types), such as
`noDoubleSpend_proof`. Each base Prop covers every accepted history:
`Run sup txs st` says that the operations `txs` run from the empty pool
and reach the state `st`. Spec clauses refer to spec 2 at 4d4dce1
(`specs/2/README.md` in ethsystems/specs-private); numbers in brackets
are its line numbers.

## The hypothesis

`CryptoHyp P txs` (L3.lean) says: among the notes and keys that appear in
the history `txs`, no two distinct notes with `u128` amounts share a
commitment (Poseidon4), and no two distinct spending keys derive the same
public key (Poseidon1). The commitment part is restricted to well-formed
notes (`Note.wf`). Every note of an accepted run passes a guard range
check (`Run.runNotes_wf`), so on accepted runs the restricted and
unrestricted forms impose the same condition; the restriction states the
domain of the hypothesis instead of leaving the reader to replay the
guard argument. It covers that one history only. It says nothing about
the hashes outside it, and it is not a Poseidon security claim. It is a
theorem hypothesis, not an axiom. No theorem uses the global form
`CryptoHypGlobal`.

## The nine base theorems

| # | Lean name | English | Spec clause | Hypothesis |
|---|---|---|---|---|
| 1 | `nullifierUniqueness_proof` | The list of spent nullifiers has no repeat. | 5.2 (313-314) | none |
| 2 | `noDoubleSpend_proof` | No input commitment is consumed twice, ballast included. | 6.2 (441), 4.2 step 5 | `CryptoHyp` |
| 3 | `valueConservation_proof` | For every token, total deposited equals total withdrawn plus the value of live notes. | 6.2 (442), 5.3 | `CryptoHyp` |
| 4 | `poolSolvency_proof` | For every token, the contract balance plus total withdrawn equals total deposited. | 4.4 | none |
| 5 | `noOverWithdrawal_proof` | For every token, total withdrawn never exceeds total deposited. | corollary supporting 6.2 (441-442); no own row | none |
| 6 | `noMinting_proof` | For every token, live note value never exceeds total deposited. | corollary supporting 6.2 (441-442); no own row | `CryptoHyp` |
| 7 | `balanceIsLiveValue_proof` | For every token, the contract balance equals the live note value. | 4.4, 6.2 | `CryptoHyp` |
| 8 | `spendRequiresOwnerKey_proof` | This is owner-key binding: each operation's witness spending key owns every history note whose commitment the operation consumes. | 5.3 (319, 348, 365), 463 | `CryptoHyp` |
| 9 | `eventReplayFaithful_proof` | Replaying the event log rebuilds the commitment tree and the nullifier set exactly. | 4.4 (279) | none |

In the Hypothesis column, "none" means no cryptographic hypothesis.
Theorems 4 and 5 also rest on the withdraw payout bound, a modelling
device (simplification 16).

## The six epoch theorems

Names below have the prefix `LeanShieldedPool.Epoch`. Their statements
are in `Statements/L5.lean`, under `Candidates`. That namespace retains
its source name; all six statements have proofs.

These rows concern the PoC extension spec, whose hash and clauses appear
in SPEC-MAP.md. They do not extend the guarantees attributed to spec 2.

| # | Lean name | English | Extension spec clause | Hypothesis |
|---|---|---|---|---|
| 10 | `crossEpochNoDoubleSpend_proof` | No commitment of a note with nonzero amount is consumed twice across an accepted history, including rollovers. A zero-amount second input (ballast) is excluded: the circuit skips its chain check, so a ballast commitment can be consumed again in a later epoch; it carries zero value. | Guarantees: cross-epoch double-spend safety (436), for value-bearing inputs | epoch `Candidates.CryptoHyp` |
| 11 | `frozenRootImmutability_proof` | After rollover, every accepted suffix preserves the newly sealed nullifier list and all older sealed lists. A frame property of the step relation: it holds from any state, because only rollover writes `frozen`. | On-Chain State (163); sealed data is immutable (205) | accepted suffix |
| 12 | `canonicalAppend_proof` | Each non-rollover step appends fresh nullifiers in spend order. The same holds for any segment whose endpoint epochs agree. | On-Chain State (161, 167); Insertion Circuit (394-405) | accepted step or segment; unchanged epoch |
| 13 | `chainKeyBinding_proof` | All consuming witnesses for one commitment use the same owned note and the same run key. | Spend Circuit (366, 372); the chain key binding of 336-337 is assumed (simplification 2), not proved | epoch `Candidates.CryptoHyp` |
| 14 | `epochZeroRefinesBase_proof` | A run without rollover translates to an accepted base run with matching state, hypotheses and consumption log. The refinement is one way: an epoch model that rejects honest base runs still satisfies it. | Diff vs Parent (47-62) | epoch `Candidates.CryptoHyp`; no rollover; `BallastStamped` (every transfer's second input carries creation epoch 0) |
| 15 | `spendableAfterRollover_proof` | After a rollover, an owned, unspent note in the tree with a clear history passes the withdraw guard at the current root; this is model liveness, not a payout claim. | Guarantees (436, second sentence); Chain Maintenance (267) | owner key; nonzero amount; enough pool balance; clear history (its nullifier is in no sealed list since creation and not in the active list) |

Rows 10, 13, 14 and 15 quantify over accepted epoch runs. The epoch
hypothesis binds full notes, including `epochCreated`, and spending keys
within that run. It is separate from the base model's `CryptoHyp`, and
unlike that one its commitment part is not restricted to `wf` notes.
The epoch guards require `wf` for every note they record, so on
accepted runs the two forms impose the same condition; that agreement
is a reading argument here, not a proved lemma. Rows 11 and 12 require
no collision hypothesis. None of these results uses `EpochDistinct`.

The epoch model follows the repinned base: its transfer guard requires
membership for the first input, as the base guard does. No L5 statement
text differs from the research-repo source, but the model admits fewer
histories than the pre-repin export did, and row 14 targets the revised
base `CryptoHyp`.

Row 14 also states the implication from the base `noDoubleSpend`
proposition to the epoch consumption claim (over `Tx.valueConsumes`, a
sublist of the base consumption log). It does not prove a recursive
circuit's base case (extension spec 324-340), or conservation for
arbitrary epoch runs. Its `BallastStamped` premise says every transfer's
second input carries creation epoch 0. For a value-bearing second input
this already follows from the chain check in a run without rollover; for
a ballast it is an assumption about the client: the spec gives every
created note `epoch_created = currentEpoch` (263, 269), which is 0 before
any rollover, but says nothing about what a ballast carries, and the code
does not constrain it.

**Ballast and the chain check.** The extension spec states the chain
check per input note with no ballast exception (358-366). The reference
transfer circuit skips both the membership and the chain check for a
zero-amount second input
(`shielded-pool-extension/circuits/transfer/src/main.nr:143-156`), and
the contract then accepts any caller-supplied `epoch_created` for that
input and derives the accumulator from it, which the circuit does not
check for a ballast (`ShieldedPoolExt.sol:268-270`;
`expectedChainAccumulator` returns 0 when `epochCreated` is at or above
`currentEpoch`). The model follows
the circuit: `TransferData.guard` requires `isBallast ∨ ChainFacts` for
the second input (simplification 7), and row 10 counts value-bearing
consumption only (`Tx.valueConsumes`). The deviation between the
extension spec and the circuit is proposed as a one-paragraph spec exception in
pocs-private PR #18; if the
circuit changes to check ballast too, the guard can take the stronger
form and row 10 can count ballast again.

`spendableAfterRollover` is the liveness counterpart of rows 10 to 14:
a model that rejected every spend after a rollover would satisfy all five
safety rows, and this row rules that out. It derives window membership of
the current root, tree membership at that root, well-formedness and the
creation-epoch bound from the run; the balance stays a premise. It says
the epoch model accepts the step and debits the pool field, not that a
token moves.

`frozenRootImmutability` preserves list contents. It does not mention
concrete Merkle roots. `chainKeyBinding` compares supplied semantic
witnesses; it does not extract keys from separate recursive proofs, and
it states nothing about per-epoch derivations beyond note and key
equality. In `canonicalAppend` the single-step half restates the guard's
`InsertionFacts` conjunct; the segment half is the content. The
cross-proof binding of extension spec 407-409 (the spend proof's and the
insertion proof's nullifier lists are equal) is simplification 4 of
`Pool/Epoch.lean`, assumed, not proved.

`Step` uses `ChainFacts` and `InsertionFacts` directly.
`VerifierSoundness` names a possible implementation assumption, but is
not a premise of these six theorems. No verifier correspondence
theorem is supplied.

## What the base rows mean

- Theorems 2 and 3 are the claim. Theorem 1 follows from the
  guards alone.
- Theorems 4 to 9 are supporting results about the same model, in three
  groups. Accounting: theorems 4 to 7. Authorization: theorem 8. Event
  semantics: theorem 9. Value conservation does not imply theorems 8 and 9.
- `spendRequiresOwnerKey` states owner-key binding at the model level
  only. Key secrecy and signature custody (spec line 308; line 463) are
  out of the model (L4B.lean docstring). Two spec theft routes are out of
  model under simplification 7: a deposit against another address's
  allowance (342-343) and a relayer redirecting the withdraw recipient
  (369).
- Live value counts the unspent notes that the pool minted. A note that a
  nullifier collision locks still counts as live.
- `doubleSpendExhibitsCollision` (L3.lean) is a definition, not a proved
  theorem. It gives the reduction reading of theorem 2: a double spend
  exhibits a collision among the history's own notes or keys. The
  inventory lists it so that the gate checks its type.

## What the theorems rest on

- The model in `LeanShieldedPool/Pool/`, with the 16 base
  simplifications and the epoch limits in SPEC-MAP.md. They are
  modelling choices. Some are encoded in the guards; none is a
  separately quantified hypothesis of any theorem. No definition has an
  implementation-correspondence theorem in this repo.
- `CryptoHyp`, where the table says so.
- Three Lean axioms: `propext`, `Classical.choice` and `Quot.sound`
  (AXIOMS.md). The gate checks the axioms of each theorem.

**Which guard conjuncts the proofs use.** The proofs consume membership,
nullifier freshness and distinctness, owner-key binding, token
consistency, the transfer sum equation, output-commitment freshness, the
deposit duplicate check, and the withdraw payout bound. The base proofs
also use the `U128` range conjuncts: they establish well-formed notes
(`Run.runNotes_wf`) before applying the restricted `CryptoHyp`. The
epoch base-case proof transports the range and root-window conjuncts
into the accepted base run it constructs. Beyond that transport, no
theorem consumes the root-window conjuncts; they keep the model's
accepted set aligned with the contract. None of this verifies concrete
root-window code or machine arithmetic; root-window correctness and
range enforcement are not among the claims. The root-window conformance
bug fixed in pocs-private#12 is an example of a bug these theorems
cannot see.

## Checks that the theorems have content

- `Draft/NonVacuity.lean` shows on a toy instance that each operation
  guard can fire, so `Run` is not empty. `Pool/Epoch.lean` also
  supplies epoch guard witnesses, including a spend after rollover and
  rejection of a repeated spend; row 15 states the former for every
  accepted run.
- The positive controls apply all fifteen theorems to concrete toy
  instances. `controls/positive_l3.lean` proves `CryptoHyp` for the
  deposit-transfer-withdraw run, and `controls/positive_l5.lean` proves
  the epoch `CryptoHyp` for an accepted run that crosses a rollover,
  plus a no-rollover prefix for row 14's premise, so the conditional
  theorems apply to nonempty accepted histories. For rows 11 and 12 it
  also instantiates the conclusions at concrete antecedents: the
  rollover inside that run with the epoch-1 withdrawal as the suffix,
  the transfer as a non-rollover step, and the no-rollover prefix as a
  segment; for row 15, the first transfer output after that prefix and
  its rollover.
- Each refutation control weakens one guard, post-state or replay step.
  It carries a history that the mutated model accepts, shows that the
  history meets the frozen Prop's other premises (`CryptoHyp` where the
  Prop has it), and proves the negation of the frozen Prop restated over
  the mutated model. For event replay the run is the real one and the
  replay function is the mutated part. The file must build, so an
  unrelated unsolved goal in its setup cannot be mistaken for success.
  `controls/refute_l3_double_spend.lean` states the three parts as
  three theorems; the eleven others end in one theorem that negates a
  universal statement over the mutated model (for replay: over the real
  `Run`, with the lossy replay). None claims the negation of an
  original theorem, which quantifies over the real `Run` or the real
  epoch model.
- The gate rejects a positive or refutation control whose build reports
  a `sorry`, and any axiom declared in a control. It runs no axiom census
  on control theorems.

REVIEW.md part 6 lists what the theorems do not say.
