# Claims

The nine proved theorems, each with its Lean name, English, spec clause
and hypothesis. The statement files `LeanShieldedPool/Statements/L3.lean`,
`L4.lean` and `L4B.lean` are the source of truth. The gate checks the type
of each name against `statements/INVENTORY.md`.

## How to read a row

Each claim is a Prop, such as `noDoubleSpend`, and a theorem that proves
it for every `P : PrimSpec` (the opaque hashes and field types), such as
`noDoubleSpend_proof`. Each Prop covers every accepted history:
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

## The nine theorems

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

## What the rows mean

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

- The model in `LeanShieldedPool/Pool/`, with the 16 simplifications of
  SPEC-MAP.md. They are modelling choices. Some are encoded in the guards;
  none is a separately quantified hypothesis of any theorem. No definition
  has an implementation-correspondence theorem in this repo.
- `CryptoHyp`, where the table says so.
- Three Lean axioms: `propext`, `Classical.choice` and `Quot.sound`
  (AXIOMS.md). The gate checks the axioms of each theorem.

**Which guard conjuncts the proofs use.** The proofs consume membership,
nullifier freshness and distinctness, owner-key binding, token
consistency, the transfer sum equation, output-commitment freshness, the
deposit duplicate check, and the withdraw payout bound. Two groups are
not used by any theorem: the two root-window conjuncts and the `U128`
range conjuncts. Weakening those leaves all nine theorems provable. They
keep the model's accepted set aligned with the contract; root-window
correctness and range enforcement are not among the nine claims. The
root-window conformance bug fixed in pocs-private#12 is an example of a
bug these theorems cannot see.

## Checks that the theorems have content

- `Draft/NonVacuity.lean` shows on a toy instance that each operation
  guard can fire, so `Run` is not empty.
- The positive controls apply the nine theorems to that toy instance, and
  `controls/positive_l3.lean` proves `CryptoHyp` for the
  deposit-transfer-withdraw run, so the conditional theorems apply to a
  nonempty accepted history.
- Each negative control weakens one guard, post-state or replay step. The
  proof attempt must then fail with "unsolved goals".
- A refutation control goes further: it carries the accepted mutated run
  and proves the explicit negation of the frozen Prop, and the file must
  build, so an unrelated unsolved goal in its setup cannot be mistaken
  for success. `controls/refute_l3_double_spend.lean` is the first one.
  The remaining `neg_*` controls keep the marker check until they are
  converted.

REVIEW.md part 6 lists what the theorems do not say.
