# Claims

The fifteen claimed theorems (nine base, six epoch) and five root-window
results, each with its Lean name, English, spec clause and hypothesis.
The statement files `LeanShieldedPool/Statements/L3.lean`, `L4.lean`,
`L4B.lean`, `L5.lean` and `Window.lean` are the source of truth. The
gate checks the type of each name against `statements/INVENTORY.md`.
These fifteen are the repo's claim; the root-window results and the
gated k-anonymity extension are supporting material, not further claims.

## How to read a row

Each claim is a Prop, such as `noDoubleSpend`, and a theorem that proves
it for every `P : PrimSpec` (the opaque hashes and field types), such as
`noDoubleSpend_proof`. Each base Prop covers every accepted history:
`Run sup txs st` says that the operations `txs` run from the empty pool
and reach the state `st`. Spec clauses refer to spec 2 at 4d4dce1
(`specs/2/README.md` in ethsystems/specs); numbers in brackets
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
membership for the first input, as the base guard does. The L5
statements of rows 10 to 14 come from an earlier version of the
model. Review changed four of them: the consumption statement
of row 10, the immutability premise of row 11, the binding clause of
row 13 and the refinement statement of row 14. Row 12 keeps its source
text. Row 15 was added here. The model admits fewer histories than the
pre-repin version did, and row 14 targets the revised base `CryptoHyp`.

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
extension spec and the circuit became a one-paragraph spec exception on
2026-10-13, after the extension spec file this repo pins; if the
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

## The five root-window theorems

Stated in `Statements/Window.lean`, proved in `Proofs/Window.lean`, over
the base model (not the epoch model). Issue #2 asked for the boundary
and liveness results. They are supporting results, not part of the
nine-theorem claim. Spec clauses refer to spec 2 at 4d4dce1.

| # | Lean name | English | Spec clause | Hypothesis |
|---|---|---|---|---|
| 16 | `windowBoundary_proof` | Every window entry is 0 (the empty tree) or the leaf count of the state after some nonempty accepted prefix of the same history. This is the half "intermediate roots do not" enter: it bounds what can enter, and a model that never pushes a root satisfies it. | 4.4 (260-263) | none |
| 17 | `windowHead_proof` | After every accepted history, the newest window entry is the current leaf count. This is the half "the root recorded after the final insertion of each operation enters the window". | 4.4 (263) | none |
| 18 | `noMidTransferRoot_proof` | For every accepted transfer in a history, the leaf count between its two inserts is not in the window at the end of the history. Proved from row 16 and the leaf count of a history (one insert per deposit, two per transfer, none per withdrawal; `Run.leaves_length`). | 4.4 (263) | none |
| 19 | `honestWithdrawWindow_proof` | For any root in the window, the owner of a note that the pool minted before that root (the ghost `minted` list behind the tree), with a fresh nullifier, a nonzero amount and enough pool balance, has an accepted withdrawal against that root, and the pool balance drops by exactly the amount. The commitment's membership at that root and the `u128` range are derived, not assumed. | 4.3 step 4 (255), 4.4 (260-261), 5.3 (365-369) | none; token set frozen (simplification 10) |
| 20 | `honestWithdraw_proof` | Row 19 at the current root: the owner of a note that the pool minted, with a fresh nullifier, a nonzero amount and enough pool balance, has an accepted withdrawal against the current root, and the pool balance drops by exactly the amount. Window membership of the current root (row 17), the commitment's membership at that root and the `u128` range are derived, not assumed. | 4.3 step 4 (255), 4.4 (260-261), 5.3 (365-369) | none; token set frozen (simplification 10) |

Rows 16 and 18 are model evidence for the bug class that
ethsystems/pocs commit a04b8b3 fixed: the control `controls/refute_window_intermediate.lean`
makes the transfer also record its between-insert root and proves the
negations of both; the weak bound "every entry is at most the leaf
count" still holds on the same counterexample history, so the boundary
form is the one with content. The control
`controls/refute_honestwithdraw_norecord.lean` (a deposit that does not
push its root) proves the negations of rows 17 and 20. In the model the
current root is accepted only through the window. The contract also
accepts it directly (`isKnownRoot`, `ShieldedPool.sol:314` at
ethsystems/pocs a04b8b3), so that control checks the model's push, not the
contract. The control `controls/refute_honestwithdraw_currentroot.lean`
(a withdraw guard that accepts only the current root, as a contract
without the window lookup at `ShieldedPool.sol:315` would) proves the
negation of row 19: it rejects a withdrawal against an older root that
is still in the window. Rows 16 to 18 say nothing about zero or repeated
hash roots (an open issue in the private implementation repository), exact eviction, or the contract. Rows 19
and 20 are model liveness: the model accepts the step and debits the
pool's per-token field; there is no recipient balance and no ERC-20 in
the model. The balance premise stays a premise. None of the five has a
positive control; the three refutation controls are their content check.

**Token removal.** Rows 19 and 20 hold in a model whose supported-token
set never changes and whose withdraw guard does not read it
(simplification 10). Spec 2 says that removing a token must not block
withdrawals of existing notes (4.4, 266). The contract at ethsystems/pocs
a04b8b3 does not meet this: `withdraw` reverts with `UnsupportedToken`
when the token is no longer supported (`ShieldedPool.sol:254`). So the
liveness of rows 19 and 20 does not carry over to the contract after the
owner removes a token. This is a deviation of the contract from the
spec; the model does not show it.

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
deposit duplicate check, the withdraw payout bound, and the `U128` range
conjuncts: `Step.notes_wf` and `Run.runNotes_wf` extract well-formedness
from the range checks, and every proof that applies
`CryptoHyp.commit_inj` passes those facts to it: no double spend
(`Proofs/NoDoubleSpend.lean:125`, `:131`, `:143`), value conservation and
its private helpers (`Proofs/Conservation.lean:23`, `:166`, `:183`,
`:202`), and owner-key binding (`Proofs/TierB.lean:31-32`). No minting
and balance equals live value call value conservation and inherit the
dependency (`Proofs/TierAConditional.lean`). The epoch base-case proof
transports the range and root-window conjuncts into the accepted base
run it constructs. Beyond that transport, and beyond row 15, which
discharges the epoch model's window conjunct through its own
`Run.window_head` (`Proofs/Epoch.lean`), none of the fifteen theorems
consumes the root-window conjuncts; they keep the model's accepted set
aligned with the contract. Rows 16 to 20 are the base results that
read the window: rows 16 to 18 state what the window contains, row 19
discharges the withdraw guard's range conjunct from `Run.runNotes_wf`
and takes the window root as a premise, and row 20 discharges the
window conjunct at the current root from row 17. None of this verifies
concrete root-window code or machine arithmetic; root-window correctness
of the contract and range enforcement are not among the claims. The
root-window conformance bug fixed in ethsystems/pocs a04b8b3 is the bug class
that the control of rows 16 and 18 reproduces in the model; the
theorems still cannot see the contract's code.

## Checks that the theorems have content

- `Draft/NonVacuity.lean` shows on a toy instance that each operation
  guard can fire, so `Run` is not empty. `Pool/Epoch.lean` also
  supplies epoch guard witnesses, including a spend after rollover and
  rejection of a repeated spend; row 15 states the former for every
  accepted run.
- The base and epoch positive controls apply all fifteen theorems to
  concrete toy instances; `controls/positive_k_anonymity.lean` applies
  the extension's frozen names to its own toys.
  `controls/positive_l3.lean` proves `CryptoHyp` for the
  deposit-transfer-withdraw run, and `controls/positive_l5.lean` proves
  the epoch `CryptoHyp` for an accepted run that crosses a rollover,
  plus a no-rollover prefix for row 14's premise, so the conditional
  theorems apply to nonempty accepted histories. For rows 11 and 12 it
  also instantiates the conclusions at concrete antecedents: the
  rollover inside that run with the epoch-1 withdrawal as the suffix,
  the transfer as a non-rollover step, and the no-rollover prefix as a
  segment; for row 15, the first transfer output after that prefix and
  its rollover.
- Each base, epoch or window refutation control changes one guard,
  post-state or replay step.
  It carries a history that the mutated model accepts, shows that the
  history meets the frozen Prop's other premises (`CryptoHyp` where the
  Prop has it), and proves the negation of the frozen Prop restated over
  the mutated model. For event replay the run is the real one and the
  replay function is the mutated part. The file must build, so an
  unrelated unsolved goal in its setup cannot be mistaken for success.
  `controls/refute_l3_double_spend.lean` states the three parts as
  three theorems. `controls/refute_window_intermediate.lean` and
  `controls/refute_honestwithdraw_norecord.lean` each negate two frozen
  Props over one mutation; the first also proves `weak_holds`, which
  shows that the weak bound holds on the same counterexample history.
  The twelve others end in one theorem that negates a universal
  statement over the mutated model (for replay: over the real `Run`,
  with the lossy replay).
  None claims the negation of an original theorem, which quantifies over
  the real `Run` or the real epoch model.
- The extension's refutation controls (below) mutate a frozen definition
  instead of a guard: one drops the injectivity of the atom renamings,
  one deletes the last-owner equation of the anonymity-set definition.
  Each proves the negation of a frozen universal restated over its
  mutation and must build, like the base controls.
- The gate rejects a positive or refutation control whose build reports
  a `sorry`, and any axiom declared in a control. Its text check rejects
  `native_decide`, its synonyms (`decide +native`, `(native := true)`)
  and direct use of `ofReduceBool` or `ofReduceNat` in the model,
  statement and control files. It runs no axiom census on control
  theorems.

REVIEW.md part 6 lists what the theorems do not say.

## Extension: symbolic k-anonymity

`LeanShieldedPool/Extensions/KAnonymity.lean` is gated supporting
material: same frozen pins, census rows (the 22 extension names in
`statements/INVENTORY.md`), axiom rules and controls as the core, but
not one of the fifteen claims above.

**The observer.** The observer sees the ordered `Event` log and nothing
else. It does not see these on-chain fields: the deposit token, amount
and funding address (331), the withdraw token, amount and recipient
(362), the commitment root (347, 460) and the payload commitments. It
also sees no encrypted payloads and no network or timing data. Spending
and viewing keys are not on-chain, so no observer sees them. This is
weaker than the public observer of spec 6.1 (424), which sees all
on-chain state and traffic. The threats of 6.1 (424-426) and 6.3
(455-461) are out of scope here; in particular a compromised viewing
key shows the owner of `out1` directly. Spec 6.1 is context for the
file, not a proved match to its observer.

**The relation.** `ObsEquiv` relates two logs when injective renamings
of commitment atoms and nullifier atoms map one to the other.
Constructors, slot order and repeated atoms stay observable; on finite
logs injections and permutations give the same relation
(`obsEquiv_iff_permutations`), and the relation is an equivalence.

**The target.** The protected attribute is the owner of the first
output of the last transfer (`lastTransferFirstOwner`). Not every
recipient, not a withdrawal address, not every accepted log. In both
toys every explanation in the proved families has the same spend key,
input owner and `out2` owner; only the owner of `out1` varies, so those
families give the sender and the change owner an anonymity set of
size 1. `explanations` itself does not fix those fields, and no theorem
bounds them. The phrase "anonymity set" also
differs from the spec's: in spec 458-459 it is pool traffic, and a
quiet pool gives weak anonymity; here it is a set of possible recipient
keys, and `ManyRecipientToy.candidate` gives any k from a pool with one
deposit and one transfer, so this count is not the spec's traffic-based
set.

**What is proved.** `hasAnonymitySet sup log k` asks for k injectively
distinct accepted explanations of `log` (each an accepted run with its
own `CryptoHyp`, observationally equivalent to `log`) whose targets are
pairwise distinct. `acceptedAnonymityCandidate` is an existence
statement: some accepted history reaches a k-member family. It gives no
universal anonymity lower bound, and k = 0 is vacuous by design; a
one-candidate set establishes no ambiguity. Two positive families are
proved, and they are distinct results:

- The two-recipient toy (`candidate_two`): both worlds share one
  primitive profile with the owner-binding commitment
  `Nat.pair owner salt`, only output owners and salts vary, and symbolic
  equivalence of the two logs is proved through an explicit commitment
  permutation (`perm01`). Collision freedom also holds
  across both histories' combined witnesses
  (`crypto_cross_history`); that concatenation is a witness
  collection, not an accepted run.
- The k-recipient family (`ManyRecipientToy.candidate`), for every
  positive finite k: the primitive profile `Toy' k` varies with k, its
  commitment binds the owner (`Nat.pair owner salt`), the output salts
  vary with the world, and the k logs are pairwise symbolically
  equivalent through an explicit commitment permutation
  (`pairwise_obs`, `cmPerm`). Collision freedom holds within each
  history (`crypto`) and across any two histories' combined witnesses
  (`crypto_cross_history`). The toys' `commit` is still not a hash:
  `Nat.pair owner salt` binds the owner and the salt but ignores the
  token and the amount, so two notes with the same owner and salt
  collide. Collision freedom is proved for the witness histories named
  above, not in general.

**A limit of `explanations`.** An explanation matches the log only up
to `ObsEquiv`, and `Event` carries no token, amount, address or root.
So two explanations can withdraw different public amounts to different
recipients, or deposit different public amounts, and both count as
members. Spec 455-456 names exactly those fields as the linking
surface, so for a log with deposits or withdrawals `hasAnonymitySet`
can count more members than the spec observer allows. The toys do not
show this: they use `Unit` tokens and addresses and have no withdraw.
The follow-up is to require each explanation to match the public fields
of deposits and withdrawals and the snapshot. It is not done here.

**The counterexample.** Key and salt cardinalities alone do not give
the candidate: with a constant commitment function no transfer guard
can fire (`constant_commit_blocks_transfer`), so the cardinality-only
implication is false at every positive count
(`not_cardinalityOnlyCandidate`).

**The hypothesis.** `HashHidingHyp` names the assumption that a chosen
real observer cannot distinguish symbolically equivalent logs. The
symbolic results above do not need it; only the bridge to a chosen
observer does (`indistinguishable_under_hiding`). No real cryptographic
hiding instance is proved. The extension proves no Poseidon hiding
bound and no deployed-privacy property. The toys' `commit` and
`nullify` are not hashes; collision freedom is checked per history via
`CryptoHyp`. The counting is possibilistic: it counts possible targets
and assigns no probabilities or equal likelihood. Only a relation at
least as coarse as `ObsEquiv` can satisfy `HashHidingHyp`:
`CannotDistinguish := Eq` fails, because `deposit_obsEquiv` relates two
deposits with different commitment values. Real hiding is a statement
about distributions over salts, not about two fixed logs, so no observer
that sees actual values can satisfy the hypothesis as stated. The
protected owner is also inside the note ciphertext that the sender
encrypts to the recipient's viewing key (spec 2 line 230), so a real
bridge needs key privacy of that encryption as well. This file does not
model that encryption.

## Separate packages

Ten packages outside the gate, each with its own check and trust base.
Five hold Lean theorems (the first table):
[hash-agreement/](hash-agreement/README.md),
[circuits-acir/](circuits-acir/README.md),
[circuits-lampe/](circuits-lampe/README.md),
[refinement/](refinement/README.md) and
[privacy-games/](privacy-games/README.md). Five are tool checks (the
second table): [verifier-reproduction/](verifier-reproduction/README.md),
[deployment/](deployment/README.md),
[contract-halmos/](contract-halmos/README.md),
[contract-kontrol/](contract-kontrol/README.md) and
[client-verus/](client-verus/README.md). None of them changes a claim above. Each package
README states its claim, its trust base and what stays open.

| Package | Lean names | English | What it narrows | Hypothesis |
|---|---|---|---|---|
| `hash-agreement/` | `noirPermute_eq_plainPerm`, `noirHash2_eq_plainHash2`, `solHashSeg_eq_plainHash2`, `solHashSeg_eq_noirHash2` | Over the BN254 scalar field, the Noir, plain and segmented Solidity transcriptions of the two-input Poseidon hash (Poseidon2 in the spec's naming: x^5, t = 3, 65 rounds) agree as functions of the two inputs; the Noir and plain permutations also agree on every state. Standard axioms only. | No simplification of the model: `PrimSpec.nullify` stays opaque, and no theorem links it to these definitions. Evidence for the implementation side of the membership guard (simplifications 1 and 2): the contract (`PoseidonT3` in LeanIMT) and the circuits (`hash_2`) hash Merkle nodes with the same function. Not collision resistance: `CryptoHyp` stays as it is. The transcriptions, the monolithic-to-segmented Solidity cut, the Lampe link and EVM semantics stay open (its README). | none |
| `circuits-acir/` | `AcirLean.Deposit.amount_lt_two_pow_128`, `AcirLean.Withdraw.amount_lt_two_pow_128`, `AcirLean.Transfer.amount_ranges`, `AcirLean.Transfer.conservation`, `AcirLean.Transfer.token_consistency`, and `satisfiable` for each circuit | Every assignment that satisfies the compiled ACIR constraints (AssertZero and RANGE) of the deposit, withdraw and transfer circuits at ethsystems/pocs `a04b8b3` keeps each amount below 2^128; in transfer, the two input amounts sum to the two output amounts over the naturals, with no u128 wrap, and the four token fields are equal. Each circuit has a kernel-checked satisfying witness. Standard axioms only. | No simplification of the model. Evidence for the circuit side of three guard conjuncts that the proofs consume: the `U128` range, the transfer sum equation and token consistency. Not the contract's checks, Brillig execution, the extractor or the ABI allocation, compiler or prover soundness, or the deployed verifier (its README). The pin predates ethsystems/pocs `748884e`, which changed the transfer circuit. | none |
| `circuits-lampe/` | `Deposit.Commitment.accepting_main_commitment_eq`, `Deposit.AttestationRoot.accepting_main_attestation_root`, `Withdraw.Nullifier.accepting_main_withdraw_rules`, `Withdraw.Root.accepting_main_withdraw_root`, `Transfer.Rules.accepting_main_transfer_rules`, `Transfer.Root.accepting_main_transfer_root`, `Merkle.Fold.bmr_fwd`, `Poseidon.Permutation2.perm`, `Poseidon.Permutation5.perm`, `Poseidon.Hash2.perm3w`, and the `*_nonvacuous` theorems | For every accepting execution of the complete extracted `main` of the deposit, withdraw and transfer circuits at ethsystems/pocs `a04b8b3`, under the semantics of a patched Lampe (the fork `oskarth/lampe`, pinned by commit) over BN254: the deposit commitment is `hash4 token amount (ownerKey key) salt`; both transfer inputs use the owner key of the one spending key, both nullifiers are `hash2 commitment key`, and each output commitment encodes its note; the withdraw commitment uses the public token and amount and the owner key, and its nullifier is `hash2 commitment key`; each checked Merkle root is the fold of its leaf along the path, with depth bounds 20 (deposit), 32 and 32; the extracted Poseidon permutations compute their pure functions. Each circuit has an accepting execution that meets the premises. Standard axioms only. | No simplification of the model: `PrimSpec` stays opaque, and no theorem links it to these definitions. Evidence for the circuit side of the hash-bound guard conjuncts (commitment, owner key, nullifier, membership root), from the Noir source. Not the compiled ACIR: the Noir compiler stays trusted on this route; `circuits-acir/` covers the ranges and the sum from the constraints, and no theorem links the two. Not Poseidon's cryptographic properties, the verifier, the contract or deployed code. Trusts Lampe's semantics at the fork commit and its extractor (its README). The pin predates ethsystems/pocs `748884e`, which changed the transfer circuit. | none |
| `refinement/` | `refineP_run`, `refinePL_run`, `refine_run`, `accepted_root_provenance`, `refineB_w9`, `refineB_run`, `Journey.withdraw_journey_of_history`, `LeanImt.complete_mem`, `LeanImt.binding_mem_or_bad`, `FoldBridge.merkleRoot_val`, `FoldBridge.withdraw_member_or_bad`, `FoldBridge.transfer_member_or_bad`, `GasEnvelope.byte_envelope`, and the toy instances | For an abstract contract (uninterpreted success, revert and verifier relations) and any hash, every accepted history with no `setVerifier` call refines a run of the gated model, under named premises: contract posts on reachable states, rollback, circuit facts, per-history extraction (A2), tree premises and `CryptoHyp`. The money theorems then hold for that run, and every root the contract accepts is the LeanIMT root of a prefix of the leaves. The LeanIMT insertion matches the circuit's Merkle fold, with membership or a named bad event. Under token premises, the pool's external balance bounds the model's balance and every admitted withdrawal. The gas arithmetic bounds canonical arguments under the 2^24 cap at most 2,941,344 bytes. Standard axioms only; imports the gated model unchanged. | No simplification of the model. A conditional composition only: no concrete execution, no production instantiation of any premise, no token effects or events. The posts, the `imtInsert` transcription and the storage layout are readings of `ShieldedPool.sol` at `a04b8b3`. The toy instances show only that the premises can hold together (its README). | every premise named in its README |
| `privacy-games/` | `RecipientGame.Rejection.advantage_le`, `ChainGame.advantage_le_delta`, `WithdrawGame.ROM.advantage_le_queryBound`, `OwnerGame.ROMCommit.advantage_le_queryBound`, `SenderGame.ROMCommit.advantage_le_queryBound`, `RecipientGame.CommitOnly.advantage_le_rom_collisions`, `ChainGame.CommitOnly.advantage_le_rom_collisions` (all under `LeanShieldedPool.`); the counterexamples `ChosenWorldGame.Counterexample.transported_bound_false` and `WithdrawGame.Toy.toy_zero_error_bound_false`; the funded examples (`RecipientGame.Rejection.Fixture.rejection_eq_five_eighths`, `RecipientGame.CommitOnly.Funded.privacy_bound`, `RecipientGame.CommitOnly.TwoFunded.privacy_bound`, `ChainGame.CommitOnly.FundedChain.small_bounds`) | In two-world games run through the model's guards, where the observer sees only the ordered commitment and nullifier log (and the public keys in the honest-key games), the attacker's advantage is bounded: for the recipient of static transfers and of fixed chains under commitment hiding and spread premises; for the withdrawn note, the deposit owner and the transfer sender under a random-oracle premise for the named hash uses, with honest challenger-sampled keys; for the recipient with only the commitment idealized. Each bound keeps a rejection term. Two proved counterexamples refute weaker premises, and funded toy witnesses show that the bounds are not vacuous in those models. Standard axioms only. | No simplification of the model: the games import `Pool/State.lean`, `Tx.lean` and `Events.lean` unchanged, pinned by hash. Not a deployed-privacy claim: no Poseidon instantiation of any premise; the random-oracle premise is a heuristic; the rejection terms of the random-oracle games have no numeric bound; interactive attackers, adaptive corruption and later key or salt disclosure are open; proofs, roots, payloads, timing and network data are outside every game (its README). | the premises named in each statement |

`verifier-reproduction/`, `deployment/`, `contract-halmos/`, `contract-kontrol/` and `client-verus/` are tool checks, not Lean theorems: a build reproduction, a deployment check, Halmos checks and Kontrol proofs about the contract source, and Verus checks of client mirrors:

| Package | Claim | Checked by | Not claimed |
|---|---|---|---|
| `verifier-reproduction/` | The three Solidity verifiers committed in ethsystems/pocs at `a04b8b3` (public) are bb's output for the three committed circuits, byte for byte, and bb's key hash for each equals the committed `VK_HASH` (nargo 1.0.0-beta.21, bb 5.0.0-nightly.20260324). | `verifier-reproduction/check.sh`: a rebuild from the pocs submodule at `a04b8b3` and a byte comparison, 9 s | Proof-system soundness (that an accepted proof implies a satisfying witness), that a deployed contract is compiled from these sources, the pool contract, that nargo and bb translate the circuits faithfully, and the transfer circuit after ethsystems/pocs `748884e` (2026-10-08). It never says "the verifier is correct". |
| `deployment/` | At Sepolia block 11949456, the runtime code at the 12 claimed addresses (pool, composite, registry, three Honk verifiers, their three `ZKTranscriptLib` libraries, LeanIMT, PoseidonT3, PoseidonT5) equals a fresh offline build of ethsystems/pocs `a04b8b3` (forge 1.8.3, solc 0.8.37), with links and immutables filled, nothing masked and the metadata tails equal (any difference is a FAIL); the composite slots hold the verifiers with their own `VK_HASH`, no slot holds mock code, the pool emitted no `VerifierUpdated` log and exactly one `OwnershipTransferred` log, to the claimed owner, and the (empty) token set matches the claim. The same holds at block 11976486 (2026-10-23). | `deployment/check.sh <rpc> deployment/claims/sepolia.json`: dependencies fetched and checked by hash, a rebuild in a network namespace with no network, then a comparison through the RPC, about 10 s; `--controls` runs the unchanged claim as a baseline and six planted deviations, each of which must fail at exactly its named checks | Anything after the claimed block, token or owner behaviour, verifier or proof-system soundness, the correctness of the contracts, the mock token of the deployment (not in the claim), and the RPC, which is trusted with its history. |
| `contract-halmos/` | Within the scope line of each of its nine suites, Halmos 0.3.3 finds no counterexample to the stated property of `ShieldedPool.sol` at ethsystems/pocs `a04b8b3` (forge 1.8.3, solc 0.8.37, the two libraries linked at fixed addresses), and each named mutant gives one: the guards before the verifier revert with their own errors and no state change; a duplicate leaf and a call under the reentrancy lock revert with no state change, with no tree-depth bound; on every successful withdrawal from a symbolic caller the nullifier is marked before the one payout `transfer(recipient, amount)` on the named token, and the verifier sees `[nullifier, token, amount, recipient, root]`; the five owner functions reject other callers and change only their stated state; the ring records the final root of each operation; each postcondition field holds on every successful call; the root window accepts only post-operation roots. | `contract-halmos/check.sh`: the export from the pocs submodule with blob checks, one Foundry project per suite, every check, mutant and forge replay compared with `EXPECTED.tsv` | The deployed contract; proof, payload and calldata shapes other than those listed; tree depths outside each suite's band; the real Poseidon where a suite uses the keccak stub; the production verifiers, the real registry and any real token (the mocks move no balances); gas; Halmos's own model, which is trusted. It never says "the contract is correct". |
| `contract-kontrol/` | Under KEVM's semantics in Kontrol 1.0.255 (an image pinned by digest), for the bytecode that solc 0.8.37 builds from `ShieldedPool.sol` at ethsystems/pocs `a04b8b3`, each within its stated scope: the 13 guards before the verifier revert with their own errors for a symbolic caller and byte lengths 0..2^30, and the four withdraw guards for proof lengths below 2^64 (a patched KEVM `abi.md`); on every successful withdrawal with a token argument above 0x11 and a fixed caller, the nullifier is marked before the one payout `transfer(recipient, amount)` on the named token, and the verifier sees `[nullifier, token, amount, recipient, root]`; every public input that reaches the verifier is below the field modulus, and deposit and transfer pass their inputs in the circuits' order; the LeanIMT insert rejects out-of-field, zero and duplicate leaves. A Halmos check shows that the pinned PoseidonT3 library is a pure function. Named mutants fail at stated outputs. | `contract-kontrol/check.sh`: the export with blob checks, the Kontrol builds and proofs in the pinned container, the forge replays and the concrete loop controls, every verdict and failing output compared with `EXPECTED.tsv`; the K claims of the insertion loop are packaged but not run, and the `public-inputs` runs were not rerun in the recorded run of 2026-10-24 | Any deployment or the contract as a whole; a symbolic caller on the success path; token addresses 0x00 to 0x11; non-canonical calldata; gas; token movement (A10) and proof binding (A2); deposit and transfer with a nonempty symbolic proof and a symbolic payload together; the real Poseidon in the insertion loop. It trusts KEVM, the patched `abi.md` and one bytes-prefix rule. |
| `client-verus/` | For 96 of the 110 security-relevant functions of the shielded-pool client at ethsystems/pocs `a04b8b3` (`src/lib/`), a selected property (the `ensures` clause of a reviewed Verus mirror of the function) holds under named parameter contracts: Verus 0.2026.09.13.671956e verifies the 15 mirror files with `--no-cheating`, each mirrored function differs from its hash-pinned source region exactly as its recorded diff shows, and each of the 96 has a negative control that Verus refutes (241 controls: 239 refuted by Verus, 2 stopped at the solver's resource limit on rows 65 and 66, which each have a second refuted control). The other 14 functions, and the Aeneas half of the 8 on both routes, rest on Aeneas results taken from the client coverage report of 2026-10-01, which is not in this repo (Aeneas 22, Verus 96, both 8, union 110). | `client-verus/check.sh`: source pins and diffs, Verus on every mirror, probe and control, the coverage arithmetic, about 100 s | The compiled client and production equivalence; effects (RPC, chain, processes, files, channels, scheduling); the libraries behind the 23 parameter interfaces (A3); Poseidon, keccak and curve properties; the 22 Aeneas results, which are not re-checked; functions outside the 110. It never says "the client is verified". |
