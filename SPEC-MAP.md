# Clause map: base pool and epoch extension

Base model status: the author has read its model and statements against
spec 2. Track A in REVIEW.md is the second reading.

Base source of truth: spec 2 at ethsystems/specs-private 4d4dce1 (`specs/2/README.md`;
the staged copy `2-SHIELDED-POOL.md` the model was written from is
byte-identical). Line numbers are that file's.
Spec main (72414f4) adds the commitment-seen set in 5.2 and shifts later
line numbers. This map stays pinned to 4d4dce1 until the 6.2 row change
lands; the repin then remaps every line citation in one commit.
Model files: `LeanShieldedPool/Pool/State.lean`, `LeanShieldedPool/Pool/Tx.lean`,
`LeanShieldedPool/Statements/L3.lean`, `LeanShieldedPool/Draft/NonVacuity.lean`.

## Definition to clause

| Lean definition | Spec clause | Lines |
|---|---|---|
| `maxU128`, `U128` | amount width `u128`; every amount witness range-checked; contract rejects public amounts at or above `2^128` | 5.1 (299), 5.3 (325-328) |
| `rootWindow = 100` | "A window of 100 roots is RECOMMENDED" | 4.4 (262) |
| `PrimSpec.derivePub` | `spending_pubkey = Poseidon1(spending_key)` | 5.1 (290) |
| `PrimSpec.commit` | `commitment = Poseidon4(token, amount, owner_pubkey, salt)` | 5.1 (304) |
| `PrimSpec.nullify` | `nullifier = Poseidon2(commitment, spending_key)` | 5.1 (305) |
| `PrimSpec.Token/Address/PubKey/SpendKey/Salt/Commitment/Nullifier` | note and key field types | 5.1 (288-302) |
| `Note` | `Note { token, amount, owner_pubkey, salt }` | 5.1 (297-302) |
| `Note.cm` | commitment of a note | 5.1 (304) |
| `Note.wf` | amount inside the note amount width | 5.3 (325-328) |
| `Note.isBallast` | ballast derived in-circuit from `amount == 0`, never a free selector | 5.3 (356-359) |
| `Note.ownedBy` | `owner_pubkey == Poseidon1(spending_key)`, one key witness for both inputs | 5.3 (348, 319-320) |
| `Note.nf` | the nullifier that spends a note | 5.1 (305), 5.3 (351) |
| `St.minted` (ghost) / `St.leaves` | commitment tree: append-only, positional insertion order | 5.2 (312), 4.2 step 6 (234) |
| `St.window`, `St.pushWindow` | bounded historical-root window; only the root after the final insertion of an operation enters it | 4.4 (260-263) |
| `St.rootInWindow` | contract accepts proofs against any root in the window | 4.4 (260-261) |
| `St.inTreeAt` | "member of the tree at the public commitment root" | 5.3 (350, 366) |
| `St.nullifiers`, `St.fresh` | nullifier set, append-only; nullifier unspent | 5.2 (313-314), 4.2 step 5 (233), 4.3 step 4 |
| `St.balance` | ERC-20 held by the pool per token | 4.1 step 6, 4.3 step 5 |
| `St.supported` | supported-token set | 5.2 (315), 4.4 (266) |
| `St.deposited`, `St.withdrawn` (ghost) | accounting for the value-conservation statement | 6.2 (442) |
| `St.empty` | pool before any operation | - |
| `St.wf` | window bound, snapshots inside the tree, no duplicate leaf, no duplicate nullifier, amounts in range | 4.4 (260-264), 5.3 (325) |
| `St.spent` | a note is spent when its commitment is in `spentCms` | 6.2 (441) |
| `St.spentCms` (ghost) | commitments consumed by accepted spends; the circuit binds each nullifier to its input commitment | 6.2 (441), 5.3 (351, 367) |
| `Tx.consumes` | the input commitments an operation consumes | 5.3 (348-351, 366-367) |
| `liveValue`, `noteValue` | value still inside the pool, for the conservation statement | 6.2 (442) |
| `DepositData` | deposit public inputs: commitment, token, amount, funding address | 5.3 (331-341) |
| `DepositData.guard` | supported token; `amount != 0`; `u128` range; commitment not already in the tree | 4.4 (264-270), 5.3 (325-328) |
| `DepositData.post` | append the commitment, record the new root, pull tokens | 4.1 steps 5-6 (200-203), 4.4 (263) |
| `TransferData` | transfer public inputs: two nullifiers, two output commitments, root | 5.3 (347) |
| `TransferData.nf1`, `.nf2` | "each public nullifier equals `Poseidon2(commitment_in, spending_key)`" | 5.3 (351) |
| `TransferData.guard` | root in window; both inputs under one key; membership for the first input and for the second unless it is ballast; both nullifiers unspent and distinct; token consistency; per-amount range checks; value conservation; no duplicate insertion. The former `U128 (in1 + in2)` conjunct is dropped: `Nat` sums never wrap, and the bound was stricter than spec 5.3 | 4.2 step 5 (233), 4.4 (260-264), 5.3 (348-359) |
| `TransferData.post` | mark both nullifiers spent, append both outputs in public-input order, record the new root | 4.2 step 6 (234) |
| `WithdrawData` | withdraw public inputs: nullifier, token, amount, recipient, root | 5.3 (362, 365-369) |
| `WithdrawData.nf` | `nullifier == Poseidon2(commitment, spending_key)` | 5.3 (367) |
| `WithdrawData.guard` | root in window; membership; owner key; nullifier unspent; `amount != 0`; `u128`; payout bound (modelling device, simplification 16; not a spec clause) | 4.3 step 4 (255), 4.4 (270), 5.3 (365-369) |
| `WithdrawData.post` | mark spent, transfer tokens out; nothing inserted, so no new root | 4.3 step 5 (256), 4.4 (263) |
| `Tx`, `Tx.spends` | the three protocol operations and the nullifiers each consumes | 4.1-4.3 (174-257) |
| `Step` | one accepted operation; a failed guard reverts and is not a step | 4.1-4.3, 4.4 |
| `Reachable` | states reachable from an empty pool | - |
| `Run` | a full accepted history from an empty pool | - |
| `runNotes`, `runKeys`, `CryptoHyp` | run-scoped collision-freedom of `Poseidon4` commitments (for `u128`-bounded notes) and `Poseidon1` key derivation, stated as named hypotheses, never axioms | 5.1 (290, 304), 5.3 (325-328) |
| `spentCommitments`, `noteSpentAtMostOnce` | "A note spends at most once", at the commitment level the chain sees | 6.2 (441) |
| `valueConservation` | "No transfer creates or destroys value", conditional on `CryptoHyp` | 6.2 (442), 5.3 (353) |
| `noDoubleSpend` | "A note spends at most once", conditional on `CryptoHyp` | 6.2 (441), 4.2 step 5 (233) |
| `nullifierUniqueness` | nullifier uniqueness from the guards alone; the former `noDoubleSpend`, kept as a lemma | 5.2 (313-314) |
| `doubleSpendExhibitsCollision` | reduction reading: a double spend exhibits a hash collision among the run's own witnesses | 6.2 (441) |
| `Event`, `Tx.event`, `events` | operation events carrying commitments and nullifiers, transfer outputs in public-input order; no note or key witnesses; encrypted payloads out (simpl. 8) | 4.1 step 6 (201-202), 4.2 step 6 (234), 4.3 step 5 (256), 4.4 (279) |
| `replayStep`, `replay`, `replayLeaves`, `replayNullifiers` | "events MUST carry enough data for a client to reconstruct the commitment tree and spent set from logs alone" | 4.4 (279) |
| `spendRequiresOwnerKey` | spending authorization binds to the note's owner key; one spending-key witness feeds both derivations; key secrecy out of model | 5.3 (319, 348, 365), spec 463 |
| `eventReplayFaithful` | honest bookkeeping: log replay reconstructs the commitment tree and nullifier set; timing vs external calls out (simpl. 9) | 4.4 (279) |
| `NonVacuity.*` | witnesses that each guard is satisfiable, so the statements are not vacuous | - |
| `d.note.cm ∉ st.leaves`, `out cm ∉ st.leaves` (guard conjuncts) | duplicate check; spec main adds the commitment-seen set that answers it on-chain | 4.4 (264); 5.2 at 72414f4 (322-323) |

## The 16 simplifications

Every item is a deliberate abstraction. Each is a review point.

Scope: in a Lean 4 model of spec 2/SHIELDED-POOL (sections 4-6, revision
4d4dce1), the protocol rules imply that no note spends twice and that
value is conserved per token, from an empty pool over every accepted
history, under one hypothesis: among the notes and keys that appear in
that history, no two distinct notes with `u128` amounts share a
commitment and no two distinct spending keys derive the same public key. That hypothesis is
`CryptoHyp`, scoped to one history. The 16 items below are modelling
choices. Some are encoded in the guards; none is a separately quantified
hypothesis of any theorem. No definition has an
implementation-correspondence theorem in this repo, so the proofs give no
evidence about the implementation of any item. Where an item below speaks
of an assumption, a soundness requirement, or a token behavior that voids
a guarantee, it describes implementation correspondence: what a deployment
must satisfy for the model to describe it. It is never a premise of a
proved theorem. No implementation behavior can invalidate a theorem about
the model.

1. **No proof system.** The proof statements of Section 5.3 are modelled as
   guards over the witnesses (notes, keys, salts) carried in the transaction
   data. The model assumes the verifier is sound and the circuit constrains
   exactly what the guard says. Verifier soundness, UltraHonk, and the
   normative public-input order (5.3, 372) are out of the model.
2. **Merkle tree to an ordered list; root to a prefix length.** The
   append-only tree (5.2, 312) is `List Commitment` in insertion order, and a
   historical root is the leaf count it commits to. "Membership at a windowed
   root" is membership in `leaves.take snapshot`. This drops LeanIMT, dynamic
   depth, `MAX_DEPTH = 32`, the `proof_length <= MAX_DEPTH` range check, and
   the rule that the two transfer inputs must not share one length (5.3,
   322-323). It assumes concrete roots bind ordered leaves. That is an
   obligation on the implementation, not a premise of any theorem here.
   The model also seeds the window with the empty-tree root; the
   reference contract registers no root until the first operation. The
   model accepts histories the contract rejects; for the universally
   quantified theorems this is strictly more general.
3. **Amounts are `Nat` with a side condition.** `U128 n` is `n <= 2^128 - 1`,
   not a 128-bit vector. `Nat` never wraps, so the model cannot exhibit the
   overflow-minting bug of 5.3 (325-328). The former `U128 (in1 + in2)`
   guard conjunct is dropped: it was stricter
   than the spec's per-amount checks and rejected spec-valid transfers.
   Each amount is still individually range-checked, and the proofs use
   those checks to establish well-formed notes for the restricted
   hypothesis. A bitvector model would make the overflow bug reachable. The
   circuit's checked `u128` additions also reject a transfer whose input
   or output sum exceeds `2^128 - 1`; the model accepts such transfers
   since the sum-range conjunct was dropped. The model is weaker than
   the circuit here, which is conservative for the universally
   quantified theorems.
4. **Hashes are opaque with no properties.** `PrimSpec` declares `commit`,
   `nullify` and `derivePub` and asserts nothing about them: no collision
   resistance, no injectivity, no hiding. Deliberate, so no assumption hides
   inside a definition. Consequence: a single `commit` value can stand for
   two different notes, and a ballast note can collide with a real one. Both
   conservation and double-spend proofs will need injectivity hypotheses.
   None is an axiom. The hypotheses are stated: `CryptoHyp` in `Statements/L3.lean`, scoped to
   the notes and keys of one run, not to the hash's whole domain.
5. **Ghost state.** `St.minted` keeps the note behind each leaf,
   `St.deposited` / `St.withdrawn` are running totals, and `St.spentCms`
   records each consumed input commitment. On-chain,
   only the commitments exist. The ghost fields exist to state the two
   guarantees; they must never appear in a guard. Check that no guard
   reads them (none does today, `spentCms` included).
6. **Field-element hygiene is absent.** The rule that the contract must
   reject any field-typed public input at or above the field modulus (4.4,
   271-272), which blocks the `nullifier + p` double-spend, cannot be stated:
   nullifiers are an opaque type with no encoding.
7. **No deposit authorisation.** The funding address is carried as data, but
   `msg.sender == funding_address` or the signature form (5.3, 342-344) is
   not modelled: the model has no caller and no signatures. Withdraw's
   `recipient` is likewise data only.
8. **Payload and encryption are out; events are modelled.** No encrypted
   note, no payload commitment, no payload binding (4.4, 268-269), and no
   recipient recompute check (4.2 step 3). Events are modelled
   (`LeanShieldedPool/Pool/Events.lean`); `eventReplayFaithful_proof` shows
   log replay rebuilds the commitment tree and the nullifier set.
9. **Reentrancy and ordering are out.** Insertion-before-external-call (4.4,
   275-276) and non-reentrancy (4.4, 278) have no counterpart: `Step` is atomic.
   These rules cannot be violated in the model, so the model gives no
   evidence about them.
10. **Governance is frozen.** `St.supported` is fixed at pool creation and no
    step changes it. Token removal that must not block existing transfers and
    withdrawals (4.4, 266) is therefore modelled only by the fact that
    transfer and withdraw guards never read `supported`. Verifier mutability
    and owner powers (6.1) are out.
11. **Ballast is the second input only.** The model follows 4.2 (208) and
    the reference circuit: input 0 is always membership-checked, and only
    input 1 may skip membership when its amount is zero
    (transfer/src/main.nr:106-131 at pocs-private a04b8b3). 5.3 (356-358)
    derives ballast from `amount == 0` alone and does not restrict the
    slot, so the two readings disagree; a spec change is proposed that
    makes 5.3 match 4.2. First-slot membership does not remove zero-value
    notes from the tree: transfer outputs may be zero-value and enter it
    as real leaves.
12. **Privacy guarantees are not stated.** Confidentiality, unlinkability and
    selective disclosure (6.2) need an observer model, which this repo does
    not have. It states no privacy result. CLAIMS.md lists the nine base
    integrity results and six epoch results.
13. **`open Classical`.** Used so per-token maps and `liveValue` can branch on
    undecidable propositions. It makes `bump`, `drop` and `liveValue`
    noncomputable. No axiom is declared; `Classical.choice` is already
    allowed by `AXIOMS.md`.
14. **Transfer arity fixed at 2-in-2-out**, per 4.2 (207). Variable arity is
    out, as the spec says.
15. **Tokens are credited at face value.** The spec excludes fee-on-transfer
    and rebasing tokens from the supported set (4.4, 267). The model relies
    on that exclusion: `deposited` and `balance` credit the stated amount.
    A supported token that violates the exclusion is outside what the model
    describes; the theorem itself stands. The exclusion is an ongoing
    obligation: a token that changes behavior after listing breaks it
    silently, and no on-chain check enforces it; a spec issue proposes a
    per-deposit balance-delta check, which narrows the deposit side of
    that exposure.
16. **The withdraw guard carries a payout bound.** `d.note.amount <=
    st.balance` is not a clause of 4.3 or 4.4: 4.3 step 4 (255) checks the
    proof and the nullifier only. It is a model assumption about token
    transfer semantics, with a conventional ERC-20 rationale: the withdraw
    transfer (checks-effects-interactions, ShieldedPool.sol:286) does not
    complete when the pool balance is short, so the accepted operation set
    matches for tokens with standard revert behavior. The unconditional
    `poolSolvency` and `noOverWithdrawal` proofs use this conjunct
    (TierA.lean:29-32). The existing solvency control removes membership
    and the payout bound together, so it does not isolate this guard.

## L5: epoch extension

L5 has a separate source: `ethsystems/pocs-private`,
`pocs/private-payment/shielded-pool-extension/SPEC.md`.
Its SHA-256 is
`a05e86a53a00725486c319f3ca40b35bd77db954bc4b3c1b233085ec7e6a5da0`.
The line numbers below refer to that exact file.

The file at revision `a04b8b38969dfc2ee64de47edee7e396454204a8` matches
that hash, and `Pool/Epoch.lean` names that verified revision. The
extension export originally recorded revision
`94e30f3f0b9fb4a3ba0d0a3b220c49c075c42672`, which is not available in
the local spec checkout; the hash is the file's identity.

Names below are relative to `LeanShieldedPool.Epoch`.
These are semantic interpretations of the clauses, with the limits below.

| Lean definition or theorem | Extension spec clause | Lines |
|---|---|---|
| `PrimSpec.commitE`, `Note.epochCreated`, `Note.cm` | Data Types: extended note and commitment | 84-100 |
| `PrimSpec.nfE`, `Note.nfE` | Data Types: extended nullifier | 102-108 |
| `St.currentEpoch`, `St.active`, `St.frozen`, `St.rollover` | On-Chain State: active state and sealing at rollover | 139-167 |
| `ChainFacts`, `SpendGuard` | Full lifetime coverage, with the current epoch checked separately | 125-135, 167, 365-374 |
| `AppendFresh`, `InsertionFacts`, `TransferData.nullifiers` | Sequential insertion and equality of ordered nullifier lists | 161, 167, 394-409 |
| `DepositData.guard`, `TransferData.guard`, `WithdrawData.guard` | Parent guards plus creation epoch, frozen history and active insertion checks. The chain check is skipped for a zero-amount second input, following the circuit, not 358-366 (simplification 7) | 51-60, 358-374 |
| `Verifiers`, `VerifierSoundness` | Abstract extraction of chain and insertion facts | 37-41, 324-338, 394-409 |
| `Candidates.CryptoHyp` | Run-scoped commitment and owner-key binding, including creation epoch | 99, 336, 372 |
| `Tx.valueConsumes`, `crossEpochNoDoubleSpend_proof` | Guarantees: cross-epoch double-spend safety, for inputs with nonzero amount; ballast is excluded because its chain check is skipped | 436 |
| `frozenRootImmutability_proof` | Preserve sealed contents after rollover. Line 163 says only what a rollover writes; 205 calls sealed data immutable. Immutability of sealed entries is a model choice | 163, 205 |
| `canonicalAppend_proof` | Preserve exact append order and sequential freshness. The single-step half restates the guard conjunct; the segment half is the content. Cross-proof binding (407-409) is simplification 4, assumed | 161, 167, 394-405 |
| `chainKeyBinding_proof` | One owned note and key across consuming witnesses. The chain key binding of 336-337 is assumed (simplification 2) | 366, 372 |
| `epochZeroRefinesBase_proof`, `Candidates.basePrim`, `Candidates.BaseStateMatches` | Translate an initial-epoch run to the parent rules, one way; no recursive-verifier claim and not the circuit's base case | 47-62 |
| `spendableAfterRollover_proof` | A clear-history note stays spendable after rollover (model liveness); notes created in the current epoch already satisfy the chain condition | 436 (second sentence), 267 |
| `Examples.*` | Concrete guard witnesses and rejected repeat attempts | model checks, no spec clause |

The base map and its 16 simplifications still apply to the base model
(`Pool/State.lean`, `Tx.lean`, `Events.lean`) and the statements L3, L4
and L4B.
The epoch model retains their amount, ownership, ballast and accounting
abstractions. It adds these limits:

- Frozen and active nullifier trees are lists. There are no authenticated
  roots, predecessor pointers, Merkle paths or encoded leaf slots.
- `ChainFacts` supplies non-membership over the entire lifetime directly.
  There are no proof bytes, recursive witnesses, accumulator transitions
  or checks against a deployed verifier.
- One supplied key covers the chain interval. The model does not prove
  that separate recursive circuits bind their keys to that same key.
- `InsertionFacts` supplies exact order and sequential freshness. It does
  not verify a concrete tree update or public-input encoding.
- Epochs are unbounded `Nat`. Rollover is atomic, with no clock or caller.
  The model does not establish `u64` bounds or authorization. Liveness is
  stated at the model level only (`spendableAfterRollover`): the guard
  admits the step; nothing is said about relayers, proofs or tokens.
- A zero-amount second input (ballast) passes the transfer guard without a
  chain check and with an unconstrained creation epoch, as in the circuit.
  Row 10 counts only value-bearing consumption; row 14 assumes epoch-0
  ballast (`Candidates.BallastStamped`).
- `EpochDistinct` is defined but unused by these six theorems. Hash
  collisions can reject valid spends without violating at-most-once safety.
- The base reduction fixes hashes at epoch zero and compares nullifier
  lists by permutation. The parent prepends batches; the epoch model appends.
- Epoch conservation, epoch event replay, PIR, privacy, storage bounds
  and proof costs are not proved here. The nine base theorems retain their
  original scope.
