# Clause map: Lean model to 2/SHIELDED-POOL

Status: the author has read the model and the statements against the
spec. Track A in REVIEW.md is the second reading.

Source of truth: spec 2 at ethsystems/specs-private 4d4dce1 (`specs/2/README.md`;
the staged copy `2-SHIELDED-POOL.md` the model was written from is
byte-identical). Line numbers are that file's.
Model files: `LeanShieldedPool/Pool/State.lean`, `LeanShieldedPool/Pool/Tx.lean`,
`LeanShieldedPool/Statements/L3.lean`, `LeanShieldedPool/Draft/NonVacuity.lean`.

## Definition to clause

| Lean definition | Spec clause | Lines |
|---|---|---|
| `maxU128`, `U128` | amount width `u128`; every amount witness range-checked; contract rejects public amounts at or above `2^128` | 5.1 (297), 5.3 (325-328) |
| `rootWindow = 100` | "A window of 100 roots is RECOMMENDED" | 4.4 (262) |
| `PrimSpec.derivePub` | `spending_pubkey = Poseidon1(spending_key)` | 5.1 (290) |
| `PrimSpec.commit` | `commitment = Poseidon4(token, amount, owner_pubkey, salt)` | 5.1 (304) |
| `PrimSpec.nullify` | `nullifier = Poseidon2(commitment, spending_key)` | 5.1 (305) |
| `PrimSpec.Token/Address/PubKey/SpendKey/Salt/Commitment/Nullifier` | note and key field types | 5.1 (288-302) |
| `Note` | `Note { token, amount, owner_pubkey, salt }` | 5.1 (294-299) |
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
| `DepositData.post` | append the commitment, record the new root, pull tokens | 4.1 steps 5-6 (200-204) |
| `TransferData` | transfer public inputs: two nullifiers, two output commitments, root | 5.3 (344-346) |
| `TransferData.nf1`, `.nf2` | "each public nullifier equals `Poseidon2(commitment_in, spending_key)`" | 5.3 (351) |
| `TransferData.guard` | root in window; both inputs under one key; membership unless ballast; both nullifiers unspent and distinct; token consistency; per-amount range checks; value conservation; no duplicate insertion. The former `U128 (in1 + in2)` conjunct is dropped: `Nat` sums never wrap, and the bound was stricter than spec 5.3 | 4.2 step 5 (233), 4.4 (260-264), 5.3 (348-359) |
| `TransferData.post` | mark both nullifiers spent, append both outputs in public-input order, record the new root | 4.2 step 6 (234) |
| `WithdrawData` | withdraw public inputs: nullifier, token, amount, recipient, root | 5.3 (362, 365-369) |
| `WithdrawData.nf` | `nullifier == Poseidon2(commitment, spending_key)` | 5.3 (367) |
| `WithdrawData.guard` | root in window; membership; owner key; nullifier unspent; `amount != 0`; `u128`; pool solvent for the payout | 4.3 step 4 (255), 4.4 (270), 5.3 (365-369) |
| `WithdrawData.post` | mark spent, transfer tokens out; nothing inserted, so no new root | 4.3 step 5 (256), 4.4 (263) |
| `Tx`, `Tx.spends` | the three protocol operations and the nullifiers each consumes | 4.1-4.3 (174-257) |
| `Step` | one accepted operation; a failed guard reverts and is not a step | 4.1-4.3, 4.4 |
| `Reachable` | states reachable from an empty pool | - |
| `Run` | a full accepted history from an empty pool | - |
| `runNotes`, `runKeys`, `CryptoHyp` | run-scoped collision-freedom of `Poseidon4` commitments and `Poseidon1` key derivation, stated as named hypotheses, never axioms | 5.1 (290, 304) |
| `spentCommitments`, `noteSpentAtMostOnce` | "A note spends at most once", at the commitment level the chain sees | 6.2 (441) |
| `valueConservation` | "No transfer creates or destroys value", conditional on `CryptoHyp` | 6.2 (442), 5.3 (353) |
| `noDoubleSpend` | "A note spends at most once", conditional on `CryptoHyp` | 6.2 (441), 4.2 step 5 (233) |
| `nullifierUniqueness` | nullifier uniqueness from the guards alone; the former `noDoubleSpend`, kept as a lemma | 5.2 (313-314) |
| `doubleSpendExhibitsCollision` | reduction reading: a double spend exhibits a hash collision among the run's own witnesses | 6.2 (441) |
| `Event`, `Tx.event`, `events` | operation events carrying commitments and nullifiers, transfer outputs in public-input order; no note or key witnesses; encrypted payloads out (simpl. 8) | 4.1 step 6 (201-202), 4.2 step 6 (234), 4.3 step 5 (256), 4.4 (279) |
| `replayStep`, `replay`, `replayLeaves`, `replayNullifiers` | "events MUST carry enough data for a client to reconstruct the commitment tree and spent set from logs alone" | 4.4 (279) |
| `noTheft` | spending authorization binds to the note's owner key; one spending-key witness feeds both derivations; key secrecy out of model | 5.3 (319, 348, 365), spec 463 |
| `eventReplayFaithful` | honest bookkeeping: log replay reconstructs the commitment tree and nullifier set; timing vs external calls out (simpl. 9) | 4.4 (275-279) |
| `NonVacuity.*` | witnesses that each guard is satisfiable, so the statements are not vacuous | - |

## The 15 simplifications

Every item is a deliberate abstraction. Each is a review point.

Scope: in a Lean 4 model of spec 2/SHIELDED-POOL (sections 4-6, revision
4d4dce1), the protocol rules imply that no note spends twice and that
value is conserved per token, from an empty pool over every accepted
history, under one hypothesis: among the notes and keys that appear in
that history, no two distinct notes share a commitment and no two
distinct spending keys derive the same public key. That hypothesis is
`CryptoHyp`, scoped to one history. The 15 items below are modelling
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
3. **Amounts are `Nat` with a side condition.** `U128 n` is `n <= 2^128 - 1`,
   not a 128-bit vector. `Nat` never wraps, so the model cannot exhibit the
   overflow-minting bug of 5.3 (325-328). The former `U128 (in1 + in2)`
   guard conjunct is dropped: it was stricter
   than the spec's per-amount checks and rejected spec-valid transfers.
   Each amount is still individually range-checked. A bitvector model
   would make the bug reachable and the guards load-bearing.
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
   `msg.sender == funding_address` or the signature form (5.3, 337-341) is
   not modelled: the model has no caller and no signatures. Withdraw's
   `recipient` is likewise data only.
8. **Payload and encryption are out; events are modelled.** No encrypted
   note, no payload commitment, no payload binding (4.4, 268-269), and no
   recipient recompute check (4.2 step 3). Events are modelled
   (`LeanShieldedPool/Pool/Events.lean`); `eventReplayFaithful_proof` shows
   log replay rebuilds the commitment tree and the nullifier set.
9. **Reentrancy and ordering are out.** Insertion-before-external-call (4.4,
   277-279) and non-reentrancy (4.4) have no counterpart: `Step` is atomic.
   These rules cannot be violated in the model, so the model gives no
   evidence about them.
10. **Governance is frozen.** `St.supported` is fixed at pool creation and no
    step changes it. Token removal that must not block existing transfers and
    withdrawals (4.4, 266) is therefore modelled only by the fact that
    transfer and withdraw guards never read `supported`. Verifier mutability
    and owner powers (6.1) are out.
11. **Ballast rule applied to both slots.** The spec pads the *second* input
    (4.2). The model lets either input be ballast, since the real rule is
    `amount == 0` (5.3, 358). This is weaker than the spec's shape and is a
    review point.
12. **Privacy guarantees are not stated.** Confidentiality, unlinkability and
    selective disclosure (6.2) need an observer model, which this repo does
    not have. It states no privacy result; the nine integrity results of
    `statements/INVENTORY.md` are the whole claim set (CLAIMS.md).
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
    describes; the theorem itself stands.
