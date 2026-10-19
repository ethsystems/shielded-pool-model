# Review guide

Find where the claim is wrong, too strong or unclear. This is not an
audit. Track A (part 5) asks whether the model says what the spec
says. It closed on 2026-10-19 with two readings; new readers are
welcome.

## 1. What is claimed

> The model covers spec 2/SHIELDED-POOL, sections 4 to 6, at revision
> 4d4dce1. In the model, the protocol rules imply two guarantees: no
> note spends twice, and value is conserved per token. Both hold from
> an empty pool, over every accepted history. One hypothesis is
> assumed, about the notes and keys that appear in that history. No
> two distinct notes with `u128` amounts share a commitment. No two
> distinct spending keys derive the same public key.
> Machine-checked with the three standard Lean axioms only. Whether
> the model says what the spec says is a human reading, not a
> machine check; two readings are done (REVIEW.md, part 5).

| Theorem | English | Spec clause | Hypothesis |
|---|---|---|---|
| `nullifierUniqueness_proof` | no nullifier repeats | 5.2 | none |
| `noDoubleSpend_proof` | no commitment is consumed twice | 6.2 (441) | `CryptoHyp` |
| `valueConservation_proof` | deposited = withdrawn + live, per token | 6.2 (442) | `CryptoHyp` |
| `poolSolvency_proof` | balance + withdrawn = deposited | 4.4 | none |
| `noOverWithdrawal_proof` | withdrawn never exceeds deposited | 6.2 | none |
| `noMinting_proof` | live value never exceeds deposited | 6.2 | `CryptoHyp` |
| `balanceIsLiveValue_proof` | balance = live value | 4.4, 6.2 | `CryptoHyp` |
| `spendRequiresOwnerKey_proof` | owner-key binding: the witness key owns each consumed note | 5.3 (319, 348, 365) | `CryptoHyp` |
| `eventReplayFaithful_proof` | log replay rebuilds the tree and the nullifier set | 4.4 (279) | none |

L5 adds six separate results from the PoC extension spec. CLAIMS.md
lists their exact scope and hypotheses; SPEC-MAP.md gives the source
hash, clauses and epoch limits. The epoch commits pass the gate and the
gate test.

## 2. What is not claimed

- No implementation is verified (client, circuits, contract). The
  separate packages (README, "Separate packages") check selected facts
  about circuits, hash code and verifier builds; they are outside
  Track A and change no claim here.
- No deployed-privacy claim. The symbolic k-anonymity extension
  (`LeanShieldedPool/Extensions/`, CLAIMS.md "Extension") proves
  properties of a symbolic observer relation; no real cryptographic
  hiding instance is proved. It is outside Track A.
- No recursive-proof or concrete nullifier-tree verification. The six
  L5 claims concern the PoC extension's semantic model, separately from
  spec 2.
- No cross-epoch claim for ballast: a zero-amount second input skips the
  chain check, as in the circuit (CLAIMS.md, "Ballast and the chain
  check").
- No conservation or event replay result for arbitrary epoch runs.
- The research repo's toy and smoke theorems are not here, except the
  toy instances inside the k-anonymity extension file.
- The root-window bug in the contract is not a claim of this repo (part 7).
  The five root-window theorems (CLAIMS.md rows 16 to 20) state what
  the model's window contains and that an honest owner can withdraw
  against any window root that covers the note (premises in CLAIMS.md
  row 19); the model's token set never changes
  (simplification 10), and the contract blocks withdrawals of a removed
  token, against spec 4.4 (266). They do not prove exact retention of
  100 roots or anything about the contract (zero and repeated roots are
  an open issue in the private implementation repository).
- The spec reading is human, not machine-checked (part 5).

## 3. How to check

Setup and the gate command are in [README.md](README.md), "Re-check".
The gate builds a fresh clone of committed HEAD, so an uncommitted tree
is not a gate result. It rejects `sorry`, unlisted axioms, and
`native_decide` and its synonyms such as `decide +native`. In the
controls it rejects a `sorry` in the build output, any declared axiom,
and the same `native_decide` text; it runs no axiom census on control
theorems. It checks the exact type and axioms of the 65 inventory
names, runs the controls, and checks the pins last.

The gate has its own test:

    bash scripts/gate_test.sh   # expect: GATE_TEST PASS

`gate_test.sh` plants 26 cheats; each must make the gate fail with the
right marker. The last one is a bad candidate commit gated through
`GATE_REF` while the checked-out HEAD is clean. The test shows that the
gate fails closed on those cheats; it is not a proof that the gate
catches every cheat.

On a Linux laptop with btrfs, no memory cap and `LEAN_NUM_THREADS=2`,
the gate takes about a minute (one fresh clone with a copied `.lake`
cache) and `gate_test.sh` about 21 minutes for the 26 cheats.

## 4. Trust base

- The Lean 4.33.1 kernel.
- Mathlib at 0df444a and eight transitive packages (`lake-manifest.json`),
  as prebuilt oleans.
- Three axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The gate script and the pins. The pins are hashes at the local HEAD.
  They bind an untrusted worker, not the maintainer, who can re-pin.
- Your own build.

## 5. The hypothesis and the 16 simplifications (Track A)

Does the model say what the spec says? No machine can check this.
Track A closed on 2026-10-19 with two human readings:

- Oskar, the author, read the L3 statements, the guards and the
  simplifications against spec 2 on 2026-09-30, from a one-page
  summary. He recorded it as a high-level reading, not a full check.
- The second reader reviewed PR #1 in 32 threads on 2026-10-01 and
  approved it on 2026-10-02. The threads covered the guards in
  `Pool/Tx.lean` (zero-value inputs, `Nat` amounts against field
  wrap-around, the payout check), the state in `Pool/State.lean` (the
  initial root, live value), the L3, L4 and L4B statements and
  `CryptoHyp`, non-vacuity, the controls, `scripts/gate.sh`, the spec
  line citations in SPEC-MAP.md and the two 6.2 rows. The same reader
  reviewed the extensions: PR #5 (epochs, 11 threads) and PR #7
  (k-anonymity, 12 threads) on 2026-10-06, PR #8 (root window, 5
  threads) on 2026-10-13, all approved by 2026-10-14. Each thread in
  these four PRs has an answer from the author.

Neither reading is a proof, and Oskar's was not a full check. Two
questions below have answers. The 6.2 question: yes, the rows may say
"machine-checked (model)" if the level names what the model cannot
show: field overflow, two encodings of one nullifier, circuit wiring
and Merkle binding (simplifications 3, 6, 1 and 2; PR #1 review). The
4.2 versus 5.3 question: the spec now follows 4.2. The questions stay
open for new readers; report as in part 8.

1. Read spec 2 sections 4-6 at the model's revision:
   `git -C <specs> show 4d4dce1:specs/2/README.md` (ethsystems/specs). SPEC-MAP line
   numbers refer to it.
2. Read SPEC-MAP.md. The 16 simplifications are modelling choices, not
   hypotheses.
3. Read `Statements/L3.lean`, `L4.lean`, `L4B.lean` and `Window.lean`
   with CLAIMS.md.

Questions:

- Does any simplification hide a real attack or failure mode?
- Do the statements match what spec 6.2 guarantees? Spec 6.2 marks no
  double spend and value conservation as "tested". Should it say
  "machine-checked (model)" after this review?
- Is `CryptoHyp` (no commitment or key collision within one history) the
  right hypothesis, or too strong?
- Two spec clauses disagree. 4.2 pads the second input. 5.3 lets any
  zero-amount input skip membership. The model now follows 4.2 and the
  reference circuit (simplification 11), and spec main says the same
  since spec commit 6bd4ba1 (2026-10-06); this repo still cites
  4d4dce1. Is 4.2 the rule you intend?

For L5, read the extension clauses in SPEC-MAP.md, then `Pool/Epoch.lean`
and `Statements/L5.lean`. Check these points:

- Does `ChainFacts` cover each epoch from creation up to the current one,
  with current freshness handled by `InsertionFacts`?
- Is exact list preservation the right semantic reading of frozen roots?
- Does the key-binding statement make its witness-level scope clear?
- Does the initial-epoch reduction select the correct hashes and explain
  why nullifier lists match by permutation?
- Are omitted recursion, authenticated roots, encodings and caller checks
  clear enough to prevent an implementation claim?
- Is excluding ballast from row 10 the right reading of the circuit, or
  should the circuit check the chain for a zero-amount input too?
- Does `spendableAfterRollover` state the liveness you expect, with the
  balance as a premise and no payout claim?

## 6. What the theorems do not say

The fifteen claimed theorems and the five root-window results say nothing
about the verifier, concrete Merkle implementations, encoded amounts,
deployed caller and authorization behavior, re-entrancy, overflow,
governance, privacy, or deployed code (the extension's symbolic observer
result is not a privacy claim about any of these either). A nullifier
collision can lock a note, and locked value counts as live.
`spendRequiresOwnerKey` is owner-key binding at the model level only; key
secrecy and custody are out of the model.

## 7. Work in progress

A private research repository uses the same model. It links the model to the Rust client
(Aeneas, Verus), the Noir circuits (Lampe, ACIR) and the Solidity
contract (Halmos, Lean over Yul), and it has privacy games. Each link is
partial, bounded or conditional, and this repo claims none of them.
Separately from those links, Verus proofs of the client's prover input
encoders and public-input array builders live on a separate branch of
the private implementation repository; they prove the byte encoding of the `Prover.toml` inputs and the
public-input array layout only, and are not linked to this model. A
bounded check against the root-window rule that the spec and the model
share found one conformance bug in the contract, fixed in ethsystems/pocs
commit a04b8b3. This gate does not
reproduce that check.

## 8. How to report

Open an issue in this repo. Tag it with the theorem or
simplification number, a severity (wrong, too strong, unclear, nit) and
a file:line. Oskar answers each issue himself.
