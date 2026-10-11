# Review guide

Find where the claim is wrong, too strong or unclear. This is not an
audit.

## 1. What is claimed

> In a Lean 4 model of spec 2/SHIELDED-POOL (sections 4-6, revision 4d4dce1), the protocol rules imply that no note spends twice and that value is conserved per token, from an empty pool over every accepted history, under one hypothesis: among the notes and keys that appear in that history, no two distinct notes with `u128` amounts share a commitment and no two distinct spending keys derive the same public key. Machine-checked with the three standard Lean axioms only. Whether the model says what the spec says is a human reading, still open.

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

- No implementation is verified (client, circuits, contract).
- No privacy claim.
- No recursive-proof or concrete nullifier-tree verification. The six
  L5 claims concern the PoC extension's semantic model, separately from
  spec 2.
- No cross-epoch claim for ballast: a zero-amount second input skips the
  chain check, as in the circuit (CLAIMS.md, "Ballast and the chain
  check").
- No conservation or event replay result for arbitrary epoch runs.
- The research repo's toy and smoke theorems are not here.
- The root-window bug in the contract is not a claim of this repo (part 7).
- The spec reading is human and still open (part 5).

## 3. How to check

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
git clone git@github.com:ethsystems/shielded-pool-model.git && cd shielded-pool-model
# Check out the revision under review before continuing.
lake exe cache get          # setup: about 30 minutes (estimate), .lake about 7.5 GB
bash scripts/gate.sh        # expect: GATE PASS (<commit>); 53 s measured
bash scripts/gate_test.sh   # expect: GATE_TEST PASS; 644 s measured
```

The gate tests committed HEAD, so an uncommitted tree is not a gate
result. The 53 s gate time is one cold build of this branch with a
copied Mathlib cache; the 644 s fixture time is one run of the 18
fixtures, on Linux with btrfs, no memory cap, `LEAN_NUM_THREADS=4`,
while another Lean build ran on the same machine.
Without cheap file copies, set `GATE_WORK` to a directory on APFS,
btrfs or XFS.

The gate builds a fresh clone of HEAD. It rejects `sorry`, `native_decide`
and unlisted axioms, in the controls too. It checks the exact type and
axioms of the 29 inventory names, runs the controls, and checks the pins last.
`gate_test.sh` plants 18 cheats; each must make the gate fail.

## 4. Trust base

- The Lean 4.33.1 kernel.
- Mathlib at 0df444a and eight transitive packages (`lake-manifest.json`),
  as prebuilt oleans.
- Three axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The gate script and the pins. The pins are hashes at the local HEAD.
  They bind an untrusted worker, not the maintainer, who can re-pin.
- Your own build.

## 5. The hypothesis and the 16 simplifications (Track A)

Does the model say what the spec says? No machine can check this. Oskar
has read the statements against the spec. Track A is the second pair of
eyes.

1. Read spec 2 sections 4-6 at the model's revision:
   `git -C <specs-private> show 4d4dce1:specs/2/README.md`. SPEC-MAP line
   numbers refer to it.
2. Read SPEC-MAP.md. The 16 simplifications are modelling choices, not
   hypotheses.
3. Read `Statements/L3.lean`, `L4.lean` and `L4B.lean` with CLAIMS.md.

Questions:

- Does any simplification hide a real attack or failure mode?
- Do the statements match what spec 6.2 guarantees? Spec 6.2 marks no
  double spend and value conservation as "tested". Should it say
  "machine-checked (model)" after this review?
- Is `CryptoHyp` (no commitment or key collision within one history) the
  right hypothesis, or too strong?
- Two spec clauses disagree. 4.2 pads the second input. 5.3 lets any
  zero-amount input skip membership. The model now follows 4.2 and the
  reference circuit (simplification 11), and a spec change is proposed
  that makes 5.3 say the same. Is 4.2 the rule you intend?

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

They say nothing about the verifier, concrete Merkle implementations,
encoded amounts, deployed caller and authorization behavior,
re-entrancy, overflow, governance, privacy, or deployed code. A nullifier
collision can lock a note, and locked value counts as live.
`spendRequiresOwnerKey` is owner-key binding at the model level only; key
secrecy and custody are out of the model.

## 7. Work in progress

A private exploratory repo (lean-shielded-pool) uses the same model.
It links the model to the Rust client
(Aeneas, Verus), the Noir circuits (Lampe, ACIR) and the Solidity
contract (Halmos, Lean over Yul), and it has privacy games. Each link is
partial, bounded or conditional, and this repo claims none of them. A
bounded check against the root-window rule that the spec and the model
share found one conformance bug in the contract, fixed in
https://github.com/ethsystems/pocs-private/pull/12. This gate does not
reproduce that check.

## 8. How to report

Open an issue in this repo. Tag it with the theorem or
simplification number, a severity (wrong, too strong, unclear, nit) and
a file:line. Oskar answers each issue himself.
