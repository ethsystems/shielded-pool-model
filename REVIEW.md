# Review guide

Find where the claim is wrong, too strong or unclear. This is not an
audit.

## 1. What is claimed

> In a Lean 4 model of spec 2/SHIELDED-POOL (sections 4-6, revision 4d4dce1), the protocol rules imply that no note spends twice and that value is conserved per token, from an empty pool over every accepted history, under one hypothesis: among the notes and keys that appear in that history, no two distinct notes share a commitment and no two distinct spending keys derive the same public key. Machine-checked with the three standard Lean axioms only. Whether the model says what the spec says is a human reading, still open.

| Theorem | English | Spec clause | Hypothesis |
|---|---|---|---|
| `nullifierUniqueness_proof` | no nullifier repeats | 5.2 | none |
| `noDoubleSpend_proof` | no commitment is consumed twice | 6.2 (441) | `CryptoHyp` |
| `valueConservation_proof` | deposited = withdrawn + live, per token | 6.2 (442) | `CryptoHyp` |
| `poolSolvency_proof` | balance + withdrawn = deposited | 4.4 | none |
| `noOverWithdrawal_proof` | withdrawn never exceeds deposited | 6.2 | none |
| `noMinting_proof` | live value never exceeds deposited | 6.2 | `CryptoHyp` |
| `balanceIsLiveValue_proof` | balance = live value | 4.4, 6.2 | `CryptoHyp` |
| `noTheft_proof` | owner-key binding: the witness key owns each consumed note | 5.3 (319, 348, 365) | `CryptoHyp` |
| `eventReplayFaithful_proof` | log replay rebuilds the tree and the nullifier set | 4.4 (275-279) | none |

## 2. What is not claimed

- No implementation is verified (client, circuits, contract).
- No privacy claim.
- No epoch claim (L5). Its source is the PoC extension spec, not spec 2.
- The research repo's toy and smoke theorems are not here.
- The root-window bug in the contract is not a claim of this repo (part 7).
- The spec reading is human and still open (part 5).

## 3. How to check

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
git clone --branch model-v1 <this repo> shielded-pool-model && cd shielded-pool-model
lake exe cache get          # setup: about 30 minutes (estimate), .lake about 7.5 GB
bash scripts/gate.sh        # expect: GATE PASS (<commit>); 37 s measured
bash scripts/gate_test.sh   # expect: GATE_TEST PASS; 206 s measured
```

`<this repo>` is the GitHub URL once the repo exists. Branch `model-v1`
holds the model until the PR merges. The 37 s gate time is one cold build
with a copied Mathlib cache. The fixture time is from two runs, 206 s
each, on Linux with btrfs. Without cheap file copies, set `GATE_WORK` to
a directory on APFS, btrfs or XFS.

The gate builds a fresh clone of HEAD. It rejects `sorry`, `native_decide`
and unlisted axioms. It checks the exact type and axioms of the 19
inventory names, runs the controls, and checks the pins last.
`gate_test.sh` plants 11 cheats; each must make the gate fail.

## 4. Trust base

- The Lean 4.33.1 kernel.
- Mathlib at 0df444a and eight transitive packages (`lake-manifest.json`),
  as prebuilt oleans.
- Three axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The gate script and the pins. The pins are hashes at the local HEAD.
  They bind an untrusted worker, not the maintainer, who can re-pin.
- Your own build.

## 5. The hypothesis and the 15 simplifications (Track A)

Does the model say what the spec says? No machine can check this. Oskar
has read the statements against the spec. Track A is the second pair of
eyes.

1. Read spec 2 sections 4-6 at the model's revision:
   `git -C <specs-private> show 4d4dce1:specs/2/README.md`. SPEC-MAP line
   numbers refer to it.
2. Read SPEC-MAP.md. The 15 simplifications are modelling choices, not
   hypotheses.
3. Read `Statements/L3.lean`, `L4.lean` and `L4B.lean` with CLAIMS.md.

Questions:

- Does any simplification hide a real attack or failure mode?
- Do the statements match what spec 6.2 guarantees? Spec 6.2 marks no
  double spend and value conservation as "tested". Should it say
  "machine-checked (model)" after this review?
- Is `CryptoHyp` (no commitment or key collision within one history) the
  right hypothesis, or too strong?
- Two spec clauses seem inconsistent. 4.2 pads the second input. 5.3 lets
  any zero-amount input skip membership. The model follows 5.3
  (simplification 11). Which one does the spec intend?

## 6. What the theorems do not say

They say nothing about the verifier, concrete Merkle implementations,
encoded amounts, deployed caller and authorization behavior,
re-entrancy, overflow, governance, privacy, or deployed code. A nullifier
collision can lock a note, and locked value counts as live. `noTheft`
is owner-key binding at the model level only; key secrecy and custody
are out of the model.

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
