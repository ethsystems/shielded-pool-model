# shielded-pool-model

Ethereum Systems writes specs for confidential payment systems. Spec
2/SHIELDED-POOL (`specs/2/README.md` in ethsystems/specs-private) is the
ungated shielded-pool core. Its section 6.2 marks each guarantee as
asserted, tested or machine-checked; today "no double spend" and "value
conservation" are marked "tested". This repo holds the candidate for
"machine-checked (model)" on those two rows: a small Lean 4 model of the
spec's rules, the proofs, and a gate that re-checks them with one command.
It is made to be read whole in an afternoon.

This repo makes one claim.

## The claim

> In a Lean 4 model of spec 2/SHIELDED-POOL (sections 4-6, revision 4d4dce1), the protocol rules imply that no note spends twice and that value is conserved per token, from an empty pool over every accepted history, under one hypothesis: among the notes and keys that appear in that history, no two distinct notes share a commitment and no two distinct spending keys derive the same public key. Machine-checked with the three standard Lean axioms only. Whether the model says what the spec says is a human reading, still open.

The hypothesis is `CryptoHyp` in `LeanShieldedPool/Statements/L3.lean`.
It covers one history only. It says nothing about Poseidon outside that
history, and it is not a Poseidon security claim.

The repo proves nine theorems. Three are about the core model: nullifier
uniqueness, no double spend and value conservation. Six are supporting
results about the same model: solvency, no over-withdrawal, no minting,
balance equals live value, owner-key binding (`noTheft`) and event replay.
CLAIMS.md gives each one with its hypothesis and spec clause.

The model makes 15 simplifications, for example a list for the Merkle
tree, `Nat` amounts and opaque hashes. They are modelling choices, not
hypotheses. SPEC-MAP.md lists them and maps each definition to its spec
line.

## Where it comes from

The model was written and proved in a private research repo,
oskarth/lean-shielded-pool, in September 2026. That repo also links the
same model to the real code: the Rust client (Aeneas, Verus), the Noir
circuits (Lampe, ACIR) and the Solidity contract (Halmos, Lean over Yul),
and it holds privacy games. Every one of those links is partial, bounded
or conditional, and none is claimed here. One result from that work is
worth knowing: a bounded check of the contract against the root-window
rule that the spec and this model share found a conformance bug, fixed in
ethsystems/pocs-private pull request 12. This repo does not reproduce that
check.

## How it was built

A controller session released small bounded tasks to AI workers from two
model families (Claude and GPT). The controller re-checked each result,
and a session from the other family judged it, before it counted. The
gate (below) makes the outcome independent of that process: it rejects
`sorry`, undeclared axioms and statement edits, so a reader trusts the
Lean kernel and the pinned statements, not the workers. Oskar directed the
work and read the statements against the spec. The review is the second
pair of eyes: Track A asks whether the model says what the spec says.

## What the theorems do not say

Nothing about the SNARK verifier, the concrete Merkle tree, field
encodings, who may call the contract, re-entrancy, integer overflow,
governance, privacy, or any deployed code. The tree is a list, amounts
are `Nat`, hashes are opaque, steps are atomic: SPEC-MAP.md lists all 15
simplifications, each a review point. A nullifier collision can lock a
note; locked value counts as live. Whether the model says what the spec
says is a human reading, still open.

## Status and the ask

Proofs and gate complete. The spec reading needs a second reader.
Aaryamann Challani and David Núñez are asked to review (REVIEW.md):
Track A, does the model say what the spec says, plus anything wrong, too
strong or unclear. After the review, either the two spec rows move to
"machine-checked (model)" through a spec change, or the claim here
shrinks to what survives. Findings go in issues here; Oskar answers each.

## What comes next

Follow-up pull requests bring in other work one claim unit at a time,
each behind the same gate: the epoch extension (its source is the PoC
extension spec, not spec 2), the claim 1 rule table as a status page, and
the privacy games once their build cost is decided. The implementation
links stay in the research repo as claim records with re-check commands,
because their inputs are private. The repo is private; no license yet.

## Names

The files keep the names they have in the research repo this model comes
from (lean-shielded-pool at commit 67160b1). The 14 Lean files under
`LeanShieldedPool/`, the 13 controls, four gate scripts and three build
files are byte-identical to that commit. `sha256sum -c PROVENANCE.sha256`
checks this. The level names come from that repo:

- L3 is the core model claim (`Statements/L3.lean`).
- L4 holds the accounting results (`Statements/L4.lean`).
- L4B holds authorization and events (`Statements/L4B.lean`).
- `Draft/NonVacuity.lean` is not a draft. It shows that each operation
  guard can fire, so the theorems are not vacuous. The directory keeps its
  old name so the bytes match.

## Reading order

1. README.md (this file).
2. CLAIMS.md: each theorem in Lean and in English.
3. SPEC-MAP.md: each definition against its spec line, then the 15
   simplifications.
4. The model: `LeanShieldedPool/Pool/State.lean`, `Tx.lean`, `Events.lean`.
5. The statements: `LeanShieldedPool/Statements/L3.lean`, `L4.lean`,
   `L4B.lean`, and `statements/INVENTORY.md`.
6. The proofs: `LeanShieldedPool/Proofs/` and `Draft/NonVacuity.lean`.
7. The controls: `controls/`. Each negative control weakens one guard,
   post-state or replay step, and the proof must then fail.
8. The gate: `scripts/gate.sh`.

REVIEW.md is the reviewer guide.

## Re-check

You need git, bash, python3 and about 8 GB of free disk.

```
# setup: about 30 minutes (an estimate, not measured)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
git clone --branch model-v1 git@github.com:ethsystems/shielded-pool-model.git && cd shielded-pool-model
lake exe cache get

bash scripts/gate.sh        # expect: GATE PASS (<commit>); 37 s measured
bash scripts/gate_test.sh   # expect: GATE_TEST PASS; 206 s measured
```

Branch `model-v1` holds the model until the pull request merges.

The gate builds a fresh clone of HEAD. It rejects `sorry`,
`native_decide` and undeclared axioms. It checks the exact type and axioms
of the 19 names in `statements/INVENTORY.md`, runs the controls, and
checks the pins in `statements/FROZEN.sha256`. `gate_test.sh` plants 11
cheats; each must make the gate fail.

The 37 s gate time is one cold build with a copied Mathlib cache. The
206 s fixture time is from two runs, 206 s each. Both ran on a Linux laptop
with btrfs. Each gate run copies `.lake` (about 7.5 GB). Without cheap
file copies, set `GATE_WORK` to a directory on APFS, btrfs or XFS.

AXIOMS.md lists the three allowed axioms: `propext`, `Classical.choice`
and `Quot.sound`. There is no domain axiom.
