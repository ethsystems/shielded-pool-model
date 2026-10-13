# shielded-pool-model

Ethereum Systems writes specs for confidential payment systems. Spec
2/SHIELDED-POOL (`specs/2/README.md` in ethsystems/specs-private) is the
ungated shielded-pool core. Its section 6.2 marks each guarantee as
asserted, tested or machine-checked; today "no double spend" and "value
conservation" are marked "tested". This repo holds the candidate for
"machine-checked (model)" on those two rows: a small Lean 4 model of the
spec's rules, the proofs, and a gate that re-checks them with one command.
It is made to be read whole in an afternoon.

The base claim below is unchanged. L5 adds five results about the
separate PoC epoch extension.

## The claim

> In a Lean 4 model of spec 2/SHIELDED-POOL (sections 4-6, revision 4d4dce1), the protocol rules imply that no note spends twice and that value is conserved per token, from an empty pool over every accepted history, under one hypothesis: among the notes and keys that appear in that history, no two distinct notes with `u128` amounts share a commitment and no two distinct spending keys derive the same public key. Machine-checked with the three standard Lean axioms only. Whether the model says what the spec says is a human reading, still open.

The hypothesis is `CryptoHyp` in `LeanShieldedPool/Statements/L3.lean`.
It covers one history only. It says nothing about Poseidon outside that
history, and it is not a Poseidon security claim.

Two standing abstractions sit under the claim, next to `CryptoHyp`: a
Merkle root stands for the exact leaf list it commits to
(simplification 2), and the verifier and circuit constrain exactly what
the guards state (simplification 1). Neither is a theorem hypothesis;
both are obligations on the implementation.

The base model proves nine theorems. Three are about the core model:
nullifier uniqueness, no double spend and value conservation. Six are
supporting results about the same model: solvency, no over-withdrawal,
no minting, balance equals live value, owner-key binding
(`spendRequiresOwnerKey`) and event replay. L5 adds cross-epoch
no-double-spend for value-bearing inputs, frozen-list immutability,
canonical append, chain key binding, a one-way refinement to the base
pool without rollover, and spendability after rollover. CLAIMS.md
gives all fifteen results with their hypotheses and spec clauses. The
epoch results concern a semantic state machine; they do not verify
recursive proofs or concrete nullifier trees.
`LeanShieldedPool/Extensions/` holds gated extensions outside this core
read; the first is symbolic k-anonymity: possibilistic, over a symbolic
event-log observer, no deployed-privacy claim (CLAIMS.md, "Extension:
symbolic k-anonymity").

Two further results about the historical-root window (spec 2 section
4.4, issue #2) sit outside the fifteen and are gated with them: every
window entry is an operation boundary (`windowBoundary`), and the owner
of a note that the pool minted, with a fresh nullifier, a nonzero amount
and enough pool balance, has an accepted withdrawal at the current root
(`honestWithdraw`). Both are over the base model. No exact-retention
claim and no claim about the contract's window code. Files:
`Statements/Window.lean`, `Proofs/Window.lean`, two refutation controls
under `controls/`, and their rows in CLAIMS.md and SPEC-MAP.md.

The base model makes 16 simplifications, for example a list for the
Merkle tree, `Nat` amounts and opaque hashes. They are modelling
choices, not hypotheses. SPEC-MAP.md lists them and maps each
definition to its spec line. The epoch extension has additional limits,
listed separately there.

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
check. CLAIMS.md rows 16 and 17 state the window rule in the model; they
do not check the contract.

## How it was built

A controller session released small bounded tasks to AI workers from two
model families (Claude and GPT). The controller re-checked each result,
and a session from the other family judged it, before it counted. The
gate (below) checks mechanical conditions on the result: it rejects
`sorry`, `native_decide`, undeclared axioms, statement edits and
frozen-file changes. It does not by itself establish independence from
malicious build or elaboration code: the axiom census reads printed
output, and code imported during elaboration can affect that channel.
The hardening work is listed as a follow-up. Oskar directed the work and
read the statements against the spec. The review is the second pair of
eyes: Track A asks whether the model says what the spec says.

## What the theorems do not say

The fifteen core theorems say nothing about the SNARK verifier, the concrete Merkle tree, field
encodings, who may call the contract, re-entrancy, integer overflow,
governance, privacy, or any deployed code. The tree is a list, amounts
are `Nat`, hashes are opaque, steps are atomic: SPEC-MAP.md lists all 16
simplifications, each a review point. A nullifier collision can lock a
note; locked value counts as live. Whether the model says what the spec
says is a human reading, still open.

## Status and the ask

The base proofs and gate are complete, and the epoch commits pass the
gate and the gate test. The spec reading needs a second reader.
Aaryamann Challani and David Núñez are asked to review (REVIEW.md):
Track A, does the model say what the spec says, plus anything wrong, too
strong or unclear. After the review, either the two spec rows move to
"machine-checked (model)" through a spec change, or the claim here
shrinks to what survives. Findings go in issues here; Oskar answers each.

## What comes next

Follow-up pull requests bring in other work one claim unit at a time,
each behind the same gate: the claim 1 rule table as a status page, and
the privacy games once their build cost is decided. The epoch extension
is included here; its source is the PoC extension spec, not spec 2. The
implementation links stay in the research repo as claim records with
re-check commands, because their inputs are private. The repo is
private; no license yet.

## Names

The files keep the names they have in the research repo this model comes
from. This section's accounting covers the original core import
(lean-shielded-pool at commit 67160b1) and the L5 files; the
k-anonymity extension came later from the L5 pin, below. Of the 34
files that came from 67160b1, 11 are still byte-identical to that
commit. The other 23 were edited here: 19 while answering the review of
pull request 1, and four more controls when the base negative controls
became refutation controls. None of them matches 67160b1 now. Nothing is written back to
the research repo from here.

The seven L5 files come from the same research repo at commit
`fa5526ee6f1a39829a494f61c66b147cb151e994`, which carries the same
transfer-guard and `CryptoHyp` changes that pull request 1 made here.
None is byte-identical to that commit any more: `Proofs/EpochBase.lean`
and `Proofs/Epoch.lean` were byte-identical until the review of pull
request 5, which changed the ballast guard, the consumption log, the
chain-key-binding clause and the base-case premise, and added the
liveness proofs. `sha256sum -c PROVENANCE.sha256` checks exactly the 11
files above, and nothing else. The other five were edited or written
here:

- `Pool/Epoch.lean`: the header's source revision becomes `a04b8b3`,
  the revision verified against the recorded spec hash; a reference to
  a research file that is not cut is dropped; the simplification-7
  input rule now says the first input must be a member and only a
  zero-amount second input may omit membership.
- `Statements/L5.lean`: the header names the two real proof files
  instead of a stale proof-file name and a research note.
- `controls/positive_l5.lean`: rewritten here. The source control only
  instantiated theorem types; this one also proves an accepted run with
  the epoch `CryptoHyp` (CLAIMS.md, "Checks that the theorems have
  content").
- `controls/refute_l5_chainfacts.lean` and
  `controls/refute_l5_rollover.lean`: the source negative controls
  `neg_l5_chainfacts` and `neg_l5_rollover`, converted to refutation
  controls that must build, per the convention above.

What deviates from 67160b1, and why:

- Model and statements. `Pool/Tx.lean`: the transfer guard requires
  membership for the first input, following spec 4.2 and the reference
  circuit, and two stale docstring lines are fixed.
  `Statements/L3.lean`: `CryptoHyp.commit_inj` is restricted to `wf`
  notes. `Statements/L4.lean`: the solvency docstring names
  simplification 16 instead of citing 4.4. `Statements/L4B.lean`:
  `noTheft` is renamed `spendRequiresOwnerKey` and the spec citations
  are narrowed. `Pool/Events.lean` and `Statements/L4B.lean` lose their
  promotion comments, and `Pool/Events.lean`'s header now names
  SPEC-MAP instead of the research repo's clause map.
- Proofs. `Proofs/Invariants.lean` adds `Step.notes_wf` and
  `Run.runNotes_wf`. `Proofs/Conservation.lean`,
  `Proofs/NoDoubleSpend.lean` and `Proofs/TierB.lean` follow the guard
  change and the `wf` restriction. `Proofs/EventReplay.lean` and
  `Proofs/TierB.lean` lose their promotion comments.
- Controls, under the names they had in pull request 1.
  `controls/positive_l3.lean` proves `CryptoHyp` for the
  deposit-transfer-withdraw run. `controls/neg_l3_double_spend.lean`
  became the refutation control `controls/refute_l3_double_spend.lean`.
  `controls/neg_l4b_notheft.lean` became
  `controls/neg_l4b_ownerkey.lean` with the rename.
  `controls/neg_l3_conservation.lean`, `controls/neg_l3_spentcms.lean`,
  `controls/neg_l4_nominting.lean` and `controls/positive_l4b.lean`
  follow the same two changes.
- Refutation controls. The eight remaining base negative controls became
  refutation controls with the same name after `refute_`:
  `l3_conservation`, `l3_spentcms`, `l4_balancelive`, `l4_nominting`,
  `l4_overwithdrawal`, `l4_solvency`, `l4b_eventreplay` and
  `l4b_ownerkey`. Each keeps its mutation and must now build a proof of
  the negation (CLAIMS.md, "Checks that the theorems have content").
  `controls/refute_l3_double_spend.lean` names its renamed sibling.
- Gate. `scripts/gate.sh` takes modifier-prefixed axioms and builds the
  refutation controls. It also rejects a positive or refutation control
  whose build reports a `sorry`, and an axiom declared in a control.
  `scripts/check_frozen.py` adds
  `LeanShieldedPool/Proofs/*.lean` to the frozen surface, so the census
  imports no unpinned project file.

`statements/INVENTORY.md` and `scripts/gate_test.sh` also changed. They
were never covered by PROVENANCE.sha256; `statements/FROZEN.sha256` pins
both.

The k-anonymity extension comes from the same pin as the L5 files,
lean-shielded-pool `fa5526e`, file
`LeanShieldedPool/Statements/KAnonymity.lean`, moved
here to `LeanShieldedPool/Extensions/KAnonymity.lean` with a header-only
fitting (a draft marker and a research-repo path dropped). It was
byte-identical to that pin from `namespace` on until the review of this
pull request, which changed the module docstring and gave both toy
families owner-binding commitments with varied salts. The file is not in
PROVENANCE.sha256, which lists only byte-identical files and keeps its
11 entries; `statements/FROZEN.sha256` pins it.

The level names come from the research repo:

- L3 is the core model claim (`Statements/L3.lean`).
- L4 holds the accounting results (`Statements/L4.lean`).
- L4B holds authorization and events (`Statements/L4B.lean`).
- L5 holds the epoch extension (`Statements/L5.lean`). Its model and
  guard witnesses are in `Pool/Epoch.lean`.
- `Draft/NonVacuity.lean` is not a draft. It shows that each operation
  guard can fire, so the theorems are not vacuous. The directory keeps its
  old name so the bytes match.

## Reading order

1. README.md (this file).
2. CLAIMS.md: each theorem in Lean and in English.
3. SPEC-MAP.md: each definition against its spec line, then the 16
   simplifications.
4. The model: `LeanShieldedPool/Pool/State.lean`, `Tx.lean`, `Events.lean`,
   then `Epoch.lean`.
5. The statements: `LeanShieldedPool/Statements/L3.lean`, `L4.lean`,
   `L4B.lean`, `L5.lean`, `Window.lean`, and `statements/INVENTORY.md`.
6. The proofs: `LeanShieldedPool/Proofs/` and `Draft/NonVacuity.lean`.
7. The controls: `controls/`. Each base or epoch refutation control
   weakens one guard, post-state or replay step; the two extension
   refutation controls mutate a frozen definition instead. Each proves
   the negation of a frozen statement over its mutation; it must build.
8. The gate: `scripts/gate.sh`.

REVIEW.md is the reviewer guide.

## Re-check

You need git, bash, python3 and about 8 GB of free disk.

```
# setup: about 30 minutes (an estimate, not measured)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
git clone git@github.com:ethsystems/shielded-pool-model.git && cd shielded-pool-model
# Check out the revision under review before continuing.
lake exe cache get

bash scripts/gate.sh        # expect: GATE PASS (<commit>); 56 s measured
bash scripts/gate_test.sh   # expect: GATE_TEST PASS; 711 s measured
```

The gate tests committed HEAD, so an uncommitted tree is not a gate
result.

The gate builds a fresh clone of HEAD. It rejects `sorry`,
`native_decide` and undeclared axioms, in the controls too. It checks the
exact type and axioms of the 59 names in `statements/INVENTORY.md`, runs
the controls, and checks the pins in `statements/FROZEN.sha256`.
`gate_test.sh` plants 22 cheats; each must make the gate fail.

The 56 s gate time is one fresh clone of this branch with a copied
`.lake` cache. The 711 s fixture time is one run of the 22 fixtures.
Both ran on a Linux laptop with btrfs, with no memory cap and
`LEAN_NUM_THREADS=2`.
Each gate run copies `.lake` (about 7.5 GB). Without cheap
file copies, set `GATE_WORK` to a directory on APFS, btrfs or XFS.

AXIOMS.md lists the three allowed axioms: `propext`, `Classical.choice`
and `Quot.sound`. There is no domain axiom.
