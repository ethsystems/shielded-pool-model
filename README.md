# shielded-pool-model

Stable, reviewable claim units about the shielded pool, one unit at a
time. Each unit states a fixed claim or supporting result and
re-checks it with one command. The core unit is a small Lean 4 model of spec
2/SHIELDED-POOL (`specs/2/README.md` in ethsystems/specs-private, at
revision 4d4dce1). At that revision, spec section 6.2 marks "no double
spend" and "value conservation" as "tested". This repo holds the
candidate for moving those two rows to "machine-checked (model)". The
core is made to be read whole in an afternoon.

## The core claim

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

Nine theorems: nullifier uniqueness, no double spend and value
conservation, plus six supporting results about the same model
(solvency, no over-withdrawal, no minting, balance equals live value,
owner-key binding, event replay). [CLAIMS.md](CLAIMS.md) gives each
with its hypothesis and spec clause. The hypothesis is `CryptoHyp` in
`LeanShieldedPool/Statements/L3.lean`. It covers one history only. It
is not a Poseidon security claim. Two standing abstractions sit under
the claim next to `CryptoHyp`: a Merkle root stands for the exact leaf list it
commits to (simplification 2), and the verifier and circuit constrain
exactly what the guards state (simplification 1). Neither is a theorem
hypothesis; both are obligations on the implementation. The model makes
16 simplifications, for example a list for the Merkle tree, `Nat`
amounts, opaque hashes and atomic steps; [SPEC-MAP.md](SPEC-MAP.md)
lists them and maps each definition to its spec line. A nullifier
collision can lock a note; locked value counts as live.

## Scope

Two kinds of units live here: machine-checked model claims and scoped
implementation evidence with pinned inputs. A unit moves in once its
claim is stable and its check is self-contained. No unit verifies
deployed code: nothing about the verifier in production, the on-chain
Merkle tree, field encodings, callers, re-entrancy, arithmetic of the
deployed contract, governance, or privacy of the real system. The separate
packages check selected facts about circuits, hash code and verifier
builds, not deployed execution; no end-to-end implementation proof is
claimed anywhere in this repo. A model theorem cannot see an
implementation bug; [SPEC-MAP.md](SPEC-MAP.md) lists what a deployment
must satisfy for the model to describe it.

Work in progress lives in a private research repo,
oskarth/lean-shielded-pool. Implementation links whose inputs are public
come here as separate packages (below); the others stay in the research
repo as claim records with re-check commands. Verus proofs of the
shielded-pool client's prover input encoders and public-input array
builders live on branch [`verus/base`](https://github.com/ethsystems/pocs-private/tree/verus/base) of ethsystems/pocs-private,
off master on purpose; they are not linked to this model. Nothing is
claimed here beyond what the units below state.

## Where it comes from

The model was written and proved in a private research repo,
oskarth/lean-shielded-pool, in September 2026, and imported here with
its file names: L3 is the core claim (`Statements/L3.lean`), L4 the
accounting results, L4B authorization and events, L5 the epoch
results. `Draft/NonVacuity.lean` is not a draft; it shows that each
guard can fire. The epoch and k-anonymity files came from the same
repo at a later pin. The root-window files and the liveness control
were written here. Many files changed here during review; the commit
history records each change.

AI agents from two model families wrote the proofs; Oskar read the
statements against the spec.
The gate checks mechanical conditions on the result. It does not
by itself establish independence from malicious build or elaboration
code: the axiom census reads printed output, and code imported during
elaboration can affect that channel. A kernel-level census is a
follow-up in issue #2.

## Layout

The core is the spec-2 review unit:

- Model: `LeanShieldedPool/Pool/State.lean`, `Tx.lean`, `Events.lean`.
- Statements: `LeanShieldedPool/Statements/L3.lean`, `L4.lean`,
  `L4B.lean`, with the L3, L4 and L4B groups of
  [statements/INVENTORY.md](statements/INVENTORY.md).
- Proofs, under `LeanShieldedPool/Proofs/`: `Invariants.lean`,
  `NoDoubleSpend.lean`, `Conservation.lean`, `TierA.lean`,
  `TierAConditional.lean`, `TierB.lean`, `EventReplay.lean`; plus
  `LeanShieldedPool/Draft/NonVacuity.lean`.
- Controls: `controls/positive.lean`, `positive_l3.lean`,
  `positive_l4.lean`, `positive_l4b.lean`, and the `refute_l3_*`,
  `refute_l4_*` and `refute_l4b_*` files.
- Gate and docs: `scripts/`, this README, [REVIEW.md](REVIEW.md),
  [AXIOMS.md](AXIOMS.md). In
  [CLAIMS.md](CLAIMS.md), read everything except the epoch,
  root-window, k-anonymity and separate-package sections; the shared
  hypothesis, assumption and control sections are core. In
  [SPEC-MAP.md](SPEC-MAP.md), skip the window rows (`St.window` to
  `honestWithdraw_proof`) and stop before "L5: epoch extension".

Core reading order: this README, then CLAIMS.md, SPEC-MAP.md, the
model, the statements, the proofs, the controls, `scripts/gate.sh`.
[REVIEW.md](REVIEW.md) is the reviewer guide.

Three more units are gated with the core, each with its own files.
The epoch results extend the claim; the root-window results and the
k-anonymity extension are supporting material, not further claims
(CLAIMS.md). Their files, excluded from the core route:

- Epochs (L5): cross-epoch no double spend for value-bearing inputs
  plus five supporting results over the PoC epoch extension spec
  (sealed-list immutability, canonical append, chain key binding, a
  one-way refinement of rollover-free runs to the base pool, and
  spendability after rollover); no epoch conservation, no
  verification of recursive proofs or concrete nullifier trees, not a
  spec-2 claim; SPEC-MAP.md lists its other limits. Files:
  `Pool/Epoch.lean`, `Statements/L5.lean`, `Proofs/Epoch.lean`,
  `Proofs/EpochBase.lean`, the `_l5` controls, the L5 sections of
  [CLAIMS.md](CLAIMS.md), [SPEC-MAP.md](SPEC-MAP.md) and the
  inventory. Gated with the core.
- Root window (spec 2 section 4.4, issue #2): five theorems over the
  core model, outside the nine. Every window entry is an operation
  boundary (`windowBoundary`), the newest entry is the current root
  (`windowHead`), and the root between a transfer's two inserts is not
  in the window (`noMidTransferRoot`). The owner of a note that the
  pool minted, with a fresh nullifier, a nonzero amount and enough pool
  balance, has an accepted withdrawal against any window root that
  covers the note (`honestWithdrawWindow`), and so against the current
  root (`honestWithdraw`). The model's token set never changes
  (simplification 10). No exact-retention claim and no claim about the
  contract's window code. Files: `Statements/Window.lean`,
  `Proofs/Window.lean`, the three `refute_window_*` and
  `refute_honestwithdraw_*` controls, their rows in
  [CLAIMS.md](CLAIMS.md) and [SPEC-MAP.md](SPEC-MAP.md), and the
  inventory. Gated with the core.
- Symbolic k-anonymity, the gated extension: in a toy symbolic model,
  some accepted histories admit multiple recipient explanations
  (positive-k families, a cardinality counterexample);
  indistinguishability uses the named hypothesis `HashHidingHyp`. No
  Poseidon hiding bound, no deployed-privacy claim. Files:
  `LeanShieldedPool/Extensions/KAnonymity.lean`, the `k_anonymity`
  controls, the k-anonymity sections of [CLAIMS.md](CLAIMS.md) and the
  inventory. Gated with the core.

The gate builds the root Lean library and its controls: the core and
these three units together. It does not build the separate packages.

## Separate packages

Packages outside the gate, each with its own check and a row in CLAIMS.md
under "Separate packages". This repo is not a copy of the implementation: a
package fetches the code it checks from upstream, pinned by commit or by
checksum.

- [hash-agreement/](hash-agreement/README.md): the Noir, plain and
  segmented Solidity transcriptions of Poseidon2 (the two-input
  Poseidon, x^5, t = 3) agree as
  functions over the BN254 scalar field, all 65 rounds, library
  sources fetched at a pinned commit and checksum, not copied in.
  Separate package, own check and trust base; the gate does not build
  it.
- [circuits-acir/](circuits-acir/README.md): over the compiled ACIR
  constraints of the three PoC circuits at ethsystems/pocs `a04b8b3`,
  the deposit, withdraw and transfer amounts are below 2^128, transfer
  conserves value with no u128 wrap, and its four token fields are
  equal. The check rebuilds the circuits from the submodule
  `circuits-acir/pocs` with pinned nargo and noir-inspector and compares
  them with pinned hashes. Separate package, own check and trust base;
  the gate does not build it.
- [verifier-reproduction/](verifier-reproduction/README.md): rebuilds the
  three Solidity verifiers committed in ethsystems/pocs at `a04b8b3` (the
  submodule `verifier-reproduction/pocs`) from the committed circuits with
  pinned nargo and bb, and compares the bytes and the key hashes. A build
  reproduction, not a theorem; it says nothing about soundness or deployed
  code.

## Re-check

You need git, bash, python3 and about 8 GB of free disk.

    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    git clone git@github.com:ethsystems/shielded-pool-model.git && cd shielded-pool-model
    lake exe cache get          # one-time setup; .lake is about 7.5 GB
    bash scripts/gate.sh        # expect: GATE PASS (<commit>)

The gate builds a fresh clone of committed HEAD, so an uncommitted
tree is not a gate result. It rejects `sorry`, axioms not listed in
AXIOMS.md, and `native_decide` and its synonyms such as
`decide +native`. In the controls it rejects a `sorry` in the build
output, any declared axiom, and the same `native_decide` text; it runs
no axiom census on control theorems. It checks the exact type and axioms of every name in
[statements/INVENTORY.md](statements/INVENTORY.md), runs the controls,
and checks the pins in `statements/FROZEN.sha256`.
[AXIOMS.md](AXIOMS.md) lists the three allowed axioms: `propext`,
`Classical.choice` and `Quot.sound`. The gate has its own test,
`scripts/gate_test.sh`, which plants cheats that must each fail;
[REVIEW.md](REVIEW.md) describes it and records measured run times.
Each gate run copies `.lake`; without cheap file copies, set
`GATE_WORK` to a directory on APFS, btrfs or XFS.

## Status

The core proofs and gate are complete. Two human readings of the
model against the spec are done (REVIEW.md, part 5).
[REVIEW.md](REVIEW.md) is the reviewer guide; findings go in issues
here, and each gets an answer.

## License

File-level SPDX headers are authoritative. Code without a more
specific file-level license is licensed under MIT OR Apache-2.0
([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)).
Documentation, readmes and review notes are licensed under CC0-1.0
([LICENSE-CC0](LICENSE-CC0)) unless otherwise stated. Third-party
dependencies, including the pinned sources that the separate packages
fetch, keep their own licenses.
