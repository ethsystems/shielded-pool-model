# shielded-pool-model

Stable, reviewable claim units about the shielded pool, one unit at a
time. Each unit states a fixed claim or supporting result and
re-checks it with one command. The core unit is a small Lean 4 model of spec
2/SHIELDED-POOL (`specs/2/README.md` in ethsystems/specs, at
revision 4d4dce1). At that revision, spec section 6.2 marks "no double
spend" and "value conservation" as "tested". This repo holds the
candidate for moving those two rows to "machine-checked (model)". The
core is made to be read whole in an afternoon.

## The core claim

> The model covers the integrity rules of spec 2/SHIELDED-POOL,
> sections 4 to 6, at revision 4d4dce1 (exclusions in SPEC-MAP.md). In
> the model, the protocol rules imply two guarantees: no
> note spends twice, and value is conserved per token. Both hold from
> an empty pool, over every accepted history. One hypothesis is
> assumed, about the notes and keys that appear in that history. No
> two distinct notes with `u128` amounts share a commitment. No two
> distinct spending keys derive the same public key.
> Machine-checked with the three standard Lean axioms only. Whether
> the model says what the spec says is a human reading, not a
> machine check; one full reading (the second reader) and one
> high-level reading (Oskar) are done (REVIEW.md, part 5).

The core claim is rows 2 and 3 of CLAIMS.md. The nine base theorems
(rows 1 to 9) are nullifier uniqueness, no double spend and value
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
deployed execution: nothing here establishes the verifier's soundness
in production, the on-chain Merkle tree as deployed, governance, or
privacy of the real system, and the contract checks of field encodings,
callers, re-entrancy and arithmetic hold only within their stated
bounds, mocks and depths. The separate packages check selected facts
about circuits, hash code, verifier builds, the bytes of one deployment
at one block, the contract source at its pin (built with fixed library
addresses, run against mocks, within stated bounds), client functions
on reviewed mirrors, and privacy games in models; one states a
conditional refinement of the contract to the model under named
premises. None of them checks deployed execution, and no end-to-end
implementation proof is claimed anywhere in this repo. A model theorem
cannot see an implementation bug; [SPEC-MAP.md](SPEC-MAP.md) lists what
a deployment must satisfy for the model to describe it.

Implementation checks whose inputs are public live here as separate
packages (below). Verus mirrors of 96 client functions, among them the
prover-input encoders and the public-input array builders, are the
separate package [client-verus/](client-verus/README.md); they are not
linked to this model. Nothing is claimed here beyond what the units
below state.

[BOARD.md](BOARD.md) is the 36-rule obligations board for claim 1 (on-chain
safety) that the writeup cites. It is a status document: people chose
its status words, and each evidence cell names the check in this repo
that backs the row, or says that no package covers it.
[FINDINGS.md](FINDINGS.md) is the findings register of the campaign, 80
rows: a record, not a re-check. Neither is a claim of this repo, and the
gate reads neither.

## From the writeup

The writeup ["Formally verifying a shielded pool: from spec to
bytecode"](https://ethsystems.org/writeups/formally-verifying-a-shielded-pool-from-spec-to-bytecode/)
describes the verification campaign around this repo. Its sections map
to the units here:

- The model and the two theorems: the core unit
  ([CLAIMS.md](CLAIMS.md), rows 1 to 9); the epoch extension in the
  same section is the L5 unit (rows 10 to 15).
- The circuits, compiled route:
  [circuits-acir/](circuits-acir/README.md).
- The hash: [hash-agreement/](hash-agreement/README.md).
- The verifier: [verifier-reproduction/](verifier-reproduction/README.md).
- Privacy: the symbolic k-anonymity extension
  (`LeanShieldedPool/Extensions/KAnonymity.lean`); the conditional
  bounds of the privacy games: [privacy-games/](privacy-games/README.md).
- The deployment check: [deployment/](deployment/README.md), the Sepolia
  deployment at block 11949456 against a fresh build of `a04b8b3`.
- The contract checks: [contract-halmos/](contract-halmos/README.md)
  and [contract-kontrol/](contract-kontrol/README.md); the board that
  collects them rule by rule, with its counts: [BOARD.md](BOARD.md).
- The refinement of the contract to the model:
  [refinement/](refinement/README.md).
- The wallet proofs, Verus half: [client-verus/](client-verus/README.md);
  the Aeneas half is counted from the client coverage report of
  2026-10-01, which is not in this repo.
- The findings: [FINDINGS.md](FINDINGS.md). Issue #10 tracks the
  hand-offs below the model.

## Where it comes from

The model was written and proved in September 2026. The file names
keep their first layout: L3 is the core claim (`Statements/L3.lean`),
L4 the accounting results, L4B authorization and events, L5 the epoch
results. `Draft/NonVacuity.lean` is not a draft; it shows that each
guard can fire. The epoch and k-anonymity files came later, the
root-window files and the liveness control last. Many files changed
during review; the commit history records each change.

AI agents from two model families wrote the proofs. A second reader
read the statements against the spec in full; Oskar did a high-level
reading from a one-page summary (REVIEW.md, part 5).
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
The epoch results (rows 10 to 15) complete the claim set of rows 1 to
15; the root-window results and the k-anonymity extension are
supporting material, outside the claim set (CLAIMS.md). Their files, excluded from the core route:

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
  core model, outside the claim set. Every window entry is an operation
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
- [circuits-lampe/](circuits-lampe/README.md): over the Noir source of the
  three PoC circuits at ethsystems/pocs `a04b8b3`, extracted into Lean by a
  patched Lampe (a fork pinned by commit), the hash-bound rules hold for
  every accepting execution: the commitment and nullifier equations, the
  one owner key, and the Merkle roots as folds with depth bounds 20, 32
  and 32 (the second transfer input, circuit input 1, is checked only when its
  amount is nonzero);
  the extracted Poseidon permutations compute their pure functions. Statements about the program as Lampe reads it, not the
  compiled constraints; the Noir compiler stays trusted on this route.
  Separate package, own check and trust base; the gate does not build it.
- [verifier-reproduction/](verifier-reproduction/README.md): rebuilds the
  three Solidity verifiers committed in ethsystems/pocs at `a04b8b3` (the
  submodule `verifier-reproduction/pocs`) from the committed circuits with
  pinned nargo and bb, and compares the bytes and the key hashes. A build
  reproduction, not a theorem; it says nothing about soundness or deployed
  code.
- [deployment/](deployment/README.md): at Sepolia block 11949456, the 12
  contracts of the shielded pool deployment equal a fresh offline build of
  ethsystems/pocs `a04b8b3` (the submodule `deployment/pocs`), byte for
  byte, with links and immutables filled; the composite slots, the absence
  of mock verifiers, the `VerifierUpdated` history, the owner and the token
  set match the claim. A check of one chain at one block, against any RPC.
  It trusts the RPC and says nothing about later blocks, token or owner
  behaviour, or soundness.
- [contract-halmos/](contract-halmos/README.md): bounded symbolic checks
  of `ShieldedPool.sol` at ethsystems/pocs `a04b8b3` (the submodule
  `contract-halmos/pocs`) with a pinned Halmos 0.3.3, in nine suites: the
  guards before the verifier, duplicate leaves and the reentrancy lock,
  insertion order and token callbacks, the owner functions, the withdraw
  payout with a symbolic caller, the root ring, the postcondition fields
  and the root window. A PASS holds only within its suite's scope line
  (byte lengths, tree depths, mocks, a keccak stub for Poseidon where
  stated, gas unmodelled), and named mutants must fail. Not a statement
  about the deployed contract. Separate package, own check and trust
  base; the gate does not build it.
- [contract-kontrol/](contract-kontrol/README.md): Kontrol proofs about
  the bytecode that solc 0.8.37 builds from `ShieldedPool.sol` at
  `a04b8b3` (the submodule `contract-kontrol/pocs`), in a container
  pinned by digest: the guards before the verifier for byte lengths up
  to 2^30 (withdraw below 2^64, with a patched KEVM file), the withdraw
  success path for a token above 0x11 and a fixed caller, canonical
  public inputs and their order, and local checks of the tree insertion
  loop; plus a Halmos check that the PoseidonT3 library is a pure
  function. Each proof holds in its stated scope, under KEVM's semantics
  and one trusted bytes-prefix rule, with mock verifiers and tokens;
  named mutants must fail. The insertion-loop K claims are archived claims
  about the solc 0.8.33 build, packaged with their 2026-10-01 results and
  not run by the check. Separate package, own check and trust base; the
  gate does not build it.
- [refinement/](refinement/README.md): a conditional refinement of the
  pool contract to the gated model, imported unchanged. Under named
  contract, circuit, tree and cryptographic premises, every accepted
  history of an abstract contract refines a model run, so the money
  theorems apply. Every accepted root is a prefix root of the leaves.
  The LeanIMT tree matches the circuits' Merkle fold (through
  `circuits-lampe/` for the field fold). Under token premises, the
  pool's balance bounds every admitted withdrawal. It also holds the
  arithmetic of the gas argument. No concrete execution and no premise
  discharged for the deployment. Separate package, own check and trust
  base; the gate does not build it.
- [client-verus/](client-verus/README.md): for 96 of the 110
  security-relevant functions of the shielded-pool client at
  ethsystems/pocs `a04b8b3` (the submodule `client-verus/pocs`), a
  selected property holds on a reviewed Verus mirror of the function,
  under named parameter contracts. A pinned Verus release checks every
  mirror with `--no-cheating`, and the diff of each mirror to its
  hash-pinned source region is checked. Of 241 negative controls, Verus
  refutes 239; 2 stop at the solver's resource limit (rows 65 and 66,
  each with a second refuted control). The 22 Aeneas results of the
  client coverage report of 2026-10-01 are counted, not re-checked.
  These are mirrors, not the compiled client, and the package says
  nothing about effects or library behaviour. Separate package, own
  check and trust base; the gate does not build it.
- [privacy-games/](privacy-games/README.md): two-world privacy games
  over the model's guards (VCV-io, pinned by commit), with conditional
  bounds on the attacker's advantage for the recipient of static
  transfers and of fixed chains (hiding and spread premises), and for
  the withdrawn note, the deposit owner and the transfer sender (a
  random-oracle premise, honest keys). It also has two proved
  counterexamples and funded toy witnesses. It imports three model
  files unchanged. No deployed-privacy claim: no Poseidon instantiation,
  the random-oracle premise is a heuristic, and interactive attackers
  are open. Separate package, own check and trust base; the gate does
  not build it.

## Re-check

You need git, bash, python3 and about 8 GB of free disk.

    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    git clone https://github.com/ethsystems/shielded-pool-model.git && cd shielded-pool-model
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

The core proofs and gate are complete. One full reading (the second
reader) and one high-level reading (Oskar) of the model against the
spec are done (REVIEW.md, part 5).
[REVIEW.md](REVIEW.md) is the reviewer guide; findings go in issues
here (part 8 of that guide gives the format), and each gets an answer.

## License

File-level SPDX headers are authoritative. Code without a more
specific file-level license is licensed under MIT OR Apache-2.0
([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)).
Documentation, readmes and review notes are licensed under CC0-1.0
([LICENSE-CC0](LICENSE-CC0)) unless otherwise stated. Third-party
dependencies, including the pinned sources that the separate packages
fetch, keep their own licenses.
