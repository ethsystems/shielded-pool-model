# Guide to this repository

The longer version of the README: where the model came from, how the
files are laid out, what each separate package claims in full, and how
the writeup's sections map onto the repository.

## Where the model comes from

The model was written and proved in September 2026. The file names
keep their first layout: L3 is the core claim (`Statements/L3.lean`),
L4 the accounting results, L4B authorization and events, L5 the epoch
results. `Draft/NonVacuity.lean` is not a draft; it shows that each
guard can fire. The epoch and k-anonymity files came later, the
root-window files and the liveness control last. Many files changed
during review; the commit history records each change.

AI agents from two model families wrote the proofs. A second reader
read the statements against the spec in full; Oskar did a high-level
reading from a one-page summary (REVIEW.md, part 5). The gate checks
mechanical conditions on the result. It does not by itself establish
independence from malicious build or elaboration code: the axiom census
reads printed output, and code imported during elaboration can affect
that channel. A kernel-level census is an open follow-up.

## Layout of the core

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
- Gate and docs: `scripts/`, the README, [REVIEW.md](REVIEW.md),
  [AXIOMS.md](AXIOMS.md). In [CLAIMS.md](CLAIMS.md), read everything
  except the epoch, root-window, k-anonymity and separate-package
  sections; the shared hypothesis, assumption and control sections are
  core. In [SPEC-MAP.md](SPEC-MAP.md), skip the window rows
  (`St.window` to `honestWithdraw_proof`) and stop before "L5: epoch
  extension".

Core reading order: the README, then CLAIMS.md, SPEC-MAP.md, the
model, the statements, the proofs, the controls, `scripts/gate.sh`.
[REVIEW.md](REVIEW.md) is the reviewer guide.

The core claim is rows 2 and 3 of CLAIMS.md. The nine base theorems
(rows 1 to 9) are nullifier uniqueness, no double spend and value
conservation, plus six supporting results about the same model
(solvency, no over-withdrawal, no minting, balance equals live value,
owner-key binding, event replay). The hypothesis is `CryptoHyp` in
`LeanShieldedPool/Statements/L3.lean`. It covers one history only. It
is not a Poseidon security claim. Two standing abstractions sit under
the claim next to `CryptoHyp`: a Merkle root stands for the exact leaf
list it commits to (simplification 2), and the verifier and circuit
constrain exactly what the guards state (simplification 1). Neither is
a theorem hypothesis; both are obligations on the implementation. The
model makes 16 simplifications, for example a list for the Merkle tree,
`Nat` amounts, opaque hashes and atomic steps; SPEC-MAP.md lists them
and maps each definition to its spec line. A nullifier collision can
lock a note; locked value counts as live.

## Units gated with the core

Three more units are gated with the core, each with its own files. The
epoch results (rows 10 to 15) complete the claim set of rows 1 to 15;
the root-window results and the k-anonymity extension are supporting
material, outside the claim set (CLAIMS.md).

- Epochs (L5): cross-epoch no double spend for value-bearing inputs
  plus five supporting results over the PoC epoch extension spec
  (sealed-list immutability, canonical append, chain key binding, a
  one-way refinement of rollover-free runs to the base pool, and
  spendability after rollover); no epoch conservation, no verification
  of recursive proofs or concrete nullifier trees, not a spec-2 claim;
  SPEC-MAP.md lists its other limits. Files: `Pool/Epoch.lean`,
  `Statements/L5.lean`, `Proofs/Epoch.lean`, `Proofs/EpochBase.lean`,
  the `_l5` controls, the L5 sections of CLAIMS.md, SPEC-MAP.md and the
  inventory.
- Root window (spec 2 section 4.4): five theorems over the core model.
  Every window entry is an operation boundary (`windowBoundary`), the
  newest entry is the current root (`windowHead`), and the root between
  a transfer's two inserts is not in the window (`noMidTransferRoot`).
  The owner of a note that the pool minted, with a fresh nullifier, a
  nonzero amount and enough pool balance, has an accepted withdrawal
  against any window root that covers the note
  (`honestWithdrawWindow`), and so against the current root
  (`honestWithdraw`). The model's token set never changes
  (simplification 10). No exact-retention claim and no claim about the
  contract's window code. Files: `Statements/Window.lean`,
  `Proofs/Window.lean`, the three `refute_window_*` and
  `refute_honestwithdraw_*` controls, their rows in CLAIMS.md and
  SPEC-MAP.md, and the inventory.
- Symbolic k-anonymity: in a toy symbolic model, some accepted
  histories admit multiple recipient explanations (positive-k
  families, a cardinality counterexample); indistinguishability uses
  the named hypothesis `HashHidingHyp`. No Poseidon hiding bound, no
  deployed-privacy claim. Files:
  `LeanShieldedPool/Extensions/KAnonymity.lean`, the `k_anonymity`
  controls, the k-anonymity sections of CLAIMS.md and the inventory.

The gate builds the root Lean library and its controls: the core and
these three units together. It does not build the separate packages.

## The separate packages in full

Each package has its own check and a row in CLAIMS.md under "Separate
packages". This repository is not a copy of the implementation: a
package fetches the code it checks from upstream, pinned by commit or
by checksum. The gate builds none of them.

- [hash-agreement/](hash-agreement/README.md): the Noir, plain and
  segmented Solidity transcriptions of Poseidon2 (the two-input
  Poseidon, x^5, t = 3) agree as functions over the BN254 scalar field,
  all 65 rounds, library sources fetched at a pinned commit and
  checksum, not copied in.
- [circuits-acir/](circuits-acir/README.md): over the compiled ACIR
  constraints of the three PoC circuits at ethsystems/pocs `a04b8b3`,
  the deposit, withdraw and transfer amounts are below 2^128, transfer
  conserves value with no u128 wrap, and its four token fields are
  equal. The check rebuilds the circuits from the submodule
  `circuits-acir/pocs` with pinned nargo and noir-inspector and
  compares them with pinned hashes.
- [circuits-lampe/](circuits-lampe/README.md): over the Noir source of
  the three PoC circuits at ethsystems/pocs `a04b8b3`, extracted into
  Lean by a patched Lampe (a fork pinned by commit), the hash-bound
  rules hold for every accepting execution: the commitment and
  nullifier equations, the one owner key, and the Merkle roots as folds
  with depth bounds 20, 32 and 32 (the second transfer input, circuit
  input 1, is checked only when its amount is nonzero); the extracted
  Poseidon permutations compute their pure functions. Statements about
  the program as Lampe reads it, not the compiled constraints; the Noir
  compiler stays trusted on this route.
- [verifier-reproduction/](verifier-reproduction/README.md): rebuilds
  the three Solidity verifiers committed in ethsystems/pocs at
  `a04b8b3` (the submodule `verifier-reproduction/pocs`) from the
  committed circuits with pinned nargo and bb, and compares the bytes
  and the key hashes. A build reproduction, not a theorem; it says
  nothing about soundness or deployed code.
- [deployment/](deployment/README.md): at Sepolia block 11949456, the
  12 contracts of the shielded pool deployment equal a fresh offline
  build of ethsystems/pocs `a04b8b3` (the submodule `deployment/pocs`),
  byte for byte, with links and immutables filled; the composite slots,
  the absence of mock verifiers, the `VerifierUpdated` history, the
  owner and the token set match the claim. A check of one chain at one
  block, against any RPC. It trusts the RPC and says nothing about
  later blocks, token or owner behaviour, or soundness.
- [contract-halmos/](contract-halmos/README.md): bounded symbolic
  checks of `ShieldedPool.sol` at ethsystems/pocs `a04b8b3` (the
  submodule `contract-halmos/pocs`) with a pinned Halmos 0.3.3, in nine
  suites: the guards before the verifier, duplicate leaves and the
  reentrancy lock, insertion order and token callbacks, the owner
  functions, the withdraw payout with a symbolic caller, the root ring,
  the postcondition fields and the root window. A PASS holds only
  within its suite's scope line (byte lengths, tree depths, mocks, a
  keccak stub for Poseidon where stated, gas unmodelled), and named
  mutants must fail. Not a statement about the deployed contract.
- [contract-kontrol/](contract-kontrol/README.md): Kontrol proofs about
  the bytecode that solc 0.8.37 builds from `ShieldedPool.sol` at
  `a04b8b3` (the submodule `contract-kontrol/pocs`), in a container
  pinned by digest: the guards before the verifier for byte lengths up
  to 2^30 (withdraw below 2^64, with a patched KEVM file), the withdraw
  success path for a token above 0x11 and a fixed caller, canonical
  public inputs and their order, and local checks of the tree insertion
  loop; plus a Halmos check that the PoseidonT3 library is a pure
  function. Each proof holds in its stated scope, under KEVM's
  semantics and one trusted bytes-prefix rule, with mock verifiers and
  tokens; named mutants must fail. The insertion-loop K claims are
  archived claims about the solc 0.8.33 build, packaged with their
  2026-10-01 results and not run by the check.
- [refinement/](refinement/README.md): a conditional refinement of the
  pool contract to the gated model, imported unchanged. Under named
  contract, circuit, tree and cryptographic premises, every accepted
  history of an abstract contract refines a model run, so the money
  theorems apply. Every accepted root is a prefix root of the leaves.
  The LeanIMT tree matches the circuits' Merkle fold (through
  `circuits-lampe/` for the field fold). Under token premises, the
  pool's balance bounds every admitted withdrawal. It also holds the
  arithmetic of the gas argument. No concrete execution and no premise
  discharged for the deployment.
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
  nothing about effects or library behaviour.
- [privacy-games/](privacy-games/README.md): two-world privacy games
  over the model's guards (VCV-io, pinned by commit), with conditional
  bounds on the attacker's advantage for the recipient of static
  transfers and of fixed chains (hiding and spread premises), and for
  the withdrawn note, the deposit owner and the transfer sender (a
  random-oracle premise, honest keys). It also has two proved
  counterexamples and funded toy witnesses. It imports three model
  files unchanged. No deployed-privacy claim: no Poseidon
  instantiation, the random-oracle premise is a heuristic, and
  interactive attackers are open.

## From the writeup

The writeup ["Formally verifying a shielded pool: from spec to
bytecode"](https://ethsystems.org/writeups/formally-verifying-a-shielded-pool-from-spec-to-bytecode/)
describes the verification campaign around this repository. Its
sections map to the units here:

- The model and the two theorems: the core unit (CLAIMS.md, rows 1 to
  9); the epoch extension in the same section is the L5 unit (rows 10
  to 15).
- The circuits, compiled route: `circuits-acir/`.
- The hash: `hash-agreement/`.
- The verifier: `verifier-reproduction/`.
- Privacy: the symbolic k-anonymity extension
  (`LeanShieldedPool/Extensions/KAnonymity.lean`); the conditional
  bounds of the privacy games: `privacy-games/`.
- The deployment check: `deployment/`, the Sepolia deployment at block
  11949456 against a fresh build of `a04b8b3`.
- The contract checks: `contract-halmos/` and `contract-kontrol/`; the
  board that collects them rule by rule, with its counts: BOARD.md.
- The refinement of the contract to the model: `refinement/`.
- The wallet proofs, Verus half: `client-verus/`; the Aeneas half is
  counted from the client coverage report of 2026-10-01, which is not
  in this repository.
- The findings: FINDINGS.md. The hand-offs below the model are tracked
  outside this repository.

## The gate in detail

The gate builds a fresh clone of committed HEAD, so an uncommitted tree
is not a gate result. It rejects `sorry`, axioms not listed in
AXIOMS.md, and `native_decide` and its synonyms such as
`decide +native`. In the controls it rejects a `sorry` in the build
output, any declared axiom, and the same `native_decide` text; it runs
no axiom census on control theorems. It checks the exact type and
axioms of every name in [statements/INVENTORY.md](statements/INVENTORY.md),
runs the controls, and checks the pins in `statements/FROZEN.sha256`.
[AXIOMS.md](AXIOMS.md) lists the three allowed axioms: `propext`,
`Classical.choice` and `Quot.sound`. The gate has its own test,
`scripts/gate_test.sh`, which plants cheats that must each fail;
[REVIEW.md](REVIEW.md) describes it and records measured run times.
Each gate run copies `.lake`; without cheap file copies, set
`GATE_WORK` to a directory on APFS, btrfs or XFS.
