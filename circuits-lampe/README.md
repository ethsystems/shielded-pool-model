# circuits-lampe: hash-bound rules of deposit, transfer and withdraw over the Lampe extraction

This package proves the hash-bound rules of the three shielded-pool Noir circuits: the
commitment, the owner key, the nullifiers and the Merkle roots. Its input is the Noir source,
not the compiled constraints: the circuits committed at `a04b8b3` of ethsystems/pocs (public),
translated into Lean by the extractor of a patched Lampe fork. Lampe gives the extracted code
a big-step semantics (`Omni`) in Lean, and the Lean kernel checks the theorems against it. The
package commits the extracted sources and pins their hashes; `scripts/extract.sh` regenerates
them from the circuit sources. It is separate from the model in the parent directory: it has
its own lakefile, uses the same toolchain (Lean 4.33.1, here with Mathlib through Lampe), and
imports no model module. Nothing here changes the claim in the parent README.

The pin is not the latest circuit. Commit `748884e` of ethsystems/pocs (merged 2026-10-08)
changed `circuits/transfer/src/main.nr` after `a04b8b3`. The package stays at the pin; the
newer transfer circuit is not covered here.

## The claim

For every accepting execution of the complete extracted `main` of each circuit, over BN254:

- deposit: `commitment = hash4 token amount (ownerKey spending_key) salt`; `proof_length ≤ 20`,
  and the public `attestation_root` is the Merkle fold of the attestation leaf
  `hash4 (ownerKey spending_key) attester issued_at expires_at` along `path` and `indices`;
- transfer: both input commitments use the owner key of the one private `spending_key`; both
  nullifiers are `hash2v Cᵢ spending_key`; each output commitment is `hash4` of its own token,
  amount, owner and salt; input 0 has `proof_length_0 ≤ 32` and `commitment_root` is its Merkle
  fold; input 1 has the same when `amount_in_1 ≠ 0`;
- withdraw: the note commitment uses the public `token` and `amount` and the owner key of the
  private `spending_key`; `nullifier = hash2v C spending_key`; `proof_length ≤ 32` and
  `commitment_root` is the Merkle fold of the commitment.

`ownerKey`, `hash4` and `hash2v` are pure Lean functions: the values that the extracted
`hash_1`, `poseidon4` and `hash_2` code computes (first element of the Poseidon permutation of
width 2, 5 and 3 on `[0, inputs]`). The permutation theorems (`Poseidon.Permutation2.perm`,
`Poseidon.Permutation5.perm`, and `Poseidon.Hash2.perm3w` with its transfer and deposit
copies) prove that the extracted `permute` with
the extracted constants returns these values, and the determinism proofs (`Determinism`) show
that no other derivation of these calls returns another value. The Merkle fold `merkleRoot` is
a pure Lean fold, and `Merkle.Fold.bmr_fwd` proves that the extracted `binary_merkle_root<N>`
computes it, for every `N`, depth, leaf, path and direction bits. Each circuit has an
accepting execution that meets the premises of its rule theorems (non-vacuity).

"Accepting execution" means a derivation `Omni p Γ st (main.call …) Q` whose postcondition
`Q` rejects failure (`¬ Q none`), in the environment `Γ` of the whole extracted circuit
(`«deposit-0.0.0».env` and so on: the circuit, the poseidon and binary_merkle_root libraries
and the Noir stdlib). `p` is the BN254 scalar field prime.

## The theorems

| Circuit | Theorem | Statement |
|---|---|---|
| deposit | `Deposit.Commitment.accepting_main_commitment_eq` | `commitment = hash4 token amount (ownerKey spending_key) salt` |
| deposit | `Deposit.AttestationRoot.accepting_main_attestation_root` | the commitment equation, `proof_length ≤ 20` and `attestation_root = merkleRoot hash2v leaf proof_length indices path` |
| deposit | `Deposit.Main.main_accepting_execution`, `Deposit.Commitment.rules_eq_nonvacuous` | an accepting execution of `main`, and the premises and conclusions of the rule equations at it |
| withdraw | `Withdraw.Nullifier.accepting_main_withdraw_rules` | `nullifier = hash2v C spending_key`, `proof_length ≤ 32`, the extracted root call on `C` returns `commitment_root` |
| withdraw | `Withdraw.Root.accepting_main_withdraw_root` | `proof_length ≤ 32`, `commitment_root = merkleRoot hash2v C proof_length indices path`, the nullifier equation |
| withdraw | `Withdraw.Nullifier.main_accepting_execution`, `Withdraw.Root.main_accepting_execution_depth`; `Withdraw.Nullifier.withdraw_rules_nonvacuous`, `Withdraw.Root.withdraw_root_nonvacuous` | accepting executions at depth 0 and at every depth up to 32; at them, the rule premises hold, and at depth 3 the root is three `hash2v` levels above `C` |
| transfer | `Transfer.Rules.accepting_main_transfer_rules` | the Merkle root calls (input 1 only when `amount_in_1 ≠ 0`), both nullifier equations, both output commitments |
| transfer | `Transfer.Root.accepting_main_transfer_root` | the same, with each root as `merkleRoot hash2v Cᵢ proof_length_i indices_i path_i` |
| transfer | `Transfer.Execution.main_accepting_execution`, `Transfer.Execution.transfer_rules_nonvacuous` | an accepting execution, with a zero-amount input 1 at `proof_length_1 = 33`; the rule premises hold at it |
| all | `Merkle.Fold.bmr_fwd` | the extracted `binary_merkle_root<N>` returns `merkleRoot h leaf depth indices path` for a hasher that computes `h` |
| all | `Poseidon.Permutation2.perm`, `Poseidon.Permutation5.perm`, `Poseidon.Hash2.perm3w` | the extracted `permute` at widths 2, 5 and 3 computes the pure permutation `f` |

In withdraw and transfer `C` (or `Cᵢ`) is `hash4 token amount (ownerKey spending_key) salt`
of that note; transfer amounts are `u128` and enter as `amount.toNat`. Relational forms of the
same rules (`Deposit.Rules`, `Deposit.Attestation`, `Withdraw.Rules`, `Transfer.Relational`)
state them over the outcomes of the extracted hash calls, with no pure function.
[statements/INVENTORY.md](statements/INVENTORY.md) lists the 634 theorems of the package
outside the lookup-certificate leaves, each with its exact statement;
[statements/CERTIFICATES.md](statements/CERTIFICATES.md) lists the 4,071 theorems of the leaves
in the same format.

The comments in the modules name rules by number: deposit rule 2 is the owner key, rule 3 the
commitment, rule 4 the attestation membership; withdraw W2 is the Merkle root, W3 the
commitment, W4 the nullifier, W5 the public token and amount in the commitment; transfer T2
is the one owner key of both inputs, T3 the Merkle roots, T4 the nullifiers, T10 the output
commitments.

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axiom.
No proof uses `native_decide`.

## What the theorems say, and what they do not

- The rules hold for every accepting execution of the extracted `main`, under Lampe's
  semantics at the pinned fork commit. They are statements about the Noir program as Lampe
  reads it, not about the compiled ACIR. That the compiled constraints enforce the same rules
  rests on the Noir compiler, which stays trusted for this route.
  [circuits-acir/](../circuits-acir/README.md) proves other rules (ranges, transfer
  conservation, token equality) over the compiled constraints; no theorem links the two.
- The hash functions are the extracted Poseidon code. No claim about Poseidon's
  cryptographic properties: collision resistance and hiding are not stated.
- Not covered: the range and linear rules (amounts below `2^128`, transfer conservation,
  equal tokens), the unconstrained inputs (`funding_address`, `payload_hash`, `recipient`),
  and the root of transfer input 1 when its amount is zero, which the circuit does not check
  (input 0 is checked at every amount).
- Non-vacuity: each circuit has an accepting execution of `main` (the `main_accepting_execution`
  theorems), and the `*_nonvacuous` theorems apply the rule theorems at it. The inputs are zero
  where the circuit lets them be: token, amount, spending key, salt, attester and timestamps 0,
  with zero paths and direction bits. The values the circuit checks are the hash expressions of
  those inputs: in deposit the commitment `hash4 0 0 (ownerKey 0) 0` and an attestation root at
  depth 0 equal to the attestation leaf; in withdraw the zero note's commitment as the root and
  its nullifier; in transfer the two nullifiers, the output commitments and input 0's commitment
  as the root. Transfer input 1 has salt 1 and `proof_length_1 = 33`, which the circuit accepts
  because its amount is zero. Withdraw also has an accepting execution at every depth up to 32,
  for every path and direction bits, with the root the Merkle fold of the zero note, and at depth
  3 the root written out. These are Lean derivations, not solver witnesses or contract-accepted
  proofs.
- The lookup certificates (`*Lookup` modules, 59 leaves each, one per module environment)
  prove by `rfl` which declarations of each name used by the proofs the circuit environment
  holds, and derive `Deposit.Range.UniqueDecl`: every declaration with that name has the same
  body. A name may be declared more than once with an identical body: the stdlib
  functions (`assert_max_bit_size`, `pow_32`, `to_le_bits`) are present three times
  (`Deposit.Range.range_unique` uses three copies). So the proofs call the body the circuit
  calls.
- The controls (`controls/`) copy a theorem, change its statement, and must fail to compile;
  the `same_*` copies change nothing and must compile. A failing control shows that the
  original proof does not prove the changed statement. It does not show that the changed
  statement is false. Some controls fail by a recursion or heartbeat limit, not by a type
  error; `controls/EXPECTED.tsv` records each first error. `pass_deposit_attestation_rel_canonical_casts`
  changes the statement and must compile: with the patched cast builtin the timestamps of the
  attestation leaf are the canonical casts. The hand-written `cast_unconstrained` is the
  theorem that the unpatched cast builtin admits any cast value; it must fail on the fork.
- No statement about the verifier, the pool contract, deployed code, or the prover.

## Trust base

- Lampe at the fork commit (`oskarth/lampe` at `e0c0f60`, on upstream reilabs/lampe
  `919a387`): its semantics and its generated stdlib. The fork changes, in commit order: the
  loop rule must establish the postcondition after zero iterations (upstream #315); the
  extractor builds against Noir 1.0.0-beta.21; Lean 4.33.1 and the matching Mathlib; the Noir
  stdlib source and its extraction move to beta.21, with the wrappers repointed; generated
  projects require Lampe by path; a `poseidon2ConfigStateSize` builtin (4 for BN254); Field
  literal arrays elaborate to `Expr.literalArray`, large ones through an auxiliary definition;
  trait resolution skips impls whose generics have the wrong type; the field-prime
  certificates no longer use `native_decide`; the stdlib wrappers are repaired for beta.21 on
  Lean 4.33, and `mkFormatString` is modelled for the one signature Poseidon2's static
  assertion reaches (it renders no text); `as_witness` gets a value-level semantics (a no-op),
  `toLeBits` and `modulusLeBits` get Boolean signatures; the cast builtin is one fixed function
  per type pair (upstream #317), where before a derivation could choose any cast value; build
  flags and manifests; the stdlib's own check modules move to `stdlib/lampe/Checks/`. Each
  change is a commit on the fork branch.
- The extractor (the fork's Rust binary, which runs the Noir 1.0.0-beta.21 frontend):
  trusted to translate the Noir source faithfully. `scripts/extract.sh` shows that it
  reproduces `extracted/` byte for byte; it does not show that the translation is right.
- The Lean kernel, and the three axioms above.
- Mathlib at `0df444a` and its dependencies, as Lampe requires them.
- Not trusted: the proof modules, the census and the controls; the census and the scans are
  checks against mistakes, not against a hostile package (as in circuits-acir: code that runs
  during elaboration could change what the census prints).

## Pins

[PINS.sha256](PINS.sha256) holds the pins as `# key value` lines and sha256sum lines:

- Lampe: `https://github.com/oskarth/lampe` at `e0c0f6097bb97dd539355b76371e2443bd58b656`,
  on upstream `https://github.com/reilabs/lampe` at `919a38712d22d05fc83e59af17ef57077abda1e0`.
  `lakefile.toml` requires the fork by git at that commit, twice: `Lampe` (`subDir = "Lampe"`)
  and its generated stdlib `std-1.0.0-beta.21` (`subDir = "stdlib/lampe"`). The fork lives on
  a personal account: if that account deletes or rewrites it, the check cannot fetch Lampe. A
  fork under the ethsystems organization, then a repin, is the planned fix.
- The 28 extracted Lean files of `extracted/`. Two dependency packages are shared by the
  three circuits, so `extracted/deps/` keeps one copy of each; the three extractions of each
  file are identical. The generated `lakefile.toml` files carried the absolute paths of the
  extractor checkout; here they require only each other by relative path, and the flags are
  `-M8192` and `-DElab.async=false` as in the rest of the package. The generated
  `lean-toolchain` files are not kept.
- The Noir sources: the circuit `Nargo.toml` and `main.nr` files at ethsystems/pocs
  `a04b8b38969dfc2ee64de47edee7e396454204a8`, and the source files of the two Noir
  dependencies (noir-lang/poseidon `v0.3.0`, zk-kit.noir `binary-merkle-root-v0.0.2`) with their
  commits. Noir 1.0.0-beta.21 (`89a0f0f`), as pinned by the fork's `Cargo.lock`.

## Re-check

Install git, bash, python3 (3.11 or later), sha256sum and elan. The first run downloads the
Lampe fork, Mathlib and Mathlib's prebuilt oleans (about 7 GB in `.lake`).

```
cd circuits-lampe
scripts/check.sh      # expect the last line: CHECK PASS: ...
```

Set `JOBS` to compile several modules at once (each takes up to about 4.5 GB of memory). For
the circuit-source pins, check out the pocs submodule first (from the repo root:
`git submodule update --init circuits-acir/pocs`); without it that stage is skipped.

`scripts/check.sh` runs, in order:

1. the tools: Lean 4.33.1 through lake, python3;
2. the pins: every file of `extracted/` against `PINS.sha256`, with no file missing or extra;
   the circuit sources at the pocs pin, as git blobs, when the checkout is there; the git
   URL, commit and `subDir` of each of the two Lampe requires, in `lakefile.toml` (parsed as
   TOML) and in `lake-manifest.json`;
3. a source scan of every Lean file for `sorry`, `admit`, `native_decide`, `axiom`, `opaque`,
   `extern`, `implemented_by`, `unsafe` and `skipKernelTC`, and of the lakefiles for kernel
   options;
4. the rename check (`scripts/check-rename.py`, below);
5. regeneration: the six generated lookup-certificate modules must equal the output of
   `scripts/gen-lookup.py`, and the Poseidon constants of widths 2, 3 and 5 must equal those of
   the extracted `Consts.lean` (`scripts/gen-constants3.py`);
6. the build: `lake build` of Lampe, its stdlib and the extracted packages, then every proof
   module with `scripts/build.py`, one Lean process per module, with the flags `-M8192
   --tstack=65536 -DElab.async=false -DmaxRecDepth=10000 -DmaxHeartbeats=4000000`; a module
   is compiled again when its source, its imports or the dependency fingerprint change (the
   lakefile, the manifest, the toolchain, the pins, the oleans of the extracted packages, and
   the commit and changes of the Lampe checkouts);
7. the census (`Census.lean`, `scripts/census.py`): every theorem of every package module,
   auxiliary ones included, depends on a subset of the three axioms; no package module declares
   an axiom or an opaque constant; the census imports every module; and the theorems, their
   printed statements and the SHA-256 of their raw types equal
   [statements/INVENTORY.md](statements/INVENTORY.md), `statements/CERTIFICATES.md` and
   `statements/RAW.sha256`;
8. the controls (`scripts/controls.py`): `scripts/gen-controls.py` must reproduce every file
   of `controls/`; each must-fail control must fail with the first error in
   `controls/EXPECTED.tsv`, and not by a parse or name error; each must-pass copy must compile
   with the three axioms only.

`scripts/extract.sh` is not part of the check. It builds the fork's extractor, reads the three
circuits from the pocs submodule at the pin, clones the two Noir dependencies by tag (commit
and source hashes checked), runs the extractor with no network access for nargo, and compares
the output with `extracted/`: for each circuit the set of generated Lean files (its own and the
two dependency copies) must equal the committed set, and each file must be the same byte for
byte. The fork pins Rust 1.90.0 in `rust-toolchain.toml`;
the reproduction recorded here used Rust 1.95.0 (`RUST_TOOLCHAIN=1.95.0`).

Cost on a Linux laptop (16 threads, 30 GB, btrfs), with Mathlib's oleans present: the
extracted packages build in 58 s (lake, `LEAN_NUM_THREADS=4`); with `LEAN_NUM_THREADS=1`, the
413 certificate leaves build in 556 s with 4 jobs, the other 77 proof modules in 132 s with 3
jobs, the census runs in 28 s and the 80 controls in 236 s with 3 jobs. Under a 10 GiB memory cap the peaks were 5.5 GB (lake, extracted
packages) and 4.5 GB (leaves); one Lean process reached a resident size of 4.6 GB. A whole
`scripts/check.sh` from a fresh copy of the package, with `JOBS=3` and Mathlib's oleans present
(it fetches and builds Lampe and its stdlib), took 1,427 s (24 minutes) to `CHECK PASS`, with
a 4.1 GB peak; a re-run on the built tree takes about 5 minutes, most of it the controls. With a warm
cargo cache, the extractor build and the three extractions took 3 minutes.

## Layout

- `extracted/`: `deposit-0.0.0/`, `withdraw-0.0.0/`, `transfer-0.0.0/`, and
  `deps/poseidon-0.0.0/`, `deps/binary_merkle_root-0.0.0/`, as the extractor wrote them.
- `Semantics/`: lemmas about Lampe builtins the proofs use (the stdlib Poseidon2 permutation
  call, `toLeBits` on 32 Boolean bits). They are copies, under package names, of two check
  modules of the fork's stdlib (`stdlib/lampe/Checks/Semantics.lean` and `Checks/Bits.lean`).
- `Exec/`: execution lemmas (binding, heap frames, loops, arrays, integer operations).
- `Poseidon/`: the extracted permutation at widths 2, 3 and 5: round constants, constant
  additions, S-boxes, matrices, full and partial rounds, `Permutation2/3/5`, `Hash2`.
- `Determinism.lean`, `Determinism/`: deterministic builtins and the `Good` traversal, which
  pins the value of a hash call in every derivation.
- `Deposit/`, `Withdraw/`, `Transfer/`: the rule theorems, the lookup certificates and the
  non-vacuity executions of each circuit.
- `Merkle/`: the Merkle fold and the depth-0 root.
- `Census.lean`; `statements/`: the inventory, the certificate list and the raw-type hashes.
- `controls/`: the generated controls, `controls/hand/` (five written by hand) and
  `controls/EXPECTED.tsv`.
- `scripts/`: `check.sh`, `build.py`, `census.py`, `controls.py`, `gen-controls.py`,
  `gen-lookup.py`, `gen-constants3.py`, `extract.sh`, `rename.py`, `check-rename.py`,
  `rename-map.txt`, `rename-origins.txt`.
- `PINS.sha256`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`.

## Earlier names

The modules were first written with working names. `scripts/rename-map.txt` maps each earlier
module, namespace, helper-function prefix and control name to its name here, so that older
reports can be read against these files. `scripts/check-rename.py` applies the map backwards
to every module, removes the comments, and compares the SHA-256 of the result with the
original's in `scripts/rename-origins.txt`: the modules differ from their first form only in
names and comments. Nine audit modules and a regression file of the first form are not here;
the census replaces the audits.
