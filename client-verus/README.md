# client-verus: selected properties of the 110 client functions at `a04b8b3`

This package re-checks the Verus half of the client coverage report of 2026-10-01 from public
inputs. That report is a research-phase report that this repository no longer carries ("the
frozen report" below); [FUNCTIONS.md](FUNCTIONS.md) keeps its selected property for each of the
110 functions. The client is the Rust library of the shielded pool in ethsystems/pocs (public) at
`a04b8b38969dfc2ee64de47edee7e396454204a8`, `pocs/private-payment/shielded-pool/src/lib/`, read
from the git submodule `pocs/`. `check.sh` pins the 110 source regions by hash, compares each
mirrored function with its region, runs Verus on every mirror and every negative control, and
recomputes the coverage table. The check is not a Lean theorem, imports nothing from the model,
and the model gate (`scripts/gate.sh`) never runs it. Nothing here changes the claim in the
parent README. [RESULT.md](RESULT.md) records the run.

## The claim

The client at `a04b8b3` has 110 security-relevant functions (the denominator of the frozen
report; [FUNCTIONS.md](FUNCTIONS.md) lists them with their lines and their selected property).

- **Verus, 96 functions, re-checked here.** For each of them, a selected property holds on a
  reviewed mirror of the function, under the parameter contracts of [TRUSTED.md](TRUSTED.md).
  Verus 0.2026.09.13.671956e verifies the 15 mirror files with `--no-cheating` (312 verified
  items, no local admission), and each of the 96 functions has a negative control of its own
  that Verus refutes. Of the 241 controls, 239 are refuted by Verus and 2 stop at the solver's
  resource limit (rows 65 and 66, which each have a second refuted control); `STRICT=1` counts
  the two as failures (see "Trust base").
- **Aeneas, 22 functions, frozen.** The frozen report records Aeneas extraction proofs for 22
  functions. This package does not re-run them (see "The Aeneas half").
- **Both, 8 functions.** `decode_path`, `DecryptionError::from`,
  `EncryptedTransferNotes::to_bytes`, `DepositProof::public_inputs_as_array`,
  `WithdrawProof::public_inputs_as_array`, `TransferWitness::validate_amounts`,
  `TransferWitness::sum` and `TransferWitness::validate_token_consistency` (rows 48, 61, 72, 97,
  103, 107, 108, 109). Their Verus result is re-checked here; their Aeneas result is frozen.
- **Union 110, none 0.** 22 + 96 - 8 = 110. The 14 Aeneas-only rows (71, 75, 77, 85, 86, 87,
  88, 91, 96, 98, 99, 100, 101, 102: the proof-record and Merkle-record constructors and
  accessors, `Note::with_salt`, the two `from_bytes` key constructors,
  `EncryptedTransferNotes::new` and `TransferProof::public_inputs_as_array`) have no result that
  this package re-checks.

So of the 110 rows, 96 are re-checked here and 14 rest on the frozen report alone.

## What a mirror is

A mirror is a copy of one client function in the Rust subset that Verus accepts, with a
specification (`requires`, `ensures`), proof blocks and loop invariants added. Where Verus
cannot take the real code, a named stand-in replaces it, and each file's header lists its
stand-ins:

- library types become plain types: `U256` is two `u128` halves, `B256` and `Address` are byte
  newtypes, records keep their fields and lose their serde derives;
- library calls become verified stand-ins (a hex writer, a decimal writer, a big-endian reader,
  a field reduction, `to_vec` as a verified copy) or calls of a trait parameter (below);
- the thread RNG becomes an input that holds the bytes it supplies;
- async functions stay async, but their effect calls become synchronous calls of a trait
  parameter: this Verus release rejects async functions in traits (`probes/async_trait.rs`
  fails with "Verus does not yet support Opaque types in trait def"; `probes/async.rs` and
  `probes/await.rs` verify);
- locks and `Arc` become a sequential registry parameter or an opaque handle.

The mirror is not the shipped code. Verus checks the mirror; the link to the source is the
region hash and the diff. `diffs/` holds, for each of the 96 rows, the unified diff from the
source region at `a04b8b3` to the mirrored function, and `check.sh` regenerates and compares all
of them, so every change from the source is on record. That each stand-in behaves as the library
it replaces is a reading of the library source, not a proof.

## What "selected property" means

The selected property of a row is the `ensures` clause of its mirrored function: a local property
chosen for that function, not its full functional correctness. Depth differs by row:

- stand-in semantics verified: the library behaviour is a verified stand-in, so the property
  covers the computation (the field reduction and 32-byte encoding, the hex and decimal writers,
  padding and truncation);
- hash-parameterised: Poseidon and keccak are abstract functions; the argument order, the
  encoding and the reduction of inputs and output are proved (`poseidon1/2/4`,
  `payload_commitment`, `Note::commitment`, the nullifiers, the witness constructors);
- provenance: every field of a record comes from the right input (the prover inputs, the
  witnesses, the proof records);
- parameterised: the library is a trait parameter, the local logic is proved (decryption, the
  Merkle proof generators, the TOML formatters, whose text stays abstract, and the 38 effect
  functions: RPC, channels, prover);
- thin: the function only passes its arguments on, and the proof shows that and no more. The four
  tree wrappers `CommitmentTree::insert`, `CommitmentTree::root`, `AttestationTree::insert` and
  `AttestationTree::root` (rows 49, 50, 52, 53) forward one call to lean-imt under an abstract
  successor-and-root contract; no insertion, hashing or root semantics is proved. They count as
  breadth, not assurance. By the earlier classification, 13 more rows are thin wrappers (the
  viewing-key and SEC1 wrappers, the serde wrappers, `P2pMessage::new`, `convert_receipt`,
  `b256_to_bytes`, `bytes_to_b256`).

## Parameter interfaces and trusted contracts (A3)

The mirrors take 23 trait interfaces as parameters. [TRUSTED.md](TRUSTED.md) copies each one
verbatim and counts its abstract spec functions and its executable methods; `check.sh`
regenerates it. A spec function has no body, and the proofs assume nothing about its value. An
executable method states its result in its `ensures` clause, and the proofs take that clause as
given. These clauses are the trusted contracts. "A3" names the assumption that each real library
or effect meets its contract, and that each non-trait stand-in behaves as the library it replaces.
No implementation of any interface is given or checked.

The eight interfaces of the four effect mirrors hold 29 spec functions and 31 executable
contracts:

| Interface | Remaining trusted behaviour |
|---|---|
| `rpc.rs` `RpcApi` | ABI calls, transaction submission, receipt retrieval and decoded logs |
| `rpc.rs` `Setup` | key and URL parsing, signer address, wallet and provider construction |
| `channel.rs` `Effects` | channel endpoints, send outcomes and receive outcomes |
| `channel.rs` `RegistryApi` | map operations, empty-map creation and shared-handle identity |
| `prover_effects.rs` `Effects` | TOML text and generated proof bytes, under explicit formatting bounds |
| `prover_effects.rs` `Paths` | path joins, named path components and display bytes |
| `prover_effects.rs` `Process` | file-system results, temporary directories, process output and explicit close |
| `tree.rs` `LeanImt` | the abstract insertion successor and root value |

Each effect contract describes the observations of one completed call. It does not say that a
live service answers the same way twice. The other 15 interfaces stand for libraries: the pool
hash functions, the Poseidon hasher and keccak, the k256 key API, sealring, serde and serde_json,
toml, and the lean-imt tree. Premises that the proofs state and do not prove: RNG entropy, that
sealing to a valid public key succeeds, a 64-bit `usize`, the TOML integer bounds (each integer
at most `i64::MAX`), that the attestation count fits a `u64`, and an attestation leaf index below
2^40.

## What the check says, and what it does not

The check establishes: at `a04b8b3`, the 110 source regions have the pinned hashes; each of the
96 mirrored functions differs from its region exactly as `diffs/` records; the 15 mirror files
verify under the pinned Verus with `--no-cheating` and hold no `assume`, `admit`,
`external_body`, `assume_specification`, `uninterp` or external specification; every negative
control fails at verification, not at compilation; and the coverage arithmetic holds. Everything
below is open, and the package claims none of it.

- The shipped client. Verus checks mirrors, not the compiled crate. No production-equivalence
  proof links a mirror to the code that runs.
- Effects. Nothing about RPC transport, ABI encoding, signing, chain state or receipt
  authenticity; process execution, file-system isolation, cleanup on drop or proof validity;
  channel delivery, scheduling, cancellation, fairness, liveness or lock behaviour; allocation
  failure; error-message text.
- Libraries. Nothing about Poseidon or keccak values or their cryptographic properties, curve
  arithmetic, key validity, the sealring envelope, the JSON or TOML codecs, or lean-imt.
- Functions outside the 110 (low-relevance helpers, tests, for example `mint_mock_token`).
- The Aeneas results (below).

The package never says "the client is verified". It says "for these 96 functions, the selected
property holds on the reviewed mirror under the stated contracts, and the mirror differs from the
source as recorded".

Some properties record client behaviour that a reader may not expect, as the frozen report did:
`ChannelRegistry::register` returns a `Channel` that holds an empty clone of the registry, so
that channel's `send_note` finds no recipient (`registered_channel_cannot_send` in
`channel.rs`); `prove_withdraw` has no client amount guard, and the full amount reaches the prover;
`get_attestation_count` and `get_attestation_leaf` verify only under their fit preconditions
(the source uses `unwrap`, which panics outside them); `add_attestation` reads the attestation
count before it submits, and nothing ties that count to the eventual insertion.

## The Aeneas half

The 22 Aeneas rows were already "inherited extraction proofs with replacements; not rerun" in the
frozen report: Charon and Aeneas extracted the real function bodies against plain-Rust stand-ins
for the library types, and Lean proofs over the extraction gave the selected property. Those
extraction projects are not part of this repository. They used an Aeneas nightly
(2026.09.15-505b6ca), Charon 0.1.254, a nightly rustc and Lean libraries ported for it, and
several of them were written against an earlier commit of the client. This package does not
re-run them: the Aeneas counts (22, of which 14 Aeneas-only and 8 both) are taken from the frozen
report, and FUNCTIONS.md marks each Aeneas-only row "(frozen)". The 8 "both" rows are re-checked
here on the Verus route only.

## Trust base

What the result rests on, and that no proof checks:

- Verus 0.2026.09.13.671956e (commit `671956ec`), with its vstd and its bundled Z3 4.16.0: the
  verifier and the solver.
- Rust 1.98.1 (`48a229cea`), the toolchain this Verus release names: `rust_verify` is built
  against its compiler driver.
- The mirrors' stand-ins and the trait contracts (A3, above).
- `--no-cheating` and the admission scan exclude local admissions; they do not exclude a
  specification that is weaker than its row's one-line summary. FUNCTIONS.md summarises; the
  `ensures` clauses in `mirrors/` are the statements.

Every input from outside this repository, and how `check.sh` treats it. "Hash" means the run
stops when the input differs from its pin; "trusted" means the run reads it as it is.

- The source (`POCS`, default the submodule `pocs/`), a git object store. Hash: the commit must
  exist, the 13 client files at that commit must have the pinned blob ids, and the 110 regions,
  read from those blobs and never from the working tree, must have their pinned sha256.
  Trusted: git's object store returns the objects that the ids name.
- The Verus release, from a zip (`VERUS_ZIP`, or the download into `.deps/`). Hash: the sha256
  of the zip, which covers every file in it. The download itself is trusted only to arrive.
- The Verus release, from a directory (`VERUS_DIR`, or a `.deps/verus-x86-linux` left by an
  earlier run). Hash: `verus`, `rust_verify`, `vstd.vir` and `z3`; the version and commit in
  `version.json` and the Z3 version must match. Trusted: every other file in the directory (the
  vstd and builtin libraries, the macro libraries).
- The Rust toolchain that rustup installed. Hash: `librustc_driver`; the commit that `rustc -vV`
  reports must match. Trusted: rustup and the rest of the toolchain (the standard library).
  `check.sh` sets `RUSTUP_TOOLCHAIN`, so a rustup toolchain file in a parent directory does not
  choose another toolchain.
- The work directory (`WORK`, default `work/`). `check.sh` deletes and recreates it, then writes
  the controls, logs and results there and reads them back. Trusted: nothing else writes there
  during the run.
- `/proc/self/cgroup` and the cgroup's `memory.max` and `memory.peak`. Read only for the memory
  figures of the summary; they do not change pass or fail.
- The host tools: bash, python3, git, sha256sum, unzip, curl and coreutils. Trusted, not hashed.

`TOOLS_UNPINNED=1` turns the Verus and driver hash checks into notes on the result line; the
versions must still match. The scripts are checks against mistakes, not against a hostile
package or host.

Solver limits. Two controls, `crypto_field/p2-swap-args` and `crypto_field/p4-swap-cd` (the
`poseidon2` arguments swapped, the last two `poseidon4` arguments swapped), stop at Z3's
resource limit (`rlimit`) instead of a refuted postcondition. Such a stop is not a refutation:
the mutated file does not verify, but Verus did not show it wrong either. `check.sh` reports the
two apart and does not fail on them, because rows 65 and 66 each have a second control
(`p2-claim-symmetric`, `p4-claim-ignores-d`) that Verus refutes; every Verus row must have a
refuted control of its own. `STRICT=1` counts the two as failures. Their outcome depends on the
file name Verus is given (the crate name): the same mutated text, under the file names of the
earlier run, ends with "postcondition not satisfied" (RESULT.md).

## Pins

[PINS.txt](PINS.txt) holds them:

- ethsystems/pocs `a04b8b38969dfc2ee64de47edee7e396454204a8`, directory
  `pocs/private-payment/shielded-pool/src/lib`, and the blob ids of the 13 client files that hold
  the 110 regions. [source/manifest.json](source/manifest.json) holds each region's lines and
  sha256 (lines `line..end`, joined with newlines, plus one trailing newline).
- Verus: the release URL, the zip sha256 `08c85b96…` (the digest GitHub lists for the asset) and
  size, the version and commit, and the sha256 of `verus`, `rust_verify`, `vstd.vir` and `z3`.
- Rust: the toolchain name, the rustc commit and the sha256 of `librustc_driver`.
- `mirrors/VERIFIED.txt`: the verified count of each mirror file, as recorded when the file was
  first checked, and of the two passing probes.
- `scripts/origins.txt`: for each mirror and probe, the sha256 of the file as first checked and of
  its code lines; the files here differ from that form in comment lines only.

## Re-check

Start from a checkout of this repo with the submodule, on x86-64 Linux:

```
git clone --recurse-submodules https://github.com/ethsystems/shielded-pool-model.git
# or, in an existing checkout:
git submodule update --init client-verus/pocs
```

Install rustup and the toolchain that Verus needs:

```
rustup toolchain install 1.98.1-x86_64-unknown-linux-gnu --profile minimal
```

Then:

```
cd client-verus
./check.sh
# expect the last line: CHECK PASS: 110 functions (Verus 96 re-checked, Aeneas 22 frozen, both 8); ...
```

Without `VERUS_DIR` or `VERUS_ZIP`, `check.sh` downloads the Verus release zip (486 MB) into
`.deps/`, checks its sha256 and unpacks it (1.6 GB). `VERUS_ZIP=/path/to/zip` uses a downloaded
zip; `VERUS_DIR=/path/to/verus-x86-linux` uses an unpacked release, whose file hashes must still
match. `VERUS_FETCH=0` forbids the download. `JOBS` sets the number of parallel Verus runs
(default 4); `WORK` the work directory (default `work/`). In order, `check.sh`:

1. checks the tools: the Verus version, commit and file hashes, Z3 4.16.0, and the rustc
   commit and driver hash of the 1.98.1 toolchain; on a miss it names the release and stops;
2. runs `scripts/source-check.py`: the pocs commit and the 13 blob ids, the 110 region hashes,
   the 96 diffs, the admission scan, the comment-only check against `scripts/origins.txt`, and
   that each control's replacement text occurs exactly once;
3. runs `scripts/verus-run.py`: each mirror with `--no-cheating` must verify with 0 errors and
   its recorded count; `probes/async.rs` and `probes/await.rs` must verify and
   `probes/async_trait.rs` must stop with the unsupported-feature diagnostic; each control (its
   mirror with one replacement) is refuted when Verus reaches verification, reports at least
   one error, reports no compiler error, and prints its expected diagnostic at a location
   inside the control's target function. The target is the function that the replacement
   changes; one control, `key_wrappers/enc-drop-seal-premise`, weakens a trait contract and
   names its caller `encrypt_note` as its target. An expected diagnostic in another function
   does not count. A stop at the resource limit in the target is reported apart, and any other
   outcome (it verifies, fails to compile, or fails only outside its target) fails the check;
4. runs `scripts/coverage.py`: the route counts (Aeneas 22, Verus 96, both 8, union 110, none
   0), the mapping of every control to the function it changes (each of the 96 rows must have
   a refuted control of its own), the eight effect interfaces with 29 and 31 contracts, and FUNCTIONS.md and
   TRUSTED.md against their regeneration.

Exit 0 means `CHECK PASS`. Each Verus run writes its log to `work/logs/`, and
`work/results.json` holds every result. A failing control prints its Verus output.

The 241 controls come in three groups. The 104 controls of the four effect mirrors are two per
target function: a mutated body and a strengthened postcondition (the `// STRENGTH` markers).
The 131 controls of the 11 domain-core mirrors are those recorded when each file was first
checked; 10 of them (in `byte_records.rs`) were reconstructed then from the description of the
original controls, which were not kept. Six controls were added in this package, two each for
the three rows that had none (`decode_path`, `DecryptionError::from`,
`EncryptedTransferNotes::to_bytes`). A refuted control shows that the proof does not accept the changed
function or the stronger claim; it does not show that the changed claim is false.

Cost on a Linux laptop (16 threads, 30 GB, btrfs), measured 2026-10-24: `check.sh` 103 s with
`JOBS=4`, of which about 10 s unpack the zip and 90 s are the 259 Verus runs (356 s summed).
Each Verus run takes 0.4 to 10 s and at most 358 MiB resident; under a 6 GiB scope the peak was
2.2 GB, most of it page cache from the unpacked release. `.deps/` takes 1.6 GB unpacked, plus
the 486 MB zip when `check.sh` downloads it; `work/` about 5 MB. Neither is tracked.

## Layout

- `check.sh`: the check.
- `mirrors/`: the 15 mirror files and `VERIFIED.txt`. The four effect mirrors are `rpc.rs`,
  `channel.rs`, `prover_effects.rs` and `tree.rs` (38 rows); the 11 domain-core mirrors are
  `guards.rs`, `note_key.rs`, `public_inputs.rs`, `hash_param.rs`, `crypto_field.rs`,
  `prover_fmt.rs`, `misc_domain.rs`, `merkle_proofs.rs`, `key_wrappers.rs`, `serde_wrappers.rs`
  and `byte_records.rs` (58 rows).
- `probes/`: three Verus feature probes (async, await, async trait).
- `controls/controls.json`: the 241 controls, each a mirror, one text replacement and the
  expected diagnostic; a control of an effect mirror also names its function, and one control
  names a `target` (step 3 above).
- `source/manifest.json`: the 110 rows: function, file, lines, region sha256, route, the mirror
  file and the marker that finds the mirrored function, the selected property.
- `diffs/`: the 96 source-to-mirror diffs, named by row number.
- `FUNCTIONS.md`, `TRUSTED.md`: generated tables (above).
- `scripts/`: `source-check.py`, `verus-run.py`, `coverage.py`, `common.py`, `origins.txt`,
  `rename-map.txt`.
- `PINS.txt`, `RESULT.md`, and `pocs/`: the git submodule, ethsystems/pocs at `a04b8b3`.

## Earlier names

The mirrors were first written and checked in three earlier runs under working file names and
labels, which the frozen report uses. [scripts/rename-map.txt](scripts/rename-map.txt) maps each
earlier label, file name and control id to its name here. Three earlier mirror files are not
carried over: two `u128` mirrors of the public-input serializers, superseded by
`public_inputs.rs` over the full `U256` domain, and a mirror of the transfer guard before
ethsystems/pocs PR #12, which is not the body at `a04b8b3`. A variant of `validate_amount` with
trusted library specifications, which fails `--no-cheating`, is not carried over either. No row
depends on them.

## Where it comes from

The frozen report gives the numbers this package re-checks: 110 relevant functions, Verus 96,
Aeneas 22, both 8, and 104 negative controls for the 38 effect functions, all refuted. The
mirrors here are those files with their comments rewritten (labels, machine names and references
to files that are not here) and their code unchanged (`scripts/origins.txt`); one file,
`byte_records.rs`, was written against an earlier commit of the client, and its regions are
byte-identical at `a04b8b3`. The frozen report's verified count for the effect mirrors (64) and
its 104 controls are reproduced here; the 58 domain-core rows, "inherited, not rerun" there, are
re-run here, with their own controls.
