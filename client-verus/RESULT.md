# client-verus: runs of 2026-10-24

Two runs of `check.sh` at a local commit whose `client-verus/` tree is the one of `d718d50` on this
branch, on a Linux laptop
(x86-64, 16 threads, 30 GB, btrfs). Each ran in its own systemd user scope with `MemoryMax=8G`
and `MemorySwapMax=0`, with `JOBS=4` (the default) and Rust 1.98.1 from the default rustup home.
After the runs, this file changed, and one comment block of `scripts/rename-map.txt` (the labels
of the earlier mirror rounds, which `check.sh` does not read). No file that `check.sh` reads changed.

The two transcripts below are the complete output of `check.sh`, with one substitution and no
other edit: the absolute path of the checkout, which names a home directory, is written
`<repo>`. So `<repo>/client-verus/.deps/verus-x86-linux` is the default `.deps/` directory of
this package.

## Run 1: fresh, from the release zip

`work/` and `.deps/verus-x86-linux/` were removed first. `.deps/` held a copy of the release zip,
so `check.sh` checked its sha256 and unpacked it without a download. `pocs/` held a clone of
ethsystems/pocs at `a04b8b3`.

```
tools: unpacked <repo>/client-verus/.deps/verus-0.2026.09.13.671956e-x86-linux.zip (sha256 08c85b96e0fbbbdcb1b3a9fa8943dce7598c3e7b343680820f649b4e1efda4b4)
tools: Verus 0.2026.09.13.671956e (<repo>/client-verus/.deps/verus-x86-linux), z3 4.16.0, rustc 1.98.1-x86_64-unknown-linux-gnu (48a229cea)
SOURCE ok blobs: 13 of 13 files at a04b8b3 have the pinned blob ids
SOURCE ok regions: 110 of 110 source regions have their pinned sha256
SOURCE ok diffs: 96 of 96 source-to-mirror diffs equal diffs/
SOURCE ok admissions: no local admission in 15 mirror files
SOURCE ok origins: 18 of 18 mirror and probe files equal their first checked form outside comment lines
SOURCE ok controls: 241 controls apply to their mirror
SOURCE PASS
VERUS PASS {"mirrors": 15, "mirrors_pass": 15, "verified_items": 312, "probes": 3, "probes_pass": 3, "controls": 241, "controls_refuted": 239, "controls_rlimit": ["crypto_field/p2-swap-args", "crypto_field/p4-swap-cd"], "controls_failed": [], "strict": false, "wall_s": 101.2, "verus_sum_s": 399.3, "max_rss_mib": 358, "jobs": 4, "cgroup": "/user.slice/user-1000.slice/user@1000.service/app.slice/run-p3115188-i3110475.scope", "memory_max": "8589934592", "memory_peak": "2749251584", "pass": true}
COVERAGE ok 110 relevant functions, numbered 1 to 110
COVERAGE ok Aeneas 22 (only 14), Verus 96 (only 88), both 8, union 110, none 0; 22 + 96 - 8 = 110
COVERAGE ok every Verus row, and no other, names a mirrored function
COVERAGE ok 38 rows use the effect mirrors (rpc, channel, prover_effects, tree)
COVERAGE ok 228 controls change a mirrored function, 13 change a stand-in, lemma or example; 96 of 96 Verus rows have a control of their own
COVERAGE ok 96 of 96 Verus rows re-checked here, each with a refuted control of its own; 14 Aeneas-only rows and the Aeneas half of 8 rows are frozen
COVERAGE note rows with a control stopped at the solver resource limit: 65, 66; each has another refuted control
COVERAGE ok Verus run: 15 of 15 mirror files, 312 verified items, 241 controls: 239 refuted, 2 stopped at the solver resource limit, 0 failed; 3 of 3 probes
COVERAGE ok 8 effect interfaces in the effect mirrors, 29 spec functions, 31 executable contracts; 23 interfaces in all mirrors
COVERAGE ok FUNCTIONS.md equals its regeneration
COVERAGE ok TRUSTED.md equals its regeneration
COVERAGE PASS
CHECK PASS: 110 functions (Verus 96 re-checked, Aeneas 22 frozen, both 8); 15 mirror files, 312 verified items; 241 controls: 239 refuted by Verus, 2 stopped at the solver's resource limit (rows 65 and 66, which each have a second refuted control); 3 probes; 116s
```

The Verus runs took 101 s of the 116 s (399 s summed over the 259 runs); most of the rest is
the unpacking of the zip. The 2.7 GB scope peak includes the page cache of the 1.6 GB unpacked
release; the largest Verus process had 358 MiB resident.

## Run 2: `STRICT=1`

The same checkout right after run 1, with the unpacked release left in `.deps/`.

```
tools: Verus 0.2026.09.13.671956e (<repo>/client-verus/.deps/verus-x86-linux), z3 4.16.0, rustc 1.98.1-x86_64-unknown-linux-gnu (48a229cea)
SOURCE ok blobs: 13 of 13 files at a04b8b3 have the pinned blob ids
SOURCE ok regions: 110 of 110 source regions have their pinned sha256
SOURCE ok diffs: 96 of 96 source-to-mirror diffs equal diffs/
SOURCE ok admissions: no local admission in 15 mirror files
SOURCE ok origins: 18 of 18 mirror and probe files equal their first checked form outside comment lines
SOURCE ok controls: 241 controls apply to their mirror
SOURCE PASS
VERUS FAIL control/crypto_field/p2-swap-args: 46 verified, 1 errors; function body check: Resource limit (rlimit) exceeded; consider rerunning with --profile for more details (target poseidon2: rlimit), 9.359 s, 342 MiB
error: function body check: Resource limit (rlimit) exceeded; consider rerunning with --profile for more details
   --> <repo>/client-verus/work/controls/crypto_field__p2-swap-args.rs:466:1
    |
466 | pub fn poseidon2<P: PoseidonHasher>(a: B256, b: B256) -> (r: B256)
    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

verification results:: 46 verified, 1 errors
error: aborting due to 1 previous error


VERUS FAIL control/crypto_field/p4-swap-cd: 46 verified, 1 errors; function body check: Resource limit (rlimit) exceeded; consider rerunning with --profile for more details (target poseidon4: rlimit), 7.313 s, 342 MiB
error: function body check: Resource limit (rlimit) exceeded; consider rerunning with --profile for more details
   --> <repo>/client-verus/work/controls/crypto_field__p4-swap-cd.rs:479:1
    |
479 | pub fn poseidon4<P: PoseidonHasher>(a: B256, b: B256, c: B256, d: B256) -> (r: B256)
    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

verification results:: 46 verified, 1 errors
error: aborting due to 1 previous error


VERUS FAIL {"mirrors": 15, "mirrors_pass": 15, "verified_items": 312, "probes": 3, "probes_pass": 3, "controls": 241, "controls_refuted": 239, "controls_rlimit": ["crypto_field/p2-swap-args", "crypto_field/p4-swap-cd"], "controls_failed": ["crypto_field/p2-swap-args", "crypto_field/p4-swap-cd"], "strict": true, "wall_s": 97.8, "verus_sum_s": 385.7, "max_rss_mib": 357, "jobs": 4, "cgroup": "/user.slice/user-1000.slice/user@1000.service/app.slice/run-p3134587-i3112070.scope", "memory_max": "8589934592", "memory_peak": "1271373824", "pass": false}
FAIL verus: see the VERUS lines above and <repo>/client-verus/work/logs/
CHECK FAIL (verus) after 99s
```

With `STRICT=1`, a control that stops at the resource limit is a failure. 239 of 241 controls
are refuted with their recorded diagnostic inside their target function; the two above stop at
Z3's resource limit in their target functions, `poseidon2` and `poseidon4`. A stop is not a
refutation: the mutated file does not verify, but Verus did not show it wrong either. Rows 65
and 66 each have a second control (`p2-claim-symmetric`, `p4-claim-ignores-d`) that Verus
refutes in both modes.

The outcome of the two depends on the file name that Verus is given (the crate name). After
run 2, the two mutated files of run 1 were run again by hand with the same Verus and the same
options, under other file names. The `--rlimit` runs ran four at a time.

| File name | Extra option | `p2-swap-args` | `p4-swap-cd` |
|---|---|---|---|
| the name in `work/controls/` | none | resource limit (run 1) | resource limit (run 1) |
| the working name of the first runs (`c81-p2-swap-args.rs`, `c81-p4-swap-cd.rs`; see `scripts/rename-map.txt`) | none | postcondition not satisfied, 2.0 s | postcondition not satisfied, 2.0 s |
| `crypto_field.rs` | none | postcondition not satisfied, 7.9 s | resource limit, 8.9 s |
| the name in `work/controls/` | `--rlimit 30` | resource limit, 29.3 s | resource limit, 24.0 s |
| the name in `work/controls/` | `--rlimit 100` | resource limit, 104.1 s | resource limit, 97.4 s |

## Per file

| Mirror | Verified | Errors | Wall (s) | Max RSS (MiB) | Controls refuted |
|---|---|---|---|---|---|
| `byte_records.rs` | 24 | 0 | 1.9 | 346 | 12 of 12 |
| `channel.rs` | 14 | 0 | 1.1 | 311 | 26 of 26 |
| `crypto_field.rs` | 47 | 0 | 2.3 | 343 | 14 of 16 (2 stopped at the resource limit) |
| `guards.rs` | 17 | 0 | 2.0 | 345 | 8 of 8 |
| `hash_param.rs` | 32 | 0 | 1.8 | 333 | 13 of 13 |
| `key_wrappers.rs` | 15 | 0 | 1.0 | 320 | 15 of 15 |
| `merkle_proofs.rs` | 8 | 0 | 1.1 | 328 | 7 of 7 |
| `misc_domain.rs` | 12 | 0 | 1.0 | 325 | 11 of 11 |
| `note_key.rs` | 19 | 0 | 1.2 | 322 | 10 of 10 |
| `prover_effects.rs` | 18 | 0 | 1.7 | 346 | 26 of 26 |
| `prover_fmt.rs` | 40 | 0 | 2.0 | 349 | 30 of 30 |
| `public_inputs.rs` | 28 | 0 | 1.7 | 328 | 7 of 7 |
| `rpc.rs` | 27 | 0 | 1.5 | 344 | 44 of 44 |
| `serde_wrappers.rs` | 6 | 0 | 0.8 | 313 | 8 of 8 |
| `tree.rs` | 5 | 0 | 0.7 | 295 | 8 of 8 |
| total | 312 | 0 | | | 239 of 241 |

Times and memory from run 1 (`work/results.json`). Probes: `async.rs` 2 verified, `await.rs` 3
verified, `async_trait.rs` stops with "Verus does not yet support Opaque types in trait def".

## Control diagnostics (run 1)

The errors of the 241 controls: "postcondition not satisfied" 214; that and "precondition not
satisfied" 11; "invariant not satisfied at end of loop body" 6; "precondition not satisfied" 3;
"assertion failed" 3; that and "postcondition not satisfied" 1; "unable to prove post-condition
of closure" 1 (its recorded diagnostic); the resource limit 2. No control verified, and no
control had a compiler error.

Each of the 239 refuted controls has its expected diagnostic at a location inside its target
function. Two of them also have an error elsewhere, which does not count for them:
`guards/amounts-unbounded-claim` (an assertion in `amount_bound_examples`, which relies on the
claim the control strengthens) and `misc_domain/decryption_error_note_decode_as_failed` (the
same postcondition failure, once more, reported first at the `From` specification of vstd).
`key_wrappers/enc-drop-seal-premise` is refuted in its named target `encrypt_note`. Control runs
took 1.5 s at the median and 9.3 s at most.

## Against the 2026-10-01 report

The client coverage report of 2026-10-01 is not in this repository. Its figures in the left
column are historical; the right column says what this run reproduces.

| The 2026-10-01 report (historical) | This run |
|---|---|
| Verus 96, Aeneas 22, both 8, union 110, none 0 | the route arithmetic recomputed from `source/manifest.json`; the 96 Verus rows re-checked; the Aeneas figures not reproduced |
| 38 effect functions, four mirror files, 64 verified | the same four files (`prover.rs` is `prover_effects.rs`), 27 + 14 + 18 + 5 = 64 verified |
| 104 negative controls, all failed with proof errors | the same 104, all refuted inside their target functions |
| 58 domain-core rows "inherited; not rerun" | re-run: 11 files, 248 verified items; of the 131 recorded controls, 129 refuted and 2 stopped at the resource limit; 6 added controls, all refuted |
| eight effect interfaces, 29 spec declarations, 31 executable contracts | the same, counted from the mirrors; TRUSTED.md also lists the 15 library interfaces of the domain-core mirrors |
| Aeneas 22 "inherited extraction proofs with replacements; not rerun" | not re-run here either |
