# client-verus: runs of 2026-10-24

Two runs of `check.sh` at commit `94cb442` on a Linux laptop (x86-64, 16 threads, 30 GB, btrfs),
each in its own systemd scope with `MemoryMax=6G` and no swap, `JOBS=4`, Rust 1.98.1 from the
default rustup home. Earlier runs the same day, before the wording of the control outcomes
changed, gave the same counts.

## Run 1: fresh, from the release zip

`work/` and `.deps/` removed first; `VERUS_ZIP` named a copy of the release asset.

```
tools: unpacked verus-0.2026.09.13.671956e-x86-linux.zip (sha256 08c85b96e0fbbbdcb1b3a9fa8943dce7598c3e7b343680820f649b4e1efda4b4)
tools: Verus 0.2026.09.13.671956e (.deps/verus-x86-linux), z3 4.16.0, rustc 1.98.1-x86_64-unknown-linux-gnu (48a229cea)
SOURCE ok blobs: 13 of 13 files at a04b8b3 have the pinned blob ids
SOURCE ok regions: 110 of 110 source regions have their pinned sha256
SOURCE ok diffs: 96 of 96 source-to-mirror diffs equal diffs/
SOURCE ok admissions: no local admission in 15 mirror files
SOURCE ok origins: 18 of 18 mirror and probe files equal their first checked form outside comment lines
SOURCE ok controls: 241 controls apply to their mirror
SOURCE PASS
VERUS PASS {"mirrors": 15, "mirrors_pass": 15, "verified_items": 312, "probes": 3, "probes_pass": 3, "controls": 241, "controls_refuted": 239, "controls_rlimit": ["crypto_field/p2-swap-args", "crypto_field/p4-swap-cd"], "controls_failed": [], "strict": false, "wall_s": 90.2, "verus_sum_s": 355.5, "max_rss_mib": 358, "jobs": 4, "memory_max": "6442450944", "memory_peak": "2198872064", "pass": true}
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
CHECK PASS: 110 functions (Verus 96 re-checked, Aeneas 22 frozen, both 8); 15 mirror files, 312 verified items; 241 controls: 239 refuted by Verus, 2 stopped at the solver's resource limit (rows 65 and 66, which each have a second refuted control); 3 probes; 103s
```

About 10 s of the 103 s unpack the zip. The 2.2 GB scope peak includes the page cache of the
1.6 GB unpacked release; the largest Verus process had 358 MiB resident.

## Run 2: `STRICT=1`

```
VERUS FAIL control/crypto_field/p2-swap-args: 46 verified, 1 errors; function body check: Resource limit (rlimit) exceeded; ...
VERUS FAIL control/crypto_field/p4-swap-cd: 46 verified, 1 errors; function body check: Resource limit (rlimit) exceeded; ...
VERUS FAIL {"mirrors": 15, "mirrors_pass": 15, "verified_items": 312, "probes": 3, "probes_pass": 3, "controls": 241, "controls_refuted": 239, "controls_rlimit": [...], "controls_failed": ["crypto_field/p2-swap-args", "crypto_field/p4-swap-cd"], "strict": true, ...}
CHECK FAIL (verus) after 109s
```

With `STRICT=1`, a control that stops at the resource limit is a failure. 239 of 241 controls
are refuted with their recorded diagnostic; the two above stop at Z3's resource limit. A stop
is not a refutation: the mutated file does not verify, but Verus did not show it wrong either.
With the same mutated text, Verus prints "postcondition not satisfied" for both when the file is
named as in the earlier run (`c81-p2-swap-args.rs`, `c81-p4-swap-cd.rs`; the earlier ids in
`scripts/rename-map.txt`), and for `p2-swap-args` also when the file is named `crypto_field.rs`.
Under `crypto_field.rs`, `p4-swap-cd` still stops at the limit, and under the names used here
both stop at it also with `--rlimit 30` (14 to 18 s) and `--rlimit 100` (70 to 85 s). The
solver outcome depends on the crate name that the file name gives. Rows 65 and 66 each have a
second control (`p2-claim-symmetric`, `p4-claim-ignores-d`) that Verus refutes in both modes.

## Per file

| Mirror | Verified | Errors | Wall (s) | Max RSS (MiB) | Controls refuted |
|---|---|---|---|---|---|
| `byte_records.rs` | 24 | 0 | 1.7 | 345 | 12 of 12 |
| `channel.rs` | 14 | 0 | 0.9 | 310 | 26 of 26 |
| `crypto_field.rs` | 47 | 0 | 1.9 | 341 | 14 of 16 (2 stopped at the resource limit) |
| `guards.rs` | 17 | 0 | 1.7 | 344 | 8 of 8 |
| `hash_param.rs` | 32 | 0 | 1.5 | 333 | 13 of 13 |
| `key_wrappers.rs` | 15 | 0 | 0.8 | 320 | 15 of 15 |
| `merkle_proofs.rs` | 8 | 0 | 0.9 | 327 | 7 of 7 |
| `misc_domain.rs` | 12 | 0 | 0.9 | 324 | 11 of 11 |
| `note_key.rs` | 19 | 0 | 1.0 | 321 | 10 of 10 |
| `prover_effects.rs` | 18 | 0 | 1.4 | 346 | 26 of 26 |
| `prover_fmt.rs` | 40 | 0 | 1.7 | 349 | 30 of 30 |
| `public_inputs.rs` | 28 | 0 | 1.5 | 327 | 7 of 7 |
| `rpc.rs` | 27 | 0 | 1.3 | 343 | 44 of 44 |
| `serde_wrappers.rs` | 6 | 0 | 0.7 | 309 | 8 of 8 |
| `tree.rs` | 5 | 0 | 0.6 | 293 | 8 of 8 |
| total | 312 | 0 | | | 239 of 241 |

Times and memory from run 1. Probes: `async.rs` 2 verified, `await.rs` 3 verified,
`async_trait.rs` stops with "Verus does not yet support Opaque types in trait def".

Diagnostics of the 241 controls (run 1): "postcondition not satisfied" 214; that and
"precondition not satisfied" 11; "invariant not satisfied at end of loop body" 6;
"precondition not satisfied" 3; "assertion failed" 3; that and "postcondition not satisfied" 1;
"unable to prove post-condition of closure" 1 (its recorded diagnostic); the resource limit 2.
No control verified and none failed at compilation. Control runs took 1.4 s at the median and
9.6 s at most.

## Against the frozen report

| Frozen report | Here |
|---|---|
| Verus 96, Aeneas 22, both 8, union 110, none 0 | the same, recomputed from `source/manifest.json`; the Aeneas side is taken from the report |
| 38 effect functions, four mirror files, 64 verified | the same four files (`prover.rs` is `prover_effects.rs`), 27 + 14 + 18 + 5 = 64 verified |
| 104 negative controls, all failed with proof errors | the same 104, all refuted |
| 58 domain-core rows "inherited; not rerun" | re-run: 11 files, 248 verified items; of the 131 recorded controls, 129 refuted and 2 stopped at the resource limit; 6 added controls, all refuted |
| eight effect interfaces, 29 spec declarations, 31 executable contracts | the same, counted from the mirrors; TRUSTED.md also lists the 15 library interfaces of the domain-core mirrors |
| Aeneas 22 "inherited extraction proofs with replacements; not rerun" | not re-run here either |
