# Result of a run of scripts/check.sh

Run of 2026-10-24, 14:28 to 15:17 (+01:00), on a Linux laptop (16 threads, 30 GB, btrfs), from a
git worktree at commit `807c5b6`, with no change to any tracked file. Before the run, the
checkouts of Mathlib and its eight dependencies, with Mathlib's prebuilt oleans, were copied into
`../.lake/packages` and `../circuits-lampe/.lake/packages` at the pinned revisions; nothing else
was built. The run cloned the Lampe fork and built Lampe, its stdlib, the extracted circuits, the
13 model modules of the parent directory and every module of this package from source. The only
change after the run is this file.

```
JOBS=1 LEAN_NUM_THREADS=2 systemd-run --user --scope -p MemoryMax=8G -- scripts/check.sh
```

Output (the first line is from systemd-run):

```
Running as unit: refine-check.scope; invocation ID: e7ea5aa4f9e044dbbcf48dfa22dd4829
== tools (0s)
tools: Lake version 5.0.0-src+819816b (Lean version 4.33.1), githash 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
== pins (0s)
PINS PASS: 480 files (13 model modules the package imports, 462 circuits-lampe files the fold bridge rests on); requires match the manifests
== scan (1s)
SCAN PASS: 42 Lean files of the package (text) and 13 model files (code): no sorry, admit, native_decide, axiom, opaque, extern, implemented_by, unsafe or skipKernelTC; 8 lakefiles: no kernel option
== rename (1s)
RENAME CHECK PASS: 24 modules, code equal to the originals after the inverse map
== regenerate (1s)
generated controls: 8 files equal the generator output
== build (1s)
DEPS PASS (main): 18 git packages at their manifest revs, unchanged, no untracked files
Build completed successfully (3045 jobs).
build: 21 modules in 90s
== census (101s)
CENSUS PASS (main): 21 modules, 758 theorems (474 in the inventory), 624 with axioms, all within ['Classical.choice', 'Quot.sound', 'propext']
== controls (112s)
fail exit=1 fail_balance_without_rollback 14:37: unsolved goals
fail exit=1 fail_journey_swapped_words 28:71: unsolved goals
fail exit=1 fail_journey_without_path_tree 38:50: unsolved goals
fail exit=1 fail_prefixroot_drop_leaf 9:9: Application type mismatch: The argument
fail exit=1 fail_prov_step_without_fresh 10:50: Application type mismatch: The argument
fail exit=1 fail_rep_without_valid_roots 16:35: Invalid field `valid`: The environment does not contain `LeanShieldedPool.Refine.RepCore.valid`, so 
fail exit=1 fail_treelink_without_nonzero 13:43: Unknown identifier `hne`
pass exit=0 pass_input0_ballast_refuted 
fail exit=1 fail_imt_fold_direction_flipped 287:4: unsolved goals
fail exit=1 fail_imt_no_carry 58:13: unsolved goals
fail exit=1 fail_imt_proof_left_bit_true 379:6: unsolved goals
pass exit=0 pass_imt_unchanged 
CONTROLS PASS (main): 10 must-fail controls fail as recorded, 2 must-pass controls compile
== fold bridge: build (159s)
circuits-lampe: lake exe cache get: exit 0, 13s
circuits-lampe dependencies (after the fetch): 11 git packages at their manifest revs, unchanged, no untracked files
circuits-lampe: lake build of Lampe and the extracted packages: exit 0, 405s
circuits-lampe: outside state differs from the last run; 0 .trace-cl files removed
circuits-lampe: scripts/build.py Merkle.Fold Withdraw.Root Transfer.Root Transfer.Execution: exit 0, 2280s
circuits-lampe dependencies (after the build): 11 git packages at their manifest revs, unchanged, no untracked files
ok   LeanShieldedPool.Pool.State 3.0s
ok   LeanShieldedPool.Pool.Tx 2.9s
ok   LeanShieldedPool.Statements.L3 2.8s
ok   Refinement.Storage 3.3s
ok   Refinement.Rep 2.9s
ok   Refinement.Post 3.2s
ok   Tree.LeanImt 6.1s
ok   FoldBridge.Bridge 4.3s
ok   FoldBridge.Checks 3.7s
ok   FoldBridge.Compose 3.8s
BUILD PASS (fold bridge): 10 modules compiled, 3 of them in fold-bridge/
== fold bridge: census (2894s)
CENSUS PASS (fold-bridge): 3 modules, 39 theorems (31 in the inventory), 39 with axioms, all within ['Classical.choice', 'Quot.sound', 'propext']
== fold bridge: controls (2899s)
fail exit=1 fail_bridge_bad_field_no_range 234:38: Unknown identifier `hL`
fail exit=1 fail_bridge_depth_plus_one 85:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
fail exit=1 fail_bridge_direction_flipped 85:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
pass exit=0 pass_bridge_unchanged 
CONTROLS PASS (fold-bridge): 3 must-fail controls fail as recorded, 1 must-pass controls compile
== pins again (2916s)
PINS PASS: 480 files (13 model modules the package imports, 462 circuits-lampe files the fold bridge rests on); requires match the manifests
DEPS PASS (main): 18 git packages at their manifest revs, unchanged, no untracked files
DEPS PASS (fold-bridge): 11 git packages at their manifest revs, unchanged, no untracked files
CHECK PASS: pins, scan, rename check, regeneration, build, census and controls, of the package and of the fold bridge (2916s)
```

The "outside state differs" line is also printed on a first run, when there is no earlier state;
there were no `.trace-cl` files to remove. "18 git packages" counts the nine packages of the
parent's manifest and the nine of this package's manifest, which share one set of checkouts.

## Counts

| Item | Count |
|---|---|
| Lean modules of the package (`Refinement/`, `Tree/`, `Balance/`, `Journey/`, `Gas/`) | 21 |
| Model modules of the parent directory they import (pinned) | 13 |
| Theorems of the package modules, auxiliary ones included | 758 (624 with axioms, all within `propext`, `Classical.choice`, `Quot.sound`) |
| Theorems in `statements/INVENTORY.md` | 474 |
| Fold-bridge modules (`fold-bridge/FoldBridge/`) | 3 |
| Fold-bridge theorems, auxiliary ones included | 39 (all within the three axioms) |
| Theorems in `statements/FOLD-BRIDGE.md` | 31 |
| Controls of the package | 12 (10 must fail, 2 must compile) |
| Controls of the fold bridge | 4 (3 must fail, 1 must compile) |
| Modules with the rename check | 24 |
| Pinned files (`PINS.sha256`) | 480 (13 model modules, 5 other parent and package files, 462 circuits-lampe files) |
| `circuits-lampe` modules compiled for the fold bridge | 423 (354 of them lookup-certificate leaves) |
| Git packages checked at their manifest revs | 9 in `../.lake/packages`, 11 in `../circuits-lampe/.lake/packages` |

## Times

| Stage | Wall time |
|---|---|
| tools, pins, scan, rename check, regeneration | 1 s |
| build: dependency check, `lake build` of the 21 modules and the 13 model modules, pins again | 100 s |
| census | 11 s |
| controls (12, one at a time) | 47 s |
| fold bridge: `lake exe cache get` in circuits-lampe (with the Lampe clone) | 13 s |
| fold bridge: `lake build` of Lampe, its stdlib and the extracted packages | 405 s |
| fold bridge: the 423 circuits-lampe modules (`scripts/build.py --jobs 1`) | 2,280 s |
| fold bridge: the 10 modules compiled into `build/fold-bridge/lib` | 36 s |
| fold bridge: census and controls | 22 s |
| pins and dependency checkouts again | under 1 s |
| total | 2,916 s |

The earlier run with `JOBS=2` took 1,771 s; most of the difference is the circuits-lampe modules
compiled one at a time.

## Memory

The run was capped at 8 GiB. The largest single Lean process was a circuits-lampe module
(`Withdraw.Lookup.Leaf17`) at 4.4 GiB resident; the largest of the fold-bridge compile
(`FoldBridge.Compose`) at 3.8 GiB. The peak of the whole run was not recorded.
