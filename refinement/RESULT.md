# Result of a run of scripts/check.sh

Run of 2026-10-24, 11:45 to 12:15 (+01:00), on a Linux laptop (16 threads, 30 GB, btrfs), from a
fresh git worktree of commit `2ede419` of this branch. Before the run, the Mathlib checkout and
its prebuilt oleans (and those of Mathlib's dependencies) were copied into `../.lake/packages`
and `../circuits-lampe/.lake/packages` at the pinned revisions; nothing else was built. The run
cloned the Lampe fork and built Lampe, its stdlib, the extracted circuits, the 13 model modules of
the parent directory and every module of this package from source.

```
JOBS=2 LEAN_NUM_THREADS=2 systemd-run --user --scope -p MemoryMax=10G -- scripts/check.sh
```

Last line:

```
CHECK PASS: pins, scan, rename check, regeneration, build, census and controls, of the package and of the fold bridge (1771s)
```

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
| Pinned files (`PINS.sha256`) | 24 |
| `circuits-lampe` modules compiled for the fold bridge | 423 (354 of them lookup-certificate leaves) |

## Times

| Stage | Wall time |
|---|---|
| tools, pins, scan, rename check, regeneration | 1 s |
| build: `lake build` of the 21 modules and the 13 model modules | 91 s |
| census | 9 s |
| controls (12, two at a time) | 24 s |
| fold bridge: `lake exe cache get` in circuits-lampe | 13 s |
| fold bridge: `lake build` of Lampe, its stdlib and the extracted packages (with the Lampe clone) | 342 s |
| fold bridge: the 423 circuits-lampe modules (`scripts/build.py --jobs 2`) | 1,236 s |
| fold bridge: the 10 modules compiled into `build/fold-bridge/lib` | 28 s |
| fold bridge: census and controls | 13 s |
| total | 1,771 s |

A re-run on the built tree takes about 75 s; with `FOLD_BRIDGE=0` the package stages of a fresh
copy take about 140 s.

## Memory

Under the 10 GiB cap, the peak of the whole run (cgroup `memory.peak`, page cache included) was
8.38 GB. The largest single Lean process was a circuits-lampe module at 4.6 GB resident; the
largest of the fold-bridge compile at 4.0 GB.
