# Result of a run

Run of `scripts/check.sh` at commit `7eeb0b2`, on 2026-10-24. The commit that records this
file changes only this file. The machine: a Linux laptop (16 threads, 30 GB, btrfs), with
other work running at the same time. Lean 4.33.1 through elan, inside a memory-capped scope
(`systemd-run --user --scope -p MemoryMax=8G`), with `JOBS=2` and `LEAN_NUM_THREADS=2`.

## Fresh copy

The repository at `7eeb0b2` with no `.lake` and no `build` directory in `privacy-games/`, and
no untracked or ignored file there. Elan, the toolchain and Mathlib's prebuilt olean archives
were already on the machine (in the user caches of elan and Mathlib), so `lake exe cache get`
did not download them again. Lake cloned VCV-io, Mathlib and their eleven other dependencies.
The output, verbatim:

```
== tools (0s)
tools: Lake version 5.0.0-src+819816b (Lean version 4.33.1)
== pins (1s)
pins: lakefile.toml requires only VCV-io dfc7ff07 and Mathlib 0df444a3; lake-manifest.json (13 git packages) matches them and its pin
pins: no fetched packages yet; checkouts not checked
pins: the three model files (State.lean, Tx.lean, Events.lean) match PINS.sha256
== scan (1s)
scan: 99 Lean files (the model files are scanned by the gate); no sorry, admit, native_decide, axiom, opaque, extern, implemented_by, unsafe or skipKernelTC
== rename (1s)
RENAME CHECK PASS: 82 modules, code equal to the originals after the inverse map
== fetch (1s)
fetch: Completed successfully in 47053 ms!
pins: lakefile.toml requires only VCV-io dfc7ff07 and Mathlib 0df444a3; lake-manifest.json (13 git packages) matches them and its pin
pins: 13 of 13 checkouts are at their manifest revision and URL, with no tracked change, no untracked file and no ignored file outside .lake/ but lake hash files
pins: the three model files (State.lean, Tx.lean, Events.lean) match PINS.sha256
== build (147s)
build: Build completed successfully (3483 jobs). (281s)
== census (428s)
CENSUS COUNTS package: 82 modules, 1450 declarations written in the source, 775 of them theorems; 3654 constants, 2079 theorems with auxiliary ones, 959 in the inventory
CENSUS COUNTS model: 3 modules, 48 declarations written in the source, 38 theorems
CENSUS PASS: 82 modules, 1450 declarations, 775 theorems written (2079 with auxiliary ones, 959 in the inventory); 1617 theorems use axioms, all within ['Classical.choice', 'Quot.sound', 'propext']
census: 25s
== controls (453s)
gen-controls: the 16 Lean controls equal the generator output
CONTROLS PASS: 24 planted failures rejected as expected, 8 unchanged copies compile
controls: 35s
== pins after the build and the controls (488s)
pins: lakefile.toml requires only VCV-io dfc7ff07 and Mathlib 0df444a3; lake-manifest.json (13 git packages) matches them and its pin
pins: 13 of 13 checkouts are at their manifest revision and URL, with no tracked change, no untracked file and no ignored file outside .lake/ but lake hash files
pins: the three model files (State.lean, Tx.lean, Events.lean) match PINS.sha256
CHECK PASS: pins, scan, rename check, build, census (82 modules, 1450 declarations, 775 theorems; standard axioms only) and controls (24 planted failures rejected) (489s)
```

| Stage | Time |
|---|---|
| tools, pins, scan, rename check | 1 s |
| fetch: clones of the 13 dependencies, `lake exe cache get` (Mathlib oleans unpacked from the local cache), pins of the checkouts | 146 s |
| build: `lake build`, with the imported VCV-io, PolyFun, cslib and loom2 modules built from source and the 82 game modules | 281 s |
| census | 25 s |
| controls (32, two at a time) | 35 s |
| pins of the checkouts after the build and the controls | 1 s |
| whole check | 489 s |

The memory peak of the capped scope over the whole check was 4.5 GB (4.2 GiB), page cache
included. No process was killed. `.lake` takes 8.1 GiB.

## Built tree

A second `scripts/check.sh` on the built tree, at the same commit: `CHECK PASS` in 70 s
(census 24 s, controls 36 s), scope peak 1.4 GB.

## Counts

- 82 game modules; 1,450 declarations written in the source, 775 of them theorems; 3,654
  constants with the ones Lean generates; 2,079 theorems with the auxiliary ones, of which
  959 have a public name and are in `statements/INVENTORY.md`.
- Every theorem of the package and of the three model modules depends on a subset of
  `propext`, `Classical.choice` and `Quot.sound` (1,617 use at least one). No package module
  declares an axiom or an opaque constant.
- The three model modules: 48 declarations written in the source.
- README.md ("The census counts") relates these counts to the 1,487 declarations and 769
  theorems of the privacy report of 2026-10-06, not included in this repository.
- No module failed. No proof was changed.
