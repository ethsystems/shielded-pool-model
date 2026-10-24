# Result of a run

Run of `scripts/check.sh` on 2026-10-24, on a Linux laptop (16 threads, 30 GB, btrfs), Lean
4.33.1 through elan, inside a memory-capped scope
(`systemd-run --user --scope -p MemoryMax=10G`), with `JOBS=2` and `LEAN_NUM_THREADS=2`.

## Fresh copy

A fresh clone of the repository at the commit that added this package, with no `.lake`
directory; elan, the toolchain and Mathlib's prebuilt olean archives were already on the
machine (in the user caches of elan and Mathlib), so `lake exe cache get` did not download
them again. Lake cloned VCV-io, Mathlib and their eleven other dependencies.

```
CENSUS COUNTS package: 82 modules, 1450 declarations written in the source, 775 of them theorems; 3654 constants, 2079 theorems with auxiliary ones, 959 in the inventory
CENSUS COUNTS model: 3 modules, 48 declarations written in the source, 38 theorems
CENSUS PASS: 82 modules, 1450 declarations, 775 theorems written (2079 with auxiliary ones, 959 in the inventory); 1617 theorems use axioms, all within ['Classical.choice', 'Quot.sound', 'propext']
CONTROLS PASS: 20 planted failures rejected as expected, 8 unchanged copies compile
CHECK PASS: pins, scan, rename check, build, census (82 modules, 1450 declarations, 775 theorems; standard axioms only) and controls (20 planted failures rejected) (362s)
```

| Stage | Time |
|---|---|
| tools, pins, scan, rename check | 1 s |
| fetch: clones of the 13 dependencies, `lake exe cache get` (Mathlib oleans unpacked from the local cache) | 77 s |
| build: `lake build`, with the imported VCV-io, PolyFun, cslib and loom2 modules built from source and the 82 game modules | 219 s |
| census | 28 s |
| controls (28, two at a time) | 37 s |
| whole check | 362 s |

The memory peak of the capped scope over the whole check was 10.2 GB (9.5 GiB). That figure
counts the page cache of the clones and of the unpacked oleans; no process was killed. The
Lean processes need much less: in separate capped runs on the same machine, the scope peaks
were 3.4 GB for the first `lake build` (170 s, the same work as the build stage above),
2.5 GB for the controls and 2.1 GB for a whole check on the built tree. `.lake` takes 8.3 GB.

## Built tree

A second `scripts/check.sh` on the built tree: `CHECK PASS` in 67 s (census 27 s, controls
31 s), scope peak 2.1 GB.

## Counts

- 82 game modules; 1,450 declarations written in the source, 775 of them theorems; 3,654
  constants with the ones Lean generates; 2,079 theorems with the auxiliary ones, of which
  959 have a public name and are in `statements/INVENTORY.md`.
- Every theorem of the package and of the three model modules depends on a subset of
  `propext`, `Classical.choice` and `Quot.sound` (1,617 use at least one). No package module
  declares an axiom or an opaque constant.
- The three model modules: 48 declarations written in the source.
- README.md ("The census counts") relates these counts to the 1,487 declarations and 769
  theorems of the frozen report.
- No module failed. No proof was changed.
