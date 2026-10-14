# hash-agreement: three transcriptions of Poseidon2 (x^5, t = 3) agree as functions

This package proves, in Lean 4 over the BN254 scalar field, that three transcriptions of
the two-input Poseidon hash that the shielded pool uses agree as functions. The spec and
the parent model call it Poseidon2, as they call the four-input and one-input instances
Poseidon4 and Poseidon1; it is the original Poseidon (x^5, t = 3, 8 full and 57 partial
rounds), not the later Poseidon2 design. The three are the plain textbook
reference, the Noir library's optimized permutation, and the Solidity library's Yul body
cut into rounds. The transcriptions are the trusted part; the Lean kernel checks the rest,
all 65 rounds, with the three standard axioms only. The package is separate from the model
in the parent directory: its own Lake project (Lean 4.33.1 and Mathlib, the same pins as
the root), its own `check.sh` with an expected theorem census, inputs and generators
committed with hashes, and no import of any model module. The root gate does not build
it. Nothing here changes the claim in the parent README.

## The claim

> Over `ZMod F` with F the BN254 scalar modulus, `noirHash2 a b = plainHash2 a b` and
> `solHashSeg a b = plainHash2 a b` for all `a b`, hence `solHashSeg a b = noirHash2 a b`.
> `plainHash2` is the textbook Poseidon with t = 3, 4 + 57 + 4 rounds and x^5 S-box,
> with the constants and MDS matrix extracted from `PoseidonT3.sol`. `noirHash2` is a
> hand transcription of `permute` and `hash_2` from noir-lang/poseidon v0.3.0, with the 81
> optimized round constants, the presparse matrix and the 57 sparse factors parsed from
> `consts.nr` (`x5_3_config`). `solHashSeg` is a machine translation of the Yul text of
> `PoseidonT3.sol` (poseidon-solidity 0.0.5), the same statements in the same order, cut
> at the 64 mix blocks. The Lean kernel checks the equalities for all inputs, 65 rounds,
> axioms `propext`, `Classical.choice`, `Quot.sound` only.

The claim is about the transcriptions. It does not say that the Noir circuit and the
Solidity contract compute the same hash: that needs the open items below.

## The theorems

All in `HashAgreement/Full.lean` unless noted. `K` is `ZMod F`, `St` is `K × K × K`.

| Theorem | Statement |
|---|---|
| `noirPermute_eq_plainPerm` | `∀ s : St, noirPermute s = plainPerm s` |
| `noirHash2_eq_plainHash2` | `∀ a b : K, noirHash2 a b = plainHash2 a b` |
| `solHashSeg_eq_plainHash2` | `∀ a b : K, solHashSeg a b = plainHash2 a b` |
| `solHashSeg_eq_noirHash2` | `∀ a b : K, solHashSeg a b = noirHash2 a b` |
| `round0` .. `round64` | one Noir round against one plain round through the boundary maps (below) |
| `solR0_eq` .. `solR63_eq`, `solLast_eq` | one Solidity segment against one plain round, boundary map `x + c_j` |
| `noirPermute_eq_fold`, `perm_eq_of_rounds` (`Base.lean`) | the loop-shaped `noirPermute` is the 65-round fold; the 65 round lemmas compose |
| `round3D`, `round4D`, `round60D` (`RoundsD.lean`) | three rounds proved again by direct expansion, a cross-check of the generic route |
| `round4_wrong_false` (`Controls.lean`) | the mutated round-4 statement that `Neg/RoundsNeg.lean` fails to prove is false |

`expected.json` pins the exact statement and axiom list of all 155 declared theorems. The
census also walks the 2,041 auxiliary lemmas that `decide +kernel` and the equation
compiler generate and requires standard axioms on each.

## What stays open

The package does not say "Noir equals Solidity". It is not a security claim. Open:

1. **Transcription faithfulness.** The transcribers are trusted. The Noir side is parsed
   from `consts.nr` by `scripts/common.py` and transcribed by hand from `mod.nr` and
   `bn254.nr` (`permute`, `apply_matrix`, `sigma`, `hash_internal`; `pow_32(alpha)` with
   `alpha() = 5` read as `^ 5`; `std::as_witness` read as no value effect). The Solidity
   side is translated from the Yul text by `scripts/gen_sol.py`, a translator specialized to
   this file: `mulmod(a, b, F)` is field multiplication, `add` is field addition (the
   hash-differential record bounds every `add` below 3.999 p, so no `uint256` wrap; this
   package does not re-check that bound), `mod(e, F)` is dropped. Nothing proves that either
   transcription matches what the Noir compiler or the EVM executes.
2. **The monolithic-to-segmented Solidity cut.** `Sol.lean` carries both the one-term
   translation `solHash` (816 multiplications, one per `mulmod`) and its cut `solHashSeg`.
   `solHash = solHashSeg` is a trusted step: the generator asserts that no variable crosses a
   cut except the three state words, and the Python replay agrees on 300 vectors, but the
   Lean equality is not proved. A `rfl` attempt stopped at the 2,000,000 heartbeat limit
   after 81 s; the unbounded retry did not finish in 2,700 s (research repo,
   `evidence/2026-10-11/a9proto-solseg/run.log`). Every theorem here is about `solHashSeg`.
3. **The Lampe link.** `noirHash2` is a transcription of the library source, not the
   extracted circuit code. In the research repo's reading, Lampe's extraction proves that
   the extracted `permute` computes a pure function over Lampe's own field type; that this
   function equals `noirPermute`, with equal tables, is not proved, and Lampe is not part
   of this package.
4. **EVM semantics.** Nothing about the deployed verifier or contract, about bytecode
   against the Yul text, `mload`/`mstore`, calldata encoding or the addition bounds. The
   only EVM execution that enters is the 300 recorded outputs in `inputs/vectors/`, used as
   a test, not as a premise.
5. **Collision resistance.** Nothing. `CryptoHyp` in the parent model stays as it is, a
   hypothesis on one history, and this package does not discharge any part of it. It
   narrows no simplification of the model, because `PrimSpec.nullify` stays opaque. It is
   evidence that the contract and the circuits hash Merkle nodes the same way (CLAIMS.md).

Also out of scope: the four-input commitment hash and the one-input key hash, Merkle paths,
and anything about the circuits that call `hash_2`.

## The round cut

Both permutations are 65 rounds: 4 full, 57 partial, 4 full. The plain round `j` adds the
constant triple `c_j`, applies the S-box to all three words (full) or to word 0 (partial),
then mixes with `M`. The Noir library stores the same instance in the optimized shape of
the Poseidon paper: constants folded through the mixes, each partial-round mix split into
a sparse factor, and the mix of round 3, the last full round before the partial ones,
replaced by the presparse matrix `P`.

`noirRound j` cuts the library's loops at the same 65 places; `noirPermute_eq_fold`
proves that the loop shape is that fold: a kernel check of the prologue constants, the
three loops rewritten to folds over `noirRound` with `List.foldl_ext`, a `decide`-checked
split of `List.range 65`, then `rfl`. The per-round
lemma is

    noirRound j (L j x) = L (j + 1) (plainRound j x)

where `L j` is an affine boundary map: `x + c_j` at the full-round boundaries,
`x * T_j + v_j` at the partial ones (`aff (Tw j) (vw j)`), and the identity after round
64. `T_j` is the backward factor `A'` of the accumulated matrix (`A = A' * S`,
`A_(r-1) = M * A'_r`), so that `T_j * S_(j-4) = M * T_(j+1)` in execution order; the
generic lemma `partial_step` needs that equation, the block shape of `T_j` (first row
`(1, 0, 0)`, first column `(1, 0, 0)`), `v_j` word 0 equal to `c_j` word 0, and the forward
propagation of `v`. `T_j` and `v_j` come from a Python witness
computation (`scripts/common.py`, `witnesses`); they are untrusted, because each round
lemma checks every equation it uses with `decide +kernel`. The generic lemmas
(`partial_step`, `full_step`, `pre_step`, `last_step`) hold over variables and are proved
by `linear_combination` or `ring`. `perm_eq_of_rounds` composes the 65 instances.

On the Solidity side the cut is syntactic: the Yul text applies `M` and adds the next
round constants in one block, so `solR_j` takes `x + c_j`, applies the S-box and the mix,
and returns `plainRound j x + c_(j+1)`, for `j` from 1 to 63. The ends differ: `solR0`
takes the two inputs with word 0 fixed at zero, as `hash` does, and `solLast` returns
word 0 only. Each `solR_j_eq` is `ring` after unfolding; the first segment also reduces
the folded literals `M_0i * C00^5` mod F (`reduce_mod_char!`).

What is real content and what holds by construction: `noirPermute = plainPerm` is real
content, the two sides meet only through the kernel-checked identities on tables that come
from different files. `solHashSeg = plainHash2` is mostly by construction, because both
sides use constants extracted from the same Yul text; its content is the folded first-round
literals, the S-box chains, the mix orientation, the full/partial schedule, and the fusion
of each mix with the next round constants. The Noir and plain MDS matrices come from
different files and are the same numbers.

## Trust base

- The Lean 4.33.1 kernel and elaborator, Mathlib at the root's pin, and Lake.
- `scripts/common.py` (the `consts.nr` parser and the `sol_params.json` loader),
  `scripts/gen_sol.py` (the Yul translator and the segmenter) and the hand transcription
  of `permute`, `sigma`, `apply_matrix` and `hash_internal` in `scripts/gen_lean.py`.
- `inputs/sol_params.json`, the hash-differential record's extraction of the plain
  constants and `M` from `PoseidonT3.sol`. The Solidity round lemmas re-check every value
  against the Yul literals; the static `add` bound is not re-checked.
- The cut `solHash = solHashSeg` (open item 2).
- `Census.lean` reads printed output of Lean code that imports the package. Code that runs
  during elaboration could change that output, so the census is a check against mistakes,
  not against a hostile package; the source scan and the review of the hand-written files
  cover that case.

## Inputs

`inputs/PROVENANCE.md` gives each file's origin. The hashes:

| File | sha256 |
|---|---|
| `inputs/PoseidonT3.sol` | 08a7493be37838166954af6c77d583d797cc17d37673196498fc70cbf557831c |
| `inputs/noir/bn254/consts.nr` | 0e1ce6ec6ed2ebbab52739ab07a2ab7a9cfb9b479cb012527f5e08447677dfd2 |
| `inputs/noir/mod.nr` | d0b044a17c0d7c26470137c17b7a43c172051da8ea74e56797323f3cc07a5a84 |
| `inputs/noir/bn254.nr` | 4800b851b4b0e2c71cd6456efb021be865e4fde040c6e63797b6f157c042653a |
| `inputs/noir/bn254/perm.nr` | 1daf55657af0418deb717b74cd45a1a4e9ac9d59678335cf0e677ed8a682be23 |
| `inputs/sol_params.json` | cbca794b53c67844b9ab3cd21203f6720e291b6c8639cece18ff37b3aa01f2b8 |
| `inputs/vectors/inputs.json` | ab284c7668a2ba195000a4c8eb9ca709d74dc61f27c60fa613025b1f490f0bcd |
| `inputs/vectors/sol_outputs.txt` | 8acc9017447ec7f85e804858d1ccbce78723119fae4688f905a8e32fa844152f |

## Controls

- `Neg/RoundsNeg.lean` must fail to build. It repeats the passing `round4` and a copy,
  `round4_wrong`, that uses the sparse factor of round 5 at round 4 with the same proof
  text. `check.sh` requires exactly two errors, both inside `round4_wrong`, both of the
  form "Tactic `decide` proved that the proposition ... is false": the kernel checks of
  `hTS` (`T * S = M * T'`) and `hv'` (the propagated `v`). Nothing else fails, so the proof
  depends on the constants and not only on the proof shape.
- `HashAgreement/Controls.lean` must build: `round4_wrong_false` proves the mutated
  statement false at `x = (1, 2, 3)` by kernel evaluation.
- `test/Vectors.lean` runs the 300 pairs through `solHash`, `solHashSeg`, `plainHash2` and
  `noirHash2` by compiled evaluation and must print `(300, 300, 300, 300)`;
  `scripts/check_vectors.py` does the same with the Python models. Both are tests, not
  proofs; they tie the Lean definitions to the recorded EVM outputs.

## Re-check

You need git, bash, python3 (3.10 or later), elan and the Mathlib build of the root
project (about 7.5 GB). The package pins the same Mathlib commit as the root. On the first
run `check.sh` copies the root's `.lake/packages` into `hash-agreement/.lake/packages`,
trying a macOS clone (`cp -Rc`), then a Linux reflink (`cp --reflink=auto`), then a plain
copy of about 7 GB; the reflink took 5 s on btrfs. Without a root build it runs
`lake exe cache get`, which needs the network.

```
cd hash-agreement
./check.sh      # expect the last line: REPLAY CHECK PASS: 155 theorems, ...
```

Use `check.sh` rather than a bare `lake build`: the check rebuilds from scratch, regenerates
the Lean files and compares everything with `expected.json`. In order, it:

1. checks the Lean and Python versions;
2. hashes every tracked file except README.md, expected.json and .gitignore, the inputs
   separately from the scripts and docs;
3. regenerates the eight generated files (`HashAgreement/*.lean`, `Neg/RoundsNeg.lean`,
   `test/Vectors.lean`, `blocks.sha256`) with `scripts/gen_lean.py` into a temporary
   directory and requires byte equality with the committed ones;
4. runs the Python vector replay;
5. rejects `sorry`, `admit`, `native_decide`, `axiom`, `extern`, `implemented_by`,
   `unsafe` and `opaque` in every Lean file except `Census.lean`;
6. provides the Mathlib dependencies as described above;
7. removes `.lake/build` and builds the five modules one at a time, timing each and
   reading its peak RSS, and rejects a reported `sorry`;
8. runs `Census.lean`: for every theorem in a `HashAgreement.*` module, its exact
   statement and its axioms (`Lean.collectAxioms`, as `#print axioms`); any axiom outside
   `propext`, `Quot.sound` and `Classical.choice` on any theorem, auxiliary lemmas included,
   and any declared axiom or opaque constant, fails;
9. compiles `Neg/RoundsNeg.lean`, which must fail as the Controls section says;
10. runs `test/Vectors.lean`;
11. compares everything with `expected.json`. A missing, duplicate or unexpected declared
    theorem, input or file fails, as does any changed statement or axiom list. The
    auxiliary lemmas are checked for axioms only; their names and count are not pinned.

`expected.json` is the reviewed output of the first run (`build/observed.json` without its
timing section). `build/` holds the logs of the last run.

## Measured cost

One Linux laptop (xps26, btrfs), `LEAN_NUM_THREADS=2`, Mathlib oleans already present,
modules built one at a time:

| Step | Wall | Peak RSS |
|---|---|---|
| `HashAgreement.Base` | 2.8 s | 2.32 GiB |
| `HashAgreement.Sol` | 3.3 s | 2.19 GiB |
| `HashAgreement.RoundsD` | 2.3 s | 2.19 GiB |
| `HashAgreement.Controls` | 1.5 s | 2.10 GiB |
| `HashAgreement.Full` | 14.3 s | 3.15 GiB |
| build, five modules | 24.2 s | 3.15 GiB |
| whole `check.sh` | 32.7 s | |

The run of 2026-10-13 that produced `expected.json`; each run writes its own numbers to
`build/observed.json` (`timing`). Peak RSS is `ru_maxrss` of the largest Lean process
(`os.wait4`), not a cgroup peak. The three logged runs that day gave 12.2 to 14.3 s and
3.15 to 3.20 GiB for `Full`. The research repo measured the same proof as one monolithic file at
19.4 s and 3.18 GiB. The Lean processes run with `-M4096`.

## Files

- `HashAgreement/Base.lean`: the field, the plain reference, the Noir transcription, the
  witness tables, the round-cut lemmas, the generic lemmas and the composition.
- `HashAgreement/Sol.lean`: `solHash` and the cut `solR0` .. `solR63`, `solLast`,
  `solHashSeg`.
- `HashAgreement/Full.lean`: the 65 round lemmas, the Noir theorems, the 65 Solidity
  segment lemmas, the Solidity theorems.
- `HashAgreement/RoundsD.lean`, `HashAgreement/Controls.lean`, `Neg/RoundsNeg.lean`,
  `test/Vectors.lean`: see Controls.
- `scripts/common.py`, `gen_sol.py`, `gen_lean.py`, `check_vectors.py`, `replay.py`;
  `check.sh`; `Census.lean`; `expected.json`; `blocks.sha256` (the sha256 of each
  generated block).
- `inputs/`: the pinned inputs and `PROVENANCE.md`.

The generated files are committed so that the proof can be read without running Python;
`check.sh` regenerates them and fails on any difference.

## Where it comes from

The proof is the night prototype `experiments/a9proto/` of the research repo
(oskarth/lean-shielded-pool, branch `dispatch/xo-fv-lean`, last change to the directory at
commit `487569f`), reported in `evidence/2026-10-07/a9proto/REPORT.md` and reviewed there
in four rounds. Research `Full.lean` has sha256
`30350003ea44c7eaf34cee647c841a3277b264ceee602d1ef1b7d7124bd47172`. The proof text here is
the same, with these changes: the namespace is `HashAgreement`, the one self-contained file
is split into the modules above, every block comment that cited a research document now
cites this README or `inputs/PROVENANCE.md`, the per-theorem `set_option profiler true`,
`#print axioms` and `#eval` lines are gone (the census and `test/Vectors.lean` replace
them), and two linter options are added. The blocks `CORE` and `UNFOLD` are byte-identical
to the research `blocks.sha256`; the other blocks differ by comment lines only. The
generators are the research generators with the input paths moved under `inputs/`. New
here: `Census.lean`, `scripts/replay.py`, `check.sh`, `expected.json`, the module split in
`gen_lean.py`, and `test/Vectors.lean`, which replaces the research's five-vector `#eval`
and its Python replay log with a 300-vector run of the Lean definitions. Nothing is
written back to the research repo.
