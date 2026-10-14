# Where the inputs come from

`check.sh` regenerates the Lean files from these inputs and replays the proofs. It
fetches no input; the only network use is `lake exe cache get` for the Mathlib
dependencies when no root build is present (README, "Re-check"). The extraction and the
EVM runs named below happened in the research repo (oskarth/lean-shielded-pool); their
records are cited, not re-run.

## Files

| File | What it is | sha256 |
|---|---|---|
| `PoseidonT3.sol` | poseidon-solidity 0.0.5, `PoseidonT3.sol` (Yul body of `hash(uint[2])`) | 08a7493be37838166954af6c77d583d797cc17d37673196498fc70cbf557831c |
| `noir/mod.nr` | noir-lang/poseidon v0.3.0 `src/poseidon/mod.nr` (`permute`, `apply_matrix`, `sigma`) | d0b044a17c0d7c26470137c17b7a43c172051da8ea74e56797323f3cc07a5a84 |
| `noir/bn254.nr` | same, `src/poseidon/bn254.nr` (`hash_internal`, `hash_2`) | 4800b851b4b0e2c71cd6456efb021be865e4fde040c6e63797b6f157c042653a |
| `noir/bn254/perm.nr` | same, `src/poseidon/bn254/perm.nr` (`x5_3`) | 1daf55657af0418deb717b74cd45a1a4e9ac9d59678335cf0e677ed8a682be23 |
| `noir/bn254/consts.nr` | same, `src/poseidon/bn254/consts.nr` (`x5_3_config`: 81 round constants, MDS, presparse matrix, 285 sparse entries) | 0e1ce6ec6ed2ebbab52739ab07a2ab7a9cfb9b479cb012527f5e08447677dfd2 |
| `noir/LICENSE` | the library's Apache-2.0 license text | (pinned in `expected.json`) |
| `sol_params.json` | the 195 plain round constants and the MDS matrix extracted from `PoseidonT3.sol` | cbca794b53c67844b9ab3cd21203f6720e291b6c8639cece18ff37b3aa01f2b8 |
| `vectors/inputs.json` | 300 input pairs: 196 edge pairs and 104 seeded random pairs | ab284c7668a2ba195000a4c8eb9ca709d74dc61f27c60fa613025b1f490f0bcd |
| `vectors/sol_outputs.txt` | `PoseidonT3.hash([a, b])` on those pairs, one decimal per line, from an EVM run | 8acc9017447ec7f85e804858d1ccbce78723119fae4688f905a8e32fa844152f |

`scripts/common.py` checks the sha256 of every file above (except the license) before it
reads it; `expected.json` pins all nine.

## Sources

The pool sources are public: ethsystems/pocs, whose `master` is
`a04b8b38969dfc2ee64de47edee7e396454204a8`, the same commit that the records below name as
the pin (checked 2026-10-13). The private twin ethsystems/pocs-private is two commits ahead.
PR #16 (`748884e`, merged 2026-10-08) changes `circuits/transfer/src/main.nr`,
`contracts/src/verifiers/TransferVerifier.sol`, `src/lib/adapters/channel.rs` and the
changelog; the circuit `Nargo.toml` files, `soldeer.lock` and `foundry.toml` are unchanged
(diff `a04b8b3..748884e`). PR #14 (`9409fae`, its current `master`) adds the private MMF
requirement documents and touches no shielded-pool file. The Poseidon pins and these
inputs are the same at that tip.

- **PoseidonT3.sol.** The dependency `poseidon-solidity` 0.0.5 that the pool pins at
  `a04b8b38969dfc2ee64de47edee7e396454204a8` (`soldeer.lock`, archive sha256
  `c622cf4f348014da6947d3ddeba267317f1ca3701466f92e0be64a7726c3b31c`; `foundry.toml`
  remaps `poseidon-solidity/=dependencies/poseidon-solidity-0.0.5/`). The pool contract
  does not call it directly: `ShieldedPool.sol` uses zk-kit's `LeanIMT`, whose
  `InternalLeanIMT.sol` computes every node as `PoseidonT3.hash([left, right])`. The file
  carries an MIT SPDX header. Research record: the Poseidon frame work of 2026-10-01, which
  rebuilt the library from this file and matched the archived runtime artifact byte for
  byte (a local build, not evidence of a production deployment).
- **Noir files.** noir-lang/poseidon at tag `v0.3.0`, git
  `0880c371e88e583d39515fd3f877538657ac41eb`, Apache-2.0 (`noir/LICENSE`). The three
  pool circuits pin it in their `Nargo.toml`
  (`poseidon = { tag = "v0.3.0", git = "https://github.com/noir-lang/poseidon" }`) and
  compute nullifiers and Merkle nodes with its `hash_2`. The copies came from the local
  nargo cache of that tag; their hashes equal those recorded in the hash-differential
  record (below).
- **sol_params.json.** Output of the hash-differential record's `extract_sol.py` on
  `PoseidonT3.sol` (2026-10-02). That extractor parses every Yul statement, rebuilds the
  round structure, recovers `C[0][0]` from the folded first-round literals `M[0][j] * C00^5`
  by a fifth root mod p, and bounds every `add` statically below 3.999 p, so no EVM `add`
  wraps for any input. The file is trusted and reused here; the Lean lemmas `solR0_eq` ..
  `solR63_eq` and `solLast_eq` would not hold if a constant or MDS entry differed from the
  Yul literals, so the proof re-checks its content against `PoseidonT3.sol`. The static
  `add` bound is not re-checked here.
- **Vectors.** `inputs.json` is the output of that record's `gen_inputs.py`: all ordered
  pairs of 14 edge values (0, 1, 2, p-1, p-2, p-3, (p-1)/2, (p+1)/2, 2^128-1, 2^128,
  2^160-1, 2^252, 2^253, 2^253+2^252) plus 104 pairs from `random.Random(20261002)`.
  `sol_outputs.txt` was written by the forge test `PoseidonDiff.t.sol` (`testDifferential`)
  running the compiled library (forge 1.8.3, solc 0.8.37, optimizer on, 100 runs). The same
  record found that nargo 1.0.0-beta.21 `hash_2` gives the same 300 values; that nargo run
  is not reproduced here.

## Earlier records (research repo, not re-run here)

- Hash differential, 2026-10-02: the parameters of both libraries equal entry for entry
  (modulus, t = 3, 8 + 57 rounds, x^5, MDS, round constants in both shapes); 300 of 300
  pairs agree in nargo, forge, a Python interpreter of the Yul text, a Python plain model and
  a Python port of Noir `permute`; four negative controls fail as they must.
- The night prototype, 2026-10-07, that this package carries: `experiments/a9proto/` on
  branch `dispatch/xo-fv-lean`, report `evidence/2026-10-07/a9proto/REPORT.md`; the
  2026-10-11 retry of the monolithic-to-segmented Solidity equality,
  `evidence/2026-10-11/a9proto-solseg/run.log` (README, "What stays open").

The inputs derive from public library sources. The vectors and the extracted parameters are
derived data, included so that the check needs no other repo and no network beyond the
Mathlib dependency setup.
