# circuits-acir: compiled-constraint proofs for deposit, withdraw and transfer

This package proves range and linear rules over the compiled constraints of the three
shielded-pool Noir circuits. Its input is what the compiler emitted, not the Noir source:
the ACIR printed by `noir-inspector` for the beta.21 artifacts of the circuits committed
at `a04b8b3` of ethsystems/pocs (public; ethsystems/pocs-private has the same commit). A
`check.sh` rebuilds the artifacts, prints and witnesses from a pocs submodule with pinned
tools and checks them against pinned hashes; the package commits the pins, not the
outputs. A Python extractor turns each print into Lean data, a small semantics gives it meaning, and
the Lean kernel checks the theorems. The package is separate from the model in the parent
directory: it has its own lakefile, uses the same toolchain (Lean 4.33.1, core only, no
Mathlib), and imports no model module. Nothing here changes the claim in the parent
README.

The pin is not the latest circuit. ethsystems/pocs-private pull request 16 (`748884e`,
merged 2026-10-08) changed `circuits/transfer/src/main.nr` and `TransferVerifier.sol`
after `a04b8b3`. The package stays at the pin; the newer transfer circuit is not covered
here.

## The theorems

`circuit.Satisfied w` means that the assignment `w : Nat → Fin P` (P the BN254 scalar
modulus) satisfies every opcode of the printed `func 0`. `(w i).val` is the canonical
value of witness `i`, in `[0, P)`.

| Circuit | Theorem | Statement |
|---|---|---|
| deposit (7,662 opcodes) | `AcirLean.Deposit.amount_lt_two_pow_128` | `∀ w, circuit.Satisfied w → (w 2).val < 2 ^ 128` |
| withdraw (11,508 opcodes) | `AcirLean.Withdraw.amount_lt_two_pow_128` | `∀ w, circuit.Satisfied w → (w 2).val < 2 ^ 128` |
| transfer (23,543 opcodes) | `AcirLean.Transfer.amount_ranges` | the four amounts w8, w11, w14, w18 are below `2 ^ 128` |
| transfer | `AcirLean.Transfer.conservation` | `(w 8).val + (w 11).val = (w 14).val + (w 18).val ∧ (w 8).val + (w 11).val < 2 ^ 128` |
| transfer | `AcirLean.Transfer.token_consistency` | `w 10 = w 7 ∧ w 13 = w 7 ∧ w 17 = w 7` |
| each circuit | `satisfiable` | `∃ w, circuit.Satisfied w` |

Witness 2 is the public input `amount` of deposit and withdraw. In transfer, w8, w11,
w14 and w18 are `amount_in_0`, `amount_in_1`, `amount_out_0` and `amount_out_1`, and
w7, w10, w13 and w17 are the four token fields. Helper theorems name the opcode that each
proof uses (for example `range_amount_mem`) and tie witness indices to ABI names
(`amount_is_public_input_2`, `amount_names`, `token_names`). Conservation is an equation
over the naturals: each amount is below `2^128`, so each sum is below `P`, and the
input sum has its own 128-bit range, so the u128 addition does not wrap.

Every theorem depends only on `propext` and `Quot.sound`, or on no axiom. Concrete
checks use kernel reduction (`decide +kernel`), never `native_decide`.

## What the theorems say, and what they do not

- The universal bounds, transfer conservation and token equality hold under
  satisfaction of the extracted ASSERT and RANGE constraints (ACIR AssertZero and the
  RANGE black box).
- Brillig entries impose `True`. Their execution is not proved. The statements quantify
  over every assignment that satisfies the constraints, so they do not depend on what
  the Brillig code computes.
- Non-vacuity: for each circuit, the witness that `nargo execute` produced for the
  committed `Prover.toml` satisfies every opcode under these semantics. The kernel
  checks it in 256-opcode chunks (`NV/G*.lean`, `NonVacuity.lean`). The witnesses give
  deposit amount 500, withdraw amount 700, and transfer amounts 1000, 0, 700 and 300
  with four equal tokens.
- Checked, not trusted: the printer. `scripts/bytecode_check.py` decodes each
  artifact's `bytecode` (base64, gzip, a format byte, then msgpack) and compares it with
  the parsed print of `func 0`: the parameter lists, the opcode count, and at each index
  the opcode kind, each RANGE witness and bit count, each ASSERT expression up to a factor
  of 1 or -1 over the field, and each Brillig function id and outputs. The decoder and
  the comparison are reviewed code, not proved.
- Trusted, not proved: the extractor (`scripts/acir2lean.py`), the semantics
  (`AcirLean/Semantics.lean` means what ACIR means), and the ABI allocation. The
  extractor re-prints every AssertZero and RANGE line from its parsed form and requires
  byte equality; Brillig lines keep only the function id and outputs. Witness names
  follow the flattened-ABI allocation convention. The extractor checks the sizes against
  the printed parameter lists, and one witness per circuit agrees, but this is not a
  proof of the name-to-wire map.
- Separate obligations: correctness of the compiler from Noir source to ACIR, of bb from
  ACIR to UltraHonk, and of the proof system and verifier contract. The identity of the
  deployed verifier is also separate: the artifacts reproduce the committed verifier
  sources at a04b8b3 (inputs/PROVENANCE.md), not on-chain bytecode.
- Hash-bound rules (commitments, nullifiers, Merkle membership) are not covered.
- `Neg/TransferNoRange.lean` is a failed proof attempt, not a false full-circuit
  statement: it drops the RANGE facts from the conservation proof, so `omega` cannot
  close it. The wrap counterexample itself is `control_asserts_alone_allow_wrap`.
- `Neg/DepositBound127.lean` and `Neg/WithdrawBound127.lean` are failed proof attempts
  too. Each claims a 127-bit amount bound with the proof of the 128-bit one, and fails at
  the membership step because opcode 23 (deposit) or 362 (withdraw) has 128 bits. They do
  not show that a 127-bit bound is false, and no control shows that the 128-bit bound is
  tight: the controls refute only the bounds 500, 700 and 1000. The control
  `control_range_alone_allows_2_pow_127` (deposit and withdraw) shows only that the RANGE
  opcode accepts amount `2^127`. A solved witness with amount `2^127` would refute the
  127-bit bound for the whole circuit. It needs new public inputs (the commitment for
  deposit; the commitment root and the nullifier for withdraw) and a second non-vacuity
  proof per circuit, and it is not included.
- The witness fixtures are solver outputs, not contract-accepted executions.

## Re-check

Install Python 3.10 or later, bash, git, elan and `leanprover/lean4:v4.33.1`, and nargo and
noir-inspector 1.0.0-beta.21 (both in the release asset named in `inputs/TOOLS.txt`), before
running the check. The package has no Lake dependencies.

```
git submodule update --init circuits-acir/pocs
cd circuits-acir
./check.sh               # expect the last line: REPLAY CHECK PASS: 3 circuits, ...
./check.sh --self-test   # expect the last line: SELF-TEST PASS: ...
```

Set `NARGO` and `NOIR_INSPECTOR` to the binaries if they are not on `PATH`. The first run
needs the network to clone the two Noir libraries into `.deps/`; later runs use that cache
and need no network.

A bare `lake build` builds the `AcirLean` modules, several at a time, once `check.sh` has
generated the data modules, and checks nothing else. It needs more memory than `check.sh`,
which builds one module at a time.

`check.sh` is a rebuild and replay check, not the proof: it rebuilds the compiler outputs,
re-runs the extractor and the kernel on them and compares every result with
`expected.json`. In order, it:

1. checks the version and the sha256 of nargo and noir-inspector against
   `inputs/TOOLS.txt`;
2. checks that `pocs/` is at the pinned commit, reads the 12 files of
   `inputs/SHA256SUMS` from that commit as git blobs and checks their hashes;
3. places the two Noir libraries of `inputs/DEPS.txt` where nargo looks for them (cloned
   once by tag into `.deps/`, with a commit check), so nargo fetches nothing;
4. runs `nargo compile`, `nargo execute` with the committed `Prover.toml` and
   `noir-inspector print-acir` for each circuit, into `build/inputs/` (not tracked);
5. checks the Lean and Python versions;
6. hashes every file of the package except README.md, expected.json, .gitignore, the
   `pocs/` checkout and the caches;
7. hashes the rebuilt outputs and compares the print, `func 0`, ABI, bytecode,
   `noir_version` and witness hashes with `expected.json` (a mismatch stops the check
   before anything is built);
8. decodes each artifact's `bytecode` and compares it with the print, opcode by opcode
   (`scripts/bytecode_check.py`, described above); a difference stops the check before
   anything is built;
9. regenerates the Lean data, the witness tries and the non-vacuity modules with the
   scripts in `scripts/`, then hashes them; the generated files are not tracked;
10. runs seven mutated-witness checks in Python and compares the failing opcodes with
   `expected.json`: five mutations must break the rule opcode they target; setting the
   deposit `amount` (w2) to 501 has no required opcode and breaks exactly opcodes 356 and
   357, two ASSERTs over w2; and setting the unconstrained deposit `payload_hash` (w5) must
   break nothing;
11. rejects `sorry`, `admit`, `native_decide`, `axiom`, `extern`, `implemented_by`,
   `unsafe`, `opaque` and `skipKernelTC` (the option `debug.skipKernelTC` turns off the
   kernel check) in every Lean file of the package, `Census.lean` included, and in
   `lakefile.toml`;
12. builds every module, one at a time;
13. runs `Census.lean`: for every theorem in an `AcirLean.*` module, its statement, printed
   with no elision (`pp.deepTerms`, `pp.proofs`, `pp.maxSteps` raised to 10^8; a `⋯` in a
   statement fails), the SHA-256 of a raw form of its type (every node of the expression,
   with a tag per constructor, names component by component and strings quoted; a syntax
   value in metadata fails), and its axioms (`Lean.collectAxioms`, as `#print axioms`);
   any axiom outside `propext`, `Quot.sound` and `Classical.choice`, and any declared
   axiom or opaque constant, fails;
14. compiles each `Neg/*.lean` file, which must fail with the expected first error;
15. compares everything with `expected.json`. A missing, duplicate or unexpected
    theorem, control, input or file fails, as does any changed statement, raw-type hash or
    axiom list.

The source scan and the census are checks against mistakes, not against a hostile
package. Code that runs during elaboration (an `elab` command, a direct `addDecl`, an
option set by code) can add declarations, skip the kernel or change what the census
prints, and the scan matches none of these: the rogue-axiom fixture of the self-test gets
through the scan, and only the census catches it. The pinned file hashes and the review of
the hand-written files cover a hostile package.

`--self-test` first checks the rebuild stages on four copies of the package, each with its
own clone of `pocs/`. Each must fail for its intended reason: `pocs/` at another commit (the
source stage), nargo or noir-inspector with one byte appended, so the version matches and
the sha256 does not (the tool stage, before any build), and the withdraw circuit narrowed
to 127 bits in a new pocs commit, with the pin and `inputs/SHA256SUMS` moved to it, so that
only the comparison of the rebuilt outputs with `expected.json` can catch it (it must
report withdraw and nothing else).

Then it copies the built package and plants one change per copy. Each change must
make `check.sh` fail for its intended reason: a removed theorem, an added theorem, a
weakened statement, a rebuilt print that differs from its pin, a rogue axiom, a `sorry`, a negative
control that compiles, a negative control that fails with a different error, a print that
differs from the bytecode in one opcode, a print that drops an opcode (both with the print
hashes repinned), and a false theorem whose kernel check is turned off with
`set_option debug.skipKernelTC true in`. That last fixture also re-blesses the census entries of that
theorem and of its auxiliary lemma into its copy of `expected.json`, and every failure
must then come from the scan. A duplicated census entry is tested on the comparator alone.
The unchanged copy must pass. To show that the deeper check catches each change, the
fixtures that edit a pinned file also update its hash in their copy of `expected.json`.

Cost on a Linux laptop (xps26, btrfs), one build at a time, `LEAN_NUM_THREADS=2`:
the first full run built 75 modules in 1,101 s of wall time (the slowest module took 67 s),
with a cgroup memory peak of 1.47 GB under a 6 GiB cap. `.lake` takes 79 MB and `build/`
28 MB. A re-run on a built tree takes seconds. The rebuild of the three circuits takes
about 10 s; `.deps/` takes 4 MB and the pocs submodule 4 MB. On 2026-10-15 the
self-test took about 4 minutes, while another Lean job ran on the same machine.

## Files

- `AcirLean/Semantics.lean`, `Witness.lean`, `Linear.lean`: the semantics, witness tries
  and the linear lemmas.
- `AcirLean/{Deposit,Withdraw,Transfer}/`: the rule theorems (`Amount.lean`,
  `Rules.lean`), the solved witness (`Solved.lean`) and the controls (`Controls.lean`).
  `check.sh` writes the generated `Data.lean`, `Data/Part*.lean`, `WitnessData.lean`,
  `NV/G*.lean` and `NonVacuity.lean` here.
- `Neg/`: four files that must fail to compile.
- `Census.lean`: the theorem census.
- `scripts/`: `acir2lean.py` (extractor), `witness_check.py` (Python solver agreement
  and witness tries), `gen_nv.py` (non-vacuity modules), `perturb_check.py` (mutated
  witnesses), `bytecode_check.py` (bytecode against print), `replay.py` (the stages
  above).
- `inputs/`: the pins (`TOOLS.txt`, `SHA256SUMS`, `DEPS.txt`) and `PROVENANCE.md`.
- `pocs/`: git submodule of ethsystems/pocs at the pinned commit.
- `expected.json`: the expected results. It is the reviewed output of the first run.

## Where it comes from

The Lean files, the scripts and the data come from two reviewed archives
in the research repo (oskarth/lean-shielded-pool at commit `fa5526e`), one
for deposit and one for withdraw and transfer, each judged there by a
cross-family reviewer. The withdraw and transfer proof logic is unchanged
from the archived sources. Comment and documentation edits remove research
labels and correct references. Their regenerated data retain the archived
hashes. Deposit now uses the
same split, `noncomputable` data form as the other two; its 30 opcode chunks are the
same text as the archived `Data.lean`. New here: `Deposit/Solved.lean` (now
`noncomputable`), `Deposit/Controls.lean`, `Neg/DepositBound127.lean`, `Census.lean`,
`scripts/replay.py`, `scripts/bytecode_check.py` and `check.sh`. The comment in
`Neg/TransferNoRange.lean` now
describes a failed proof attempt, after that review.

`check.sh` rebuilds the inputs from the circuit sources at `a04b8b3`, and the witnesses
from the `Prover.toml` fixtures committed there; that commit is public in ethsystems/pocs.
Until 2026-10-15 the package committed the nine outputs; the rebuild reproduces them
(`inputs/PROVENANCE.md`). Keep
this package private with the rest of the repo; review it again before any public release.
