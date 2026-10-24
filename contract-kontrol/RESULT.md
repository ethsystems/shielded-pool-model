# contract-kontrol: runs of 2026-10-24

These are the runs of `check.sh` on 2026-10-24, on a Linux x86_64 laptop (16 threads, 30 GiB, btrfs)
that other jobs shared (`free -g` showed 5 to 15 GiB available during the runs). They were judged by
the `check.sh` and `scripts/compare.py` of their commits, before the changes listed under "Checker
changes after these runs" below; no run of that day ended `CHECK PASS` over every suite. Each run
used a `git archive` copy of the package at the commit named below, with `POCS`, `DEPS_CACHE` and `WORK`
set to the checkout's `pocs/`, `.deps/` and a `work/` directory. Every Kontrol container: image
`runtimeverificationinc/kontrol@sha256:858f004144d61b005997f56bb8b7cd15673850286c96e0e5ec0502d9c9a9e204`
(Kontrol 1.0.255, the image's own `abi.md` sha256 `878f7732...f95e`), `--memory 8g --memory-swap 8g`,
core dumps off, no network, CPUs `0-1` for a build and `0-5` for a proof run, one container at a
time, started only when `free -g` showed at least 10 GiB available. Compiler inside the container:
solc 0.8.37 (`5de843c2...404a`) for the Prague EVM; on the host: forge and cast 1.8.3, solc 0.8.37.

"Wall" is the container's wall time. "Peak" is the container cgroup's `memory.peak` (bytes / 10^9).
"Time" is Kontrol's own time for one proof (proofs run in parallel, so the times add up to more than
the wall). Node ids are those of this run; the earlier runs had other ids for the same nodes.

## Summary

| Suite | Run | Rerun here | Result |
|---|---|---|---|
| `withdraw-success` | `token-above-0x11` | yes (run 5) | 7 of 7 as expected: stock PASSED, six mutants FAILED at their outputs; 3,438 s wall, 6.88 GB peak |
| `withdraw-success` | `two-tokens` | yes (run 5) | 7 of 7 as expected; 3,554 s, 7.13 GB |
| `withdraw-success` | `replay` | yes (run 5) | 23 of 23 forge replays pass |
| `guards-patched` | `withdraw` | yes (run 3) | 8 of 8 as expected (4 PASSED, 4 mutants FAILED); 3,000 s, 6.18 GB |
| `guards-stock` | `withdraw`, `deposit`, `transfer` | yes (run 5) | 26 of 26 as expected (13 PASSED, 13 mutants FAILED); 2,324 s, 2,179 s, 2,257 s; peaks 6.28, 6.68, 6.73 GB |
| `insert-loop` | `rejections` | yes (run 5) | 6 of 6 as expected; 326 s, 3.86 GB |
| `insert-loop` | `controls` | yes (run 5; also run 2) | 21 stock tests pass, 20 mutant controls fail at their named postconditions, stub test passes in both, witness audit passes |
| `insert-loop` | K claims in `k/` | not rerun here; archived claims about the 0.8.33 build (Cancun) | `check.sh` does not run them (README.md) |
| `public-inputs` | `canonical`, `order`, `fixed-token` | not rerun here; expected verdicts from the 2026-10-01 run on the 0.8.33 build | not started; time budget exhausted. The build and the replays ran (run 6) |
| `public-inputs` | build, `replay` | yes (run 6) | build passes (143 s, peak 8.59 GB, just under the 8 GiB cap); 36 of 36 replays pass |
| `poseidon-frame` | `frame` | yes (run 5; also run 4) | 9 of 9 as expected: four real checks PASS with 1, 1, 2 and 132 paths, the mutant witness FAILs with one valid model, the deployment test and the real replay pass, the mutant replay fails |

Runs, each `check.sh` from a `git archive` copy of the package. The commit named is the one in this
history whose `contract-kontrol/` tree equals the tree of the run (the runs were made before a
rebase that changed the commit ids, not the package files):

- run 3, commit `e7e6829`, `./check.sh withdraw-success guards-patched guards-stock public-inputs`,
  started about 10:14Z: the `withdraw-success` build hit the cap (below); `guards-patched` ran to the end;
  I stopped the run after it to start the queue below with `withdraw-success` first. Its
  comparison was run on its work directory afterwards (`scripts/compare.py EXPECTED.tsv work
  guards-patched`).
- run 5, commit `77b56e2`, `./check.sh withdraw-success guards-stock insert-loop public-inputs
  poseidon-frame`, started 11:14Z, 14,617 s: four suites `CHECK PASS`; I stopped the
  `public-inputs` build container after 11 s because the time budget of the day was spent, so that
  suite reads `BUILD-FAILED` there and the last line is `CHECK FAIL`.
- run 6, commit `77b56e2`, `./check.sh public-inputs:none` (the build and the replays, no proof
  run; the checker of that commit read the unknown run name `none` as "no prove run"; the current
  `check.sh` rejects it, and `public-inputs:build,replay` selects the same runs), started 15:18Z,
  151 s: `CHECK PASS suite public-inputs (partial: not run canonical, order, fixed-token)`.
- run 2 (commit `842a889`, `insert-loop` with `controls` only) and run 4 (commit `7a1d3fc`,
  `poseidon-frame`) gave the same results as run 5 for those runs.
- run 7, commit `0ae5190`, `./check.sh insert-loop`, started 15:24Z, 439 s: `CHECK PASS` (all 50
  lines; build 7.25 GB, `rejections` 299 s at 3.71 GB, failing nodes 22, 25 and 29). Commit
  `0ae5190` came after runs 3 to 6 and changed no proof input: the prove commands spell
  the parallel-process option by its short alias `-j` (one option of the image's `pyk`), and `check.sh` asks the
  image for the path of its `abi.md` in place of a pinned path. Run 7 checks that end to end.

Between run 3 and run 5 the harness of `withdraw-success` changed (commit `e9cb2b2`: the probe and
witness bodies moved out of the mutant siblings, bodies unchanged) and `insert-loop` gained the
`rejections` run; no other suite input changed.

## Checker changes after these runs

Commits `5273313` and `be4ab83` changed the checker after the runs above. They changed
`check.sh`, `scripts/compare.py` and `scripts/kontrol-run.sh`, added `scripts/pyenv-check.py`, and
added the Halmos environment pins to `PINS.txt`. No harness, mutant, lemma, `abi.md`, prove command
or line of `EXPECTED.tsv` changed.

- `scripts/kontrol-run.sh`: the shell in the container exits with the command's status. Before, it
  ended with an `echo`, so the runner exit was 0 even when the command failed. Now the RUN end line
  shows a runner exit equal to the command exit, unless the run was stopped (124: timeout, 137:
  kill).
- `check.sh`:
  - rejects a suite that `harness/SUITES.txt` does not name, a run that the suite's `runs.tsv` does
    not name, and a name given twice (run 6's `public-inputs:none` is now a usage error). A selection
    names runs of any kind; a selected prove run brings its suite's build; a run not selected does
    not run.
  - runs the inventory of every suite (`compare.py --inventory`) before any tool.
  - writes the exit status of each forge, controls and Halmos run as the last line of its log
    (`HOST_EXIT=`), at once. Before, the forge exit was not recorded.
  - counts a build as built only when the runner exit, `COMMAND_EXIT` and `BUILD_EXIT` are all 0.
    Before, "Kontrol project built" with `COMMAND_EXIT=0` was enough.
  - checks the Halmos environment with `scripts/pyenv-check.py` against `requirements-halmos.txt` and
    the RECORD pins, pins Python 3.12, z3 4.12.6 and the yices binary, and runs Halmos as
    `python -I -m halmos`. Before, it checked the halmos and yices version strings only.
  - ends `CHECK PASS` (exit 0) only when every run of every named suite matched, `CHECK PARTIAL
    (<selection>)` (exit 3) when the selection left runs out, and `CHECK FAIL` (exit 1) otherwise.
    Before, a partial selection also ended `CHECK PASS`.
- `scripts/compare.py`: gets the explicit selection, and a selected run without results is a
  mismatch. Before, it skipped every run without results, so a check with no `public-inputs` proof
  passed. A run is now void, and each of its expected verdicts a mismatch, when its runner or command
  exit differs from the exit its expected verdicts give, when `BUILD_EXIT` or `HOST_EXIT` is missing
  or wrong, when forge's test count differs from the recorded lines, or when its log has a kill, a
  traceback or a crashed proof. It also checks the inventory.

What this means for the runs above. Their logs predate the two status lines, so the new comparator
voids their prove runs (runner exit 0, command exit 1, from the old runner) and their host runs (no
`HOST_EXIT` line); every build passes its status check, and no recorded verdict differs from
`EXPECTED.tsv` (all 165 mismatches are verdicts of void runs). On copies of the saved logs with the two
lines added (the runner exit set to the recorded `COMMAND_EXIT`; `HOST_EXIT=0`, which for controls
and Halmos is the exit behind the recorded `all-checks PASS` and for the forge replays was not
recorded), all 170 expected verdicts of runs 3, 5, 6 and 7 match, with `public-inputs` partial. That
shows the new comparator reads the saved results. It is not a rerun: the Kontrol suites have not yet
run with the current scripts.

The `poseidon-frame` runs 4 and 5 ran Halmos in a Python 3.14.9 environment installed from
`requirements-halmos.txt`. The new environment check rejects it: the Python is not 3.12, and the
RECORD digests of charset-normalizer, safe-pysha3 and xxhash differ from the pins (another build of
the same versions). With `TOOLS_UNPINNED=1` the suite passes in it. The rerun below used a Python
3.12.14 environment that matches every pin.

## Runs after the checker changes

Commit `be4ab83`, each `check.sh` from a `git archive` copy of the package, with `POCS`,
`DEPS_CACHE` and `WORK` set as above. No Kontrol container ran: another Kontrol run held the
machine (one container at a time, and `free -g` showed 8 GiB available, below the 10 GiB gate).

- `./check.sh withdraw-success:replay public-inputs:replay insert-loop:controls`, started 15:57Z,
  17 s: 23 of 23 and 36 of 36 forge replays pass, the controls pass (21 stock tests, 20 mutant
  controls at their named postconditions, the stub test in both runs, the witness audit), every
  run's exit as expected; 102 verdicts, 0 mismatches. Last line `CHECK PARTIAL
  (withdraw-success:replay public-inputs:replay insert-loop:controls)`, exit 3.
- `./check.sh poseidon-frame`, started 15:57Z, 12 s, Halmos as `python -I -m halmos` in a Python
  3.12.14 environment (19 of 19 RECORD digests equal `PINS.txt`, 811 files equal their RECORD
  hashes): 9 of 9 as expected (the four real checks PASS with 1, 1, 2 and 132 paths, the mutant
  witness FAILs, the deployment test and the real replay pass, the mutant replay fails). Last line
  `CHECK PASS: 1 suites (poseidon-frame), every run`, exit 0.
- The same suite with the Python 3.14.9 environment of runs 4 and 5: `FAIL tools: the halmos
  environment runs Python '3.14', pinned 3.12`, exit 1; with `TOOLS_UNPINNED=1`, `CHECK PASS` with
  `(unpinned build: python3.14 pyenv)`.
- Selections `public-inputs:none`, `nosuch`, `insert-loop:rejections,rejections`, `insert-loop:`
  and `insert-loop insert-loop`: each a usage error, exit 2, before any tool runs.

Fault checks of the new comparator, each on a copy of the saved logs with the two status lines
added (above), and each ending `CHECK FAIL` with exit 1:

| Fault | Comparator result |
|---|---|
| `public-inputs` with every run selected; only the build and the replays recorded (run 6) | `canonical`, `order`, `fixed-token` void (no recorded verdict, no log); 22 mismatches |
| `withdraw-success` with the `two-tokens` results and log removed | `two-tokens` void; 7 mismatches |
| forge replay log ends `HOST_EXIT=1`, every test line PASS | `replay` void (exit 1, expected 0); 23 mismatches |
| `insert-loop` `rejections` exits 0, although its mutants must fail | void (command exit 0, expected 1); 6 mismatches |
| `guards-stock` `deposit` runner exit 124 after all verdicts were printed | void (runner exit 124, command exit 1); 10 mismatches |
| `insert-loop` build log says `BUILD_EXIT=1`, results say BUILT | build void; 1 mismatch |
| `insert-loop` controls exit 1 with `all-checks PASS` recorded | `controls` void; 43 mismatches |
| a Python traceback after the PROOF lines of `rejections`, exit 1 as expected | void (traceback); 6 mismatches |
| a `Killed` line in the `two-tokens` log | void (Killed); 7 mismatches |
| `guards-patched` `withdraw` log without its RUN end line | void (1 RUN start, 0 RUN end); 8 mismatches |
| a `guards-patched` results line recorded twice | `CHECK DUPLICATE`; 1 mismatch |
| two verdicts of `guards-patched` `withdraw` deleted from the results | void (8 PROOF lines, 6 recorded) and 2 MISSING; 8 mismatches |

## What was checked beyond the verdicts

- `withdraw-success` `token-above-0x11`, the stock graph: 225 nodes, 173 edges, 15 splits, 2
  non-deterministic branches (the token call), 36 terminal nodes, one leaf (the target), 0 vacuous,
  0 stuck. The record of the 2026-10-07 run (not in this repository) gives the same counts.
- `withdraw-success` `two-tokens`, the stock graph: 248 nodes, 184 edges, 31 splits, 34 terminal
  nodes, one leaf (the target), 0 vacuous, 0 stuck (the 2026-10-06 run: 248 nodes, 31 splits).
- The failing node of `FIXED_TOKEN` in `token-above-0x11` (node 122) has the path constraints
  `17 < token`, `token != ` the cheatcode account and `token != 0xf000...000b`: the failure is at a
  token other than the fixed one, as in the 2026-10-07 run.
- The failing node of `DEPOSIT_FUNDER_CALLER` (node 90): Kontrol prints the path condition
  `P <= c`, so with the caller check removed the canonical-input check fires first, as in the
  2026-10-01 run (node 89, `c >= P`).
- `guards-patched`, the four stock graphs have 51, 51, 53 and 69 nodes, as in the 2026-10-01 run.
- `scripts/klengths.py` on the saved graphs, at the test entry (node 11): every `guards-stock` proof
  carries `lengthBytes(b) <= 1073741824` and `< 2^64` for each `bytes` argument; every
  `guards-patched` and `withdraw-success` proof carries only `lengthBytes(proof) < 2^64`. So the
  patched `abi.md` was in force where the suites say so, and only there.
- Every container printed the sha256 of the `abi.md` it saw: `e249e9e2...7a88` for the patched
  suites, `878f7732...f95e` for `guards-stock` and `insert-loop`.
- Not done here: the per-node feasibility evaluation of the earlier runs (every constraint of a
  failing node true at one point). The forge replays, which run concrete executions at the
  earlier points, pass.

## Attempts that did not finish

- `withdraw-success` build with the earlier layout of `WithdrawSuccess.t.sol` (the probe and
  witness bodies inherited by all six mutant siblings): at 10:09:42Z with 4 CPUs (`--cpus 4`),
  188 s, the kompile was killed at 8.61 GB (exit 137); at 10:16:05Z with CPUs `0-1`, 241 s, the
  LLVM kompile was killed at the 8 GiB cap. KEVM runs the LLVM and the Haskell kompile in parallel,
  and the earlier runs of this build peaked between 5.9 and 8.6 GB. After the probes moved to their
  own contract the build passed at 7.56 GB.
- `public-inputs` `canonical`, `order`, `fixed-token`: not started; time budget exhausted. In the 2026-10-01 run
  `canonical` and `order` (15 proofs) took 4,996 s of wall time; `fixed-token` ran separately
  there.
- An earlier attempt of the `guards-stock` build (run 3) was stopped by me after it started, when I
  reordered the queue; it is not a result.

# The runs, suite by suite

## withdraw-success

| Run | Started (UTC) | Wall | Peak memory | Outcome |
|---|---|---|---|---|
| build | 2026-10-24T11:14:29Z | 206 s | 7.56 GB | BUILD_EXIT=0 |
| replay | - | - | - | host run |
| token-above-0x11 | 2026-10-24T11:17:55Z | 3438 s | 6.88 GB | exit 1, runner 0 |
| two-tokens | 2026-10-24T12:15:13Z | 3554 s | 7.13 GB | exit 1, runner 0 |

| Run | Proof | Verdict | Failing node output | Time |
|---|---|---|---|---|
| build | `build` | BUILT | - | 206s |
| token-above-0x11 | `WithdrawSuccess.prove_success_token_above_0x11` | PASSED | - | 29m 45s |
| token-above-0x11 | `WithdrawSuccess_M_FIXED_TOKEN.prove_success_token_above_0x11` | FAILED | EVMC_REVERT:7fa6412e (node 122) | 15m 16s |
| token-above-0x11 | `WithdrawSuccess_M_LATE_MARK.prove_success_token_above_0x11` | FAILED | EVMC_REVERT:e3e0fc25 (node 203) | 26m 49s |
| token-above-0x11 | `WithdrawSuccess_M_SWAP_INPUTS.prove_success_token_above_0x11` | FAILED | EVMC_REVERT:1987cd34 (node 106) | 15m 25s |
| token-above-0x11 | `WithdrawSuccess_M_DROP_BIT253.prove_success_token_above_0x11` | FAILED | EVMC_REVERT:1987cd34 (node 104) | 15m 2s |
| token-above-0x11 | `WithdrawSuccess_M_PAY_CALLER.prove_success_token_above_0x11` | FAILED | EVMC_REVERT:0bc6283d (node 233) | 23m 35s |
| token-above-0x11 | `WithdrawSuccess_M_SKIP_VERIFIER.prove_success_token_above_0x11` | FAILED | EVMC_REVERT:5b1cfd09 (node 173) | 18m 22s |
| two-tokens | `WithdrawSuccess.prove_success_two_tokens` | PASSED | - | 27m 20s |
| two-tokens | `WithdrawSuccess_M_FIXED_TOKEN.prove_success_two_tokens` | FAILED | EVMC_REVERT:7fa6412e (node 224) | 24m 47s |
| two-tokens | `WithdrawSuccess_M_LATE_MARK.prove_success_two_tokens` | FAILED | EVMC_REVERT:e3e0fc25 (node 224) | 24m 45s |
| two-tokens | `WithdrawSuccess_M_SWAP_INPUTS.prove_success_two_tokens` | FAILED | EVMC_REVERT:1987cd34 (node 191) | 20m 10s |
| two-tokens | `WithdrawSuccess_M_DROP_BIT253.prove_success_two_tokens` | FAILED | EVMC_REVERT:1987cd34 (node 194) | 21m 33s |
| two-tokens | `WithdrawSuccess_M_PAY_CALLER.prove_success_two_tokens` | FAILED | EVMC_REVERT:0bc6283d (node 248) | 23m 41s |
| two-tokens | `WithdrawSuccess_M_SKIP_VERIFIER.prove_success_two_tokens` | FAILED | EVMC_REVERT:5b1cfd09 (node 172) | 10m 47s |
| replay | `WithdrawSuccessReplay.test_W_success_original_high` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_W_success_original_low` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_W_success_original_low_nhi` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_W_success_original_low_reject` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_W_success_original_unsupported_reverts_quietly` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_W_witness_original_high` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_W_witness_original_low` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_any_token_original_nocode_supported` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_token_pick_original_low` | PASS | - | - |
| replay | `WithdrawSuccessReplay.test_two_tokens_original_low_b` | PASS | - | - |
| replay | `WithdrawSuccessReplay_Caller.test_caller_original_other` | PASS | - | - |
| replay | `WithdrawSuccessReplay_Caller.test_caller_original_token` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_DROP_BIT253.test_replay` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_FIXED_TOKEN.test_replay_high_token_passes` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_FIXED_TOKEN.test_replay_low_token_fails` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_FIXED_TOKEN.test_replay_nocode_token_fails` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_LATE_MARK.test_replay` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_LATE_MARK.test_replay_token` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_PAY_CALLER.test_replay` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_PAY_CALLER_Caller.test_replay_prank` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_SKIP_VERIFIER.test_replay` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_SKIP_VERIFIER.test_replay_token` | PASS | - | - |
| replay | `WithdrawSuccessReplay_M_SWAP_INPUTS.test_replay` | PASS | - | - |

CHECK PASS suite withdraw-success

## guards-patched

| Run | Started (UTC) | Wall | Peak memory | Outcome |
|---|---|---|---|---|
| build | 2026-10-24T10:20:07Z | 229 s | 7.67 GB | BUILD_EXIT=0 |
| withdraw | 2026-10-24T10:23:56Z | 3000 s | 6.18 GB | exit 1, runner 0 |

| Run | Proof | Verdict | Failing node output | Time |
|---|---|---|---|---|
| build | `build` | BUILT | - | 229s |
| withdraw | `LongProofWithdrawGuards.prove_withdraw_zero_amount` | PASSED | - | 8m 3s |
| withdraw | `LongProofWithdrawGuards_M_WITHDRAW_ZERO_AMOUNT.prove_withdraw_zero_amount` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 77) | 12m 30s |
| withdraw | `LongProofWithdrawGuards.prove_withdraw_amount_max` | PASSED | - | 8m 24s |
| withdraw | `LongProofWithdrawGuards_M_WITHDRAW_AMOUNT_MAX.prove_withdraw_amount_max` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 70) | 13m 0s |
| withdraw | `LongProofWithdrawGuards.prove_withdraw_spent` | PASSED | - | 9m 28s |
| withdraw | `LongProofWithdrawGuards_M_WITHDRAW_SPENT.prove_withdraw_spent` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 141) | 26m 0s |
| withdraw | `LongProofWithdrawGuards.prove_withdraw_root` | PASSED | - | 12m 55s |
| withdraw | `LongProofWithdrawGuards_M_WITHDRAW_ROOT.prove_withdraw_root` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 89) | 19m 1s |

CHECK PASS suite guards-patched


## guards-stock

| Run | Started (UTC) | Wall | Peak memory | Outcome |
|---|---|---|---|---|
| build | 2026-10-24T13:14:33Z | 159 s | 7.88 GB | BUILD_EXIT=0 |
| deposit | 2026-10-24T13:55:56Z | 2179 s | 6.68 GB | exit 1, runner 0 |
| transfer | 2026-10-24T14:32:15Z | 2257 s | 6.73 GB | exit 1, runner 0 |
| withdraw | 2026-10-24T13:17:12Z | 2324 s | 6.28 GB | exit 1, runner 0 |

| Run | Proof | Verdict | Failing node output | Time |
|---|---|---|---|---|
| build | `build` | BUILT | - | 159s |
| withdraw | `RejectGuards.prove_withdraw_zero_amount` | PASSED | - | 4m 9s |
| withdraw | `RejectGuards_M_WITHDRAW_ZERO_AMOUNT.prove_withdraw_zero_amount` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 68) | 10m 14s |
| withdraw | `RejectGuards.prove_withdraw_amount_max` | PASSED | - | 4m 46s |
| withdraw | `RejectGuards_M_WITHDRAW_AMOUNT_MAX.prove_withdraw_amount_max` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 70) | 11m 15s |
| withdraw | `RejectGuards.prove_withdraw_spent` | PASSED | - | 5m 37s |
| withdraw | `RejectGuards_M_WITHDRAW_SPENT.prove_withdraw_spent` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 138) | 21m 11s |
| withdraw | `RejectGuards.prove_withdraw_root` | PASSED | - | 11m 18s |
| withdraw | `RejectGuards_M_WITHDRAW_ROOT.prove_withdraw_root` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 90) | 15m 7s |
| deposit | `RejectGuards.prove_deposit_token` | PASSED | - | 6m 49s |
| deposit | `RejectGuards_M_DEPOSIT_TOKEN.prove_deposit_token` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 71) | 11m 32s |
| deposit | `RejectGuards.prove_deposit_zero_amount` | PASSED | - | 6m 51s |
| deposit | `RejectGuards_M_DEPOSIT_ZERO_AMOUNT.prove_deposit_zero_amount` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 69) | 9m 57s |
| deposit | `RejectGuards.prove_deposit_amount_max` | PASSED | - | 7m 12s |
| deposit | `RejectGuards_M_DEPOSIT_AMOUNT_MAX.prove_deposit_amount_max` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 72) | 10m 31s |
| deposit | `RejectGuards.prove_deposit_zero_funder` | PASSED | - | 6m 50s |
| deposit | `RejectGuards_M_DEPOSIT_ZERO_FUNDER.prove_deposit_zero_funder` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 42) | 6m 2s |
| deposit | `RejectGuards.prove_deposit_funder_caller` | PASSED | - | 7m 20s |
| deposit | `RejectGuards_M_DEPOSIT_FUNDER_CALLER.prove_deposit_funder_caller` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 90) | 9m 41s |
| transfer | `RejectGuards.prove_transfer_same_nullifiers` | PASSED | - | 4m 48s |
| transfer | `RejectGuards_M_TRANSFER_SAME_NULLIFIERS.prove_transfer_same_nullifiers` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 69) | 9m 42s |
| transfer | `RejectGuards.prove_transfer_spent_first` | PASSED | - | 5m 53s |
| transfer | `RejectGuards_M_TRANSFER_SPENT_FIRST.prove_transfer_spent_first` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 168) | 24m 25s |
| transfer | `RejectGuards.prove_transfer_spent_second` | PASSED | - | 6m 38s |
| transfer | `RejectGuards_M_TRANSFER_SPENT_SECOND.prove_transfer_spent_second` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 145) | 20m 5s |
| transfer | `RejectGuards.prove_transfer_root` | PASSED | - | 10m 27s |
| transfer | `RejectGuards_M_TRANSFER_ROOT.prove_transfer_root` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 88) | 15m 46s |

CHECK PASS suite guards-stock


## insert-loop

| Run | Started (UTC) | Wall | Peak memory | Outcome |
|---|---|---|---|---|
| build | 2026-10-24T15:09:53Z | 141 s | 7.25 GB | BUILD_EXIT=0 |
| controls | - | - | - | host run |
| rejections | 2026-10-24T15:12:14Z | 326 s | 3.86 GB | exit 1, runner 0 |

| Run | Proof | Verdict | Failing node output | Time |
|---|---|---|---|---|
| controls-stock | `test_runtime_M1_depth2` | PASS | - | - |
| controls-stock | `test_runtime_M1_depth4` | PASS | - | - |
| controls-stock | `test_runtime_M2_depth2` | PASS | - | - |
| controls-stock | `test_runtime_M2_depth4` | PASS | - | - |
| controls-stock | `test_runtime_M3_depth2` | PASS | - | - |
| controls-stock | `test_runtime_M3_depth4` | PASS | - | - |
| controls-stock | `test_runtime_exact_M1_depth2` | PASS | - | - |
| controls-stock | `test_runtime_exact_M1_depth4` | PASS | - | - |
| controls-stock | `test_runtime_exact_M2_depth2` | PASS | - | - |
| controls-stock | `test_runtime_exact_M2_depth4` | PASS | - | - |
| controls-stock | `test_source_M1_depth2` | PASS | - | - |
| controls-stock | `test_source_M1_depth4` | PASS | - | - |
| controls-stock | `test_source_M2_depth2` | PASS | - | - |
| controls-stock | `test_source_M2_depth4` | PASS | - | - |
| controls-stock | `test_source_M3_depth2` | PASS | - | - |
| controls-stock | `test_source_M3_depth4` | PASS | - | - |
| controls-stock | `test_source_exact_M1_depth2` | PASS | - | - |
| controls-stock | `test_source_exact_M1_depth4` | PASS | - | - |
| controls-stock | `test_source_exact_M2_depth2` | PASS | - | - |
| controls-stock | `test_source_exact_M2_depth4` | PASS | - | - |
| controls-stock | `test_stub_matches_archived_runtime` | PASS | - | - |
| controls-mutants | `test_runtime_M1_depth2` | FAIL:loop-frame:_slot_0_changed | - | - |
| controls-mutants | `test_runtime_M1_depth4` | FAIL:loop-frame:_slot_0_changed | - | - |
| controls-mutants | `test_runtime_M2_depth2` | FAIL:loop-frame2:_watched_leaves_key_changed | - | - |
| controls-mutants | `test_runtime_M2_depth4` | FAIL:loop-frame2:_watched_leaves_key_changed | - | - |
| controls-mutants | `test_runtime_M3_depth2` | FAIL:post-loop-exact:_leaves[LEAF]_missing | - | - |
| controls-mutants | `test_runtime_M3_depth4` | FAIL:post-loop-exact:_leaves[LEAF]_missing | - | - |
| controls-mutants | `test_runtime_exact_M1_depth2` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_runtime_exact_M1_depth4` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_runtime_exact_M2_depth2` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_runtime_exact_M2_depth4` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_source_M1_depth2` | FAIL:loop-frame:_slot_0_changed | - | - |
| controls-mutants | `test_source_M1_depth4` | FAIL:loop-frame:_slot_0_changed | - | - |
| controls-mutants | `test_source_M2_depth2` | FAIL:loop-frame2:_watched_leaves_key_changed | - | - |
| controls-mutants | `test_source_M2_depth4` | FAIL:loop-frame2:_watched_leaves_key_changed | - | - |
| controls-mutants | `test_source_M3_depth2` | FAIL:post-loop-exact:_leaves[LEAF]_missing | - | - |
| controls-mutants | `test_source_M3_depth4` | FAIL:post-loop-exact:_leaves[LEAF]_missing | - | - |
| controls-mutants | `test_source_exact_M1_depth2` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_source_exact_M1_depth4` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_source_exact_M2_depth2` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_source_exact_M2_depth4` | FAIL:loop-exact:_sideNodes_mismatch | - | - |
| controls-mutants | `test_stub_matches_archived_runtime` | PASS | - | - |
| controls | `all-checks` | PASS | - | - |
| build | `build` | BUILT | - | 141s |
| rejections | `TreeRejections.prove_reject_field` | PASSED | - | 28s |
| rejections | `TreeRejections.prove_reject_zero` | PASSED | - | 23s |
| rejections | `TreeRejections.prove_reject_duplicate` | PASSED | - | 44s |
| rejections | `TreeRejections_M_FIELD.prove_reject_field` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 25) | 1m 48s |
| rejections | `TreeRejections_M_ZERO.prove_reject_zero` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 25) | 1m 36s |
| rejections | `TreeRejections_M_DUP.prove_reject_duplicate` | FAILED | EVMC_REVERT:4e487b710000000000000000000000000000000000000000000000000000000000000001 (node 27) | 1m 42s |

CHECK PASS suite insert-loop


## public-inputs

| Run | Started (UTC) | Wall | Peak memory | Outcome |
|---|---|---|---|---|
| build | 2026-10-24T15:18:15Z | 143 s | 8.59 GB | BUILD_EXIT=0 |
| replay | - | - | - | host run |

| Run | Proof | Verdict | Failing node output | Time |
|---|---|---|---|---|
| build | `build` | BUILT | - | 143s |
| replay | `CanonicalInputsReplay.test_S1d0_c_noncanonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1d0_canonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1d0_root_noncanonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1d0_witness` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1d_split` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1t0_c1_noncanonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1t0_canonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1t0_n0_noncanonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1t0_r_noncanonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1t0_witness` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1t_split` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1w_canonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1w_n_noncanonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1w_r_noncanonical` | PASS | - | - |
| replay | `CanonicalInputsReplay.test_S1w_witness` | PASS | - | - |
| replay | `CanonicalInputsReplay_M_BOUND_GT.test_w_n_P_plus_1_rejected` | PASS | - | - |
| replay | `CanonicalInputsReplay_M_BOUND_GT.test_w_n_eq_P` | PASS | - | - |
| replay | `CanonicalInputsReplay_M_DEPOSIT_CANONICAL.test_c` | PASS | - | - |
| replay | `CanonicalInputsReplay_M_DEPOSIT_CANONICAL.test_root` | PASS | - | - |
| replay | `CanonicalInputsReplay_M_TRANSFER_CANONICAL.test_n0` | PASS | - | - |
| replay | `CanonicalInputsReplay_M_WITHDRAW_CANONICAL.test_n` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay.test_W_success_original_a` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay.test_W_success_original_b` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay.test_W_success_original_c` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay.test_W_witness_original` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay_M_DROP_BIT253.test_replay` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay_M_LATE_MARK.test_replay` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay_M_PAY_CALLER.test_replay` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay_M_SKIP_VERIFIER.test_replay` | PASS | - | - |
| replay | `FixedTokenWithdrawReplay_M_SWAP_INPUTS.test_replay` | PASS | - | - |
| replay | `InputOrderReplay.test_S2_original` | PASS | - | - |
| replay | `InputOrderReplay.test_S2_witness_original` | PASS | - | - |
| replay | `InputOrderReplay_M_DEPOSIT_SWAP_45.test_replay` | PASS | - | - |
| replay | `InputOrderReplay_M_TRANSFER_SWAP_45.test_replay` | PASS | - | - |
| replay | `InputOrderWitnessReplay.test_S2d0_witness` | PASS | - | - |
| replay | `InputOrderWitnessReplay.test_S2t0_witness` | PASS | - | - |

CHECK PASS suite public-inputs (partial: not run canonical, order, fixed-token)


Runs `canonical`, `order` and `fixed-token`: not started; time budget exhausted. Their expected verdicts in EXPECTED.tsv are results of the 2026-10-01 run on the 0.8.33 build.

## poseidon-frame

| Run | Started (UTC) | Wall | Peak memory | Outcome |
|---|---|---|---|---|
| frame | - | - | - | host run |

| Run | Proof | Verdict | Failing node output | Time |
|---|---|---|---|---|
| frame-real-final | `check_call_context_same_result` | PASS | - | - |
| frame-real-final | `check_frame_equal_inputs` | PASS | - | - |
| frame-real-final | `check_wrong_selector` | PASS | - | - |
| frame-short-calldata | `check_short_calldata` | PASS | - | - |
| frame-mutant-witness | `check_mutant_witness` | FAIL | - | - |
| frame-deployment | `DeploymentTest.test_constructor_runtime` | PASS | - | - |
| frame-replay | `RealReplay.test_concrete_frame` | PASS | - | - |
| frame-replay | `MutantReplay.test_concrete_frame` | FAIL | - | - |
| frame | `all-checks` | PASS | - | - |

CHECK PASS suite poseidon-frame


