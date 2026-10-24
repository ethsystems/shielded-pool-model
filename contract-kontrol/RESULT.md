# contract-kontrol: runs of 2026-10-24

These are the runs of `check.sh` on 2026-10-24, on a Linux x86_64 laptop (16 threads, 30 GiB, btrfs)
that other jobs shared (`free -g` showed 5 to 15 GiB available during the runs). Each run used a
`git archive` copy of the package at the commit named below, with `POCS`, `DEPS_CACHE` and `WORK`
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
| `insert-loop` | K claims in `k/` | not rerun here; expected values from the earlier run | `check.sh` does not run them (README.md) |
| `public-inputs` | `canonical`, `order`, `fixed-token` | not rerun here; expected values from the earlier run | stopped at the time limit; the build and the replays ran (run 6) |
| `public-inputs` | build, `replay` | yes (run 6) | build passes (143 s, peak 8.59 GB, just under the 8 GiB cap); 36 of 36 replays pass |
| `poseidon-frame` | `frame` | yes (run 5; also run 4) | 9 of 9 as expected: four real checks PASS with 1, 1, 2 and 132 paths, the mutant witness FAILs with one valid model, the deployment test and the real replay pass, the mutant replay fails |

Runs, each `check.sh` from a `git archive` copy of the package:

- run 3, commit `bcf2eff`, `./check.sh withdraw-success guards-patched guards-stock public-inputs`,
  started about 10:14Z: the `withdraw-success` build hit the cap (below); `guards-patched` ran to the end;
  I stopped the run after it to start the queue below with `withdraw-success` first. Its
  comparison was run on its work directory afterwards (`scripts/compare.py EXPECTED.tsv work
  guards-patched`).
- run 5, commit `af458b3`, `./check.sh withdraw-success guards-stock insert-loop public-inputs
  poseidon-frame`, started 11:14Z, 14,617 s: four suites `CHECK PASS`; I stopped the
  `public-inputs` build container after 11 s at the time limit, so that suite reads
  `BUILD-FAILED` there and the last line is `CHECK FAIL`.
- run 6, commit `af458b3`, `./check.sh public-inputs:none` (the build and the replays, no proof
  run), started 15:18Z, 151 s: `CHECK PASS suite public-inputs (partial: not run canonical, order,
  fixed-token)`.
- run 2 (commit `fddc38b`, `insert-loop` with `controls` only) and run 4 (commit `5e82a71`,
  `poseidon-frame`) gave the same results as run 5 for those runs.
- run 7, commit `939e653`, `./check.sh insert-loop`, started 15:24Z, 439 s: `CHECK PASS` (all 50
  lines; build 7.25 GB, `rejections` 299 s at 3.71 GB, failing nodes 22, 25 and 29). Commit
  `939e653` came after runs 3 to 6 and changed no proof input: the prove commands spell
  `--workers` as its alias `-j` (both are one option of the image's `pyk`), and `check.sh` asks the
  image for the path of its `abi.md` in place of a pinned path. Run 7 checks that end to end.

Between run 3 and run 5 the harness of `withdraw-success` changed (commit `a8586b7`: the probe and
witness bodies moved out of the mutant siblings, bodies unchanged) and `insert-loop` gained the
`rejections` run; no other suite input changed.

## What was checked beyond the verdicts

- `withdraw-success` `token-above-0x11`, the stock graph: 225 nodes, 173 edges, 15 splits, 2
  non-deterministic branches (the token call), 36 terminal nodes, one leaf (the target), 0 vacuous,
  0 stuck. The earlier report gives the same counts.
- `withdraw-success` `two-tokens`, the stock graph: 248 nodes, 184 edges, 31 splits, 34 terminal
  nodes, one leaf (the target), 0 vacuous, 0 stuck (earlier: 248 nodes, 31 splits).
- The failing node of `FIXED_TOKEN` in `token-above-0x11` (node 122) has the path constraints
  `17 < token`, `token != ` the cheatcode account and `token != 0xf000...000b`: the failure is at a
  token other than the fixed one, as in the earlier run.
- The failing node of `DEPOSIT_FUNDER_CALLER` (node 90): Kontrol prints the path condition
  `P <= c`, so with the caller check removed the canonical-input check fires first, as in the
  earlier run (node 89, `c >= P`).
- `guards-patched`, the four stock graphs have 51, 51, 53 and 69 nodes, as in the earlier run.
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
- `public-inputs` `canonical`, `order`, `fixed-token`: not started (time limit). In the earlier run
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


Runs `canonical`, `order` and `fixed-token`: not rerun here; expected values from the earlier run (EXPECTED.tsv, dated 2026-10-01).

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


