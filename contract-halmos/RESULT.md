# RESULT: the run of 2026-10-24

## Summary

```
CHECK PASS: 9 suites, 418 verdicts equal EXPECTED.tsv, 55 path counts differ from the frozen runs (PATHS lines), 4659s
```

Every one of the 418 verdicts (391 Halmos verdicts and 27 forge tests) equals `EXPECTED.tsv`. The
inventory step passed: every run of `runs.tsv` has expected verdicts, and every mutant is checked
as `MUTANTS.tsv` says (91 by their own runs, seven ring-funding copies run in insert-callback,
NO_GUARD_W inside a root-window check). All 91 mutants that have their own runs fail their named
checks; the caller mutants fail at their named assertions (`NotMarkedAtPayout`, `PayoutArgs`). No
run is void: every log has one `SCOPE` line, every exit status is the expected one, Halmos's result
lines count the recorded verdicts, and no log has a kill, a timeout, a traceback, a loop-bound
warning or a solver unknown. The only raw-scan hit is the expected `NotConcreteError` of the
arbitrary-calldata attempt (`duplicate-lock/attempt-raw-calldata`, three ERROR verdicts). 55 of the
379 path counts that have a frozen value differ from it (list below); every difference is in a
count, none in a verdict.

## The run

- Date: 2026-10-24, started 13:41 UTC, from a local commit whose `contract-halmos/` tree is the one of
  `8338e47` on this branch (the last package commit before the run), with the submodule `contract-halmos/pocs` at
  `a04b8b38969dfc2ee64de47edee7e396454204a8`. After that commit, this file and one README sentence
  (the reports of 2026-09-29 and 2026-09-30 are not in this repository) changed, and one stray
  line of pasted output was removed from `PINS.txt` (no pin changed); no other file `check.sh`
  reads changed.
- Command: `PYTHON=<python 3.12.14> ./check.sh --venv`. `.venv/` came from an earlier
  `./check.sh --venv` of the same day (pip `--require-hashes` from PyPI) and was not reinstalled;
  this run checked it: `pyenv: 19 distributions at the versions of requirements.txt, 811 files equal
  their RECORD hashes, no stray entry in site-packages; 19 of 19 RECORD digests equal PINS.txt`.
  `.deps/` came from the same earlier run and was hashed again.
- Machine: Linux x86_64 laptop, Intel Core Ultra X7 358H, 16 threads, 30 GB; other checks were
  running at the same time. Runner line: `runner: one systemd user scope per run, MemoryMax=8G,
  MemorySwapMax=512M, killed after 900 s`.
- Tools: halmos 0.3.3 on Python 3.12.14, run as `python -I -m halmos`; z3 4.12.6 (Python module),
  yices 2.6.4 (`yices-smt2`, sha256 `8b5598ac…`), forge 1.8.3 (`cae51ad4`, sha256 `deb412a7…`),
  solc 0.8.37+commit.f401782d (sha256 `5de843c2…`). All match `PINS.txt`; no unpinned build.
- Setup lines: `source: pocs a04b8b38…, 14 files under pocs/private-payment/shielded-pool equal the
  blob pins`; `deps: 3 soldeer zips by sha256 and integrity, zk-kit.solidity a171c845… tree
  7ced94ae…`; every suite: `14 files equal their blobs at a04b8b3; library patch`, and its mutant
  diffs applied with sha256 equal to `MUTANTS.sha256`.
- Wall time: 4659 s for `check.sh` (77 min 39 s). Runs per suite: caller 44 s, duplicate-lock
  153 s, insert-callback 1157 s, owner-payout 391 s, guards 409 s, ring-funding 211 s,
  post-deposit-withdraw 809 s, post-transfer-admin 841 s, root-window 512 s.
- Memory: the highest scope peak was 3.09 GiB (`insert-callback/mutant-NR_T`), then 2.44 GiB
  (`root-window/cap-witness-transfer-255`); every other run stayed below 1.9 GiB. A peak is the
  scope's `memory.peak`, which also counts page cache.
- Disk: `work/` takes about 1.5 GB (one project per suite, three variant projects for
  ring-funding); `.venv/` 200 MB.

## Path counts that differ from the frozen runs

Halmos decides branch feasibility with a 1 ms solver timeout, so a count depends on the machine and
its load; `--early-exit` runs stop at the first counterexample while other paths are in flight.
`EXPECTED.tsv` keeps the frozen counts (a range where a first run and its fresh rerun differed) and
was not changed to match this run.

```
duplicate-lock dup-full check_D5_dupReverts: PASS paths=56, frozen run paths=55
duplicate-lock mutant-NR_T-band check_X1core_lockedTransfer: FAIL paths=8, frozen run paths=6-7
insert-callback mutant-DUP-deposit check_D5s_depositTwice_reverts: FAIL paths=78, frozen run paths=77
insert-callback mutant-INS_D check_D5b_depositInsertsCommitment: FAIL paths=306, frozen run paths=307-310
insert-callback mutant-SWAP_T check_T11b_transferInsertsOutputsInOrder: FAIL paths=306, frozen run paths=304
insert-callback mutant-NR_T check_X1_depositReentersTransfer: FAIL paths=3932, frozen run paths=3922-3923
insert-callback mutant-NR_T check_X1_withdrawReentersTransfer: FAIL paths=702, frozen run paths=680-681
insert-callback mutant-NR_W check_X1_depositReentersWithdraw: FAIL paths=1644, frozen run paths=1642
insert-callback mutant-ORD_D check_X2_depositTreeUpdatedBeforeTokenCall: FAIL paths=155, frozen run paths=154
insert-callback mutant-ORD_W check_X2_withdrawSpentBeforeTokenCall: FAIL paths=10, frozen run paths=6
owner-payout sweep check_G1_sweep_nonOwnerKeepsAdminState: PASS paths=2480, frozen run paths=2479
owner-payout sweep check_WIT_sweepSomeCallSucceeds_expectFail: FAIL paths=2482, frozen run paths=2478-2481
guards guards check_withdraw_zeroAmount: PASS paths=11, frozen run paths=10
guards core-mutant-TR_CANONICAL check_core_transfer_nonCanonicalInput: FAIL paths=133, frozen run paths=132
ring-funding funding-witness check_D6_successWitness_expectFail: FAIL paths=7, frozen run paths=8
ring-funding ring-deposit check_FRW_deposit_index: PASS paths=173, frozen run paths=174-175
ring-funding ring-transfer check_FRW_transfer_index: PASS paths=689, frozen run paths=681
ring-funding ring-witnesses check_FRW_W_deposit_expectFail: FAIL paths=19, frozen run paths=20
ring-funding reached-roots check_RW_postOpRootsOnly: PASS paths=6, frozen run paths=7-8
ring-funding deposit-order check_X2_depositTreeUpdatedBeforeTokenCall: PASS paths=156, frozen run paths=154
post-deposit-withdraw D_amount_ne_zero check_D_amount_ne_zero: PASS paths=403, frozen run paths=400
post-deposit-withdraw mutant-D_amount_ne_zero check_D_amount_ne_zero: FAIL paths=16, frozen run paths=20-21
post-deposit-withdraw mutant-D_fresh_leaf check_D_fresh_leaf: FAIL paths=20, frozen run paths=22
post-deposit-withdraw mutant-D_post check_D_post: FAIL paths=530, frozen run paths=529
post-deposit-withdraw mutant-D_token_calls check_D_token_calls: FAIL paths=19, frozen run paths=17
post-deposit-withdraw mutant-D_verified check_D_verified: FAIL paths=17, frozen run paths=16
post-transfer-admin A_registry check_A_registry: PASS paths=11, frozen run paths=10
post-transfer-admin mutant-T_known_root check_T_known_root: FAIL paths=29, frozen run paths=30
post-transfer-admin mutant-T_no_effects check_T_no_effects: FAIL paths=21, frozen run paths=22
post-transfer-admin mutant-T_post_mapping check_T_post: FAIL paths=56, frozen run paths=50-52
post-transfer-admin mutant-T_post_order check_T_post: FAIL paths=33, frozen run paths=29
post-transfer-admin mutant-T_verified_canonical check_T_verified: FAIL paths=21, frozen run paths=20
post-transfer-admin mutant-T_verified check_T_verified: FAIL paths=24, frozen run paths=22-23
post-transfer-admin mutant-T_verified_root check_T_verified: FAIL paths=22, frozen run paths=21
post-transfer-admin T_fresh_outputs check_T_fresh_outputs: PASS paths=1305, frozen run paths=1307-1312
post-transfer-admin T_fresh_outputs_witness check_T_fresh_outputs_witness: FAIL paths=30, frozen run paths=31-32
post-transfer-admin T_post check_T_post: PASS paths=8135, frozen run paths=8181-8196
post-transfer-admin T_post_witness check_T_post_witness: FAIL paths=32, frozen run paths=26-28
post-transfer-admin T_verified_witness check_T_verified_witness: FAIL paths=18, frozen run paths=21
root-window reached check_P3b_freshReentryFails: PASS paths=8, frozen run paths=9
root-window reached check_P3b_freshReentryGuardError: PASS paths=9, frozen run paths=8
root-window reached check_P4_knownRootsOnly_reached: PASS paths=5, frozen run paths=4
root-window reached check_P4v1_postTxRootsOnly: PASS paths=8, frozen run paths=5
root-window reached check_W_P2_firstWithdrawReachable_expectFail: FAIL paths=9, frozen run paths=8
root-window reached check_W_P3b_withdrawSuccessReachable_expectFail: FAIL paths=7, frozen run paths=8
root-window fresh-depth40 check_F40_P5_withdraw: PASS paths=16, frozen run paths=15
root-window fresh-depth40 check_F40_W_withdraw_expectFail: FAIL paths=16, frozen run paths=15
root-window depth-cap check_R256i_deposit: PASS paths=9, frozen run paths=8
root-window cap-witness-deposit-255 check_RWc_deposit_expectFail: FAIL paths=11, frozen run paths=10
root-window cap-witness-deposit-64 check_RWc_deposit_expectFail: FAIL paths=13, frozen run paths=10
root-window band8-P5-deposit check_B_P5_deposit: PASS paths=4101, frozen run paths=4095
root-window band8-P1-deposit check_B_P1_deposit: PASS paths=3069, frozen run paths=3067
root-window band8-witness-deposit check_B_W_deposit_expectFail: FAIL paths=1553, frozen run paths=1554
root-window band4-P5-transfer check_B_P5_transfer: PASS paths=810, frozen run paths=792
root-window band4-P1-transfer check_B_P1_transfer: PASS paths=907, frozen run paths=912
```

## Earlier runs of the same day, on Python 3.14

Before Python 3.12 was pinned, the suites ran once each on a venv with Python 3.14.9 (same
requirements, same tools). All verdicts matched `EXPECTED.tsv` except one: the run
`guards/spent-mutant-TR_SPENT0` was killed by the 8 GB cap after 26 s (the Halmos process reached
8.1 GB) and recorded no verdict. Two reruns on 3.14 gave one more kill and one FAIL with 127 paths
at 1.5 GB; three reruns on 3.12.14 gave FAIL with 127 paths at 1.2 GB each time, as the first run
did (0.55 GB under its 3 GB cap). Path counts on 3.14 also drifted further from the frozen ones:
`ring-funding/ring-transfer` explored 1017 paths (frozen 681; 718 on 3.12 in a separate rerun) and
`ring-funding/deposit-order` 198 (frozen 154; 154 on 3.12). `check.sh` therefore requires Python
3.12. Those 3.14 runs are not the result of this file.

An earlier version of this file recorded a run of an earlier commit of this package, before the
inventory, exit-status and Python-environment checks were added. It also ended in `CHECK PASS`,
with 418 verdicts, 66 path differences and 4852 s.

## Mutants

Every mutant that has its own runs, with the number of its checks that fail. The root-window control
NO_GUARD_W has no run of its own: `check_P3b_noGuard_freshReentryFails_expectFail` deploys it and
FAILs (root-window table). The insert-callback mutants that ring-funding builds but does not run are
not repeated there.

| Suite | Mutant | Runs | Checks that FAIL | Assertion |
|---|---|---|---|---|
| caller | LATE_MARK | 1 | 1 of 1 | NotMarkedAtPayout |
| caller | PAY_CALLER | 1 | 1 of 1 | PayoutArgs |
| duplicate-lock | SKIP | 2 | 4 of 4 | - |
| duplicate-lock | DUP | 2 | 3 of 3 | - |
| duplicate-lock | ARG | 2 | 3 of 3 | - |
| duplicate-lock | NR_W | 2 | 5 of 5 | - |
| duplicate-lock | NR_D | 2 | 4 of 4 | - |
| duplicate-lock | NR_T | 2 | 3 of 3 | - |
| insert-callback | DUP | 2 | 5 of 5 | - |
| insert-callback | INS_D | 1 | 1 of 1 | - |
| insert-callback | SWAP_T | 1 | 1 of 1 | - |
| insert-callback | NR_D | 2 | 4 of 4 | - |
| insert-callback | NR_T | 2 | 4 of 4 | - |
| insert-callback | NR_W | 2 | 4 of 4 | - |
| insert-callback | ORD_D | 1 | 1 of 1 | - |
| insert-callback | ORD_W | 1 | 1 of 1 | - |
| owner-payout | PAY_SENDER | 1 | 1 of 1 | - |
| owner-payout | PAY_AMT1 | 1 | 1 of 1 | - |
| owner-payout | PAY_TOK | 1 | 1 of 1 | - |
| owner-payout | PAY_TWICE | 1 | 1 of 1 | - |
| owner-payout | PAY_RCP_HI | 1 | 1 of 1 | - |
| owner-payout | PI_TOK | 1 | 1 of 1 | - |
| owner-payout | PI_AMT | 1 | 1 of 1 | - |
| owner-payout | PI_RCP | 1 | 1 of 1 | - |
| owner-payout | PI_NUL_HI | 1 | 1 of 1 | - |
| owner-payout | PI_TOK_HI | 1 | 1 of 1 | - |
| owner-payout | PI_RCP_HI | 1 | 1 of 1 | - |
| owner-payout | PI_ROOT_HI | 1 | 1 of 1 | - |
| owner-payout | OO_ADD | 1 | 2 of 2 | - |
| owner-payout | OO_REM | 1 | 2 of 2 | - |
| owner-payout | OO_SETV | 1 | 2 of 2 | - |
| owner-payout | OO_SETR | 1 | 2 of 2 | - |
| owner-payout | OO_OWN | 1 | 2 of 2 | - |
| owner-payout | EFF_ADD | 1 | 1 of 1 | - |
| owner-payout | EFF_REM | 1 | 1 of 1 | - |
| owner-payout | EFF_SETV | 1 | 1 of 1 | - |
| owner-payout | EFF_SETR | 1 | 1 of 1 | - |
| owner-payout | EFF_OWN | 1 | 1 of 1 | - |
| guards | DEP_TOKEN | 2 | 2 of 2 | - |
| guards | DEP_AMOUNT_ZERO | 2 | 2 of 2 | - |
| guards | DEP_AMOUNT_MAX | 2 | 2 of 2 | - |
| guards | DEP_FUNDER_ZERO | 3 | 2 of 3 (check_core_deposit_zeroFundingAddress_nonzeroCaller PASS) | - |
| guards | DEP_FUNDER_CALLER | 2 | 2 of 2 | - |
| guards | DEP_CANONICAL | 2 | 2 of 2 | - |
| guards | TR_DISTINCT | 2 | 2 of 2 | - |
| guards | TR_SPENT0 | 3 | 3 of 3 | - |
| guards | TR_SPENT1 | 3 | 3 of 3 | - |
| guards | TR_ROOT | 2 | 2 of 2 | - |
| guards | TR_CANONICAL | 2 | 2 of 2 | - |
| guards | WD_TOKEN | 2 | 2 of 2 | - |
| guards | WD_AMOUNT_ZERO | 2 | 2 of 2 | - |
| guards | WD_AMOUNT_MAX | 2 | 2 of 2 | - |
| guards | WD_RECIPIENT_ZERO | 2 | 2 of 2 | - |
| guards | WD_SPENT | 3 | 3 of 3 | - |
| guards | WD_ROOT | 2 | 2 of 2 | - |
| guards | WD_CANONICAL | 2 | 2 of 2 | - |
| ring-funding | D6 | 1 | 1 of 1 | - |
| ring-funding | D6_CALLER | 1 | 1 of 1 | - |
| ring-funding | ORD_D | 1 | 1 of 1 | - |
| ring-funding | M1 | 1 | 1 of 1 | - |
| ring-funding | M2 | 1 | 2 of 2 | - |
| ring-funding | M3 | 1 | 1 of 1 | - |
| post-deposit-withdraw | D_amount_ne_zero | 1 | 1 of 1 | - |
| post-deposit-withdraw | D_fresh_leaf | 1 | 1 of 1 | - |
| post-deposit-withdraw | D_guarded | 1 | 1 of 1 | - |
| post-deposit-withdraw | D_post | 1 | 1 of 1 | - |
| post-deposit-withdraw | D_supported | 1 | 1 of 1 | - |
| post-deposit-withdraw | D_token_calls | 1 | 1 of 1 | - |
| post-deposit-withdraw | D_verified | 1 | 1 of 1 | - |
| post-deposit-withdraw | W_amount_ne_zero | 1 | 1 of 1 | - |
| post-deposit-withdraw | W_guarded | 1 | 1 of 1 | - |
| post-deposit-withdraw | W_known_root | 1 | 1 of 1 | - |
| post-deposit-withdraw | W_post | 1 | 1 of 1 | - |
| post-deposit-withdraw | W_token_calls | 1 | 1 of 1 | - |
| post-deposit-withdraw | W_unspent | 1 | 1 of 1 | - |
| post-deposit-withdraw | W_verified | 1 | 1 of 1 | - |
| post-transfer-admin | A_add | 1 | 1 of 1 | - |
| post-transfer-admin | A_owner | 1 | 1 of 1 | - |
| post-transfer-admin | A_registry | 1 | 1 of 1 | - |
| post-transfer-admin | A_remove | 1 | 1 of 1 | - |
| post-transfer-admin | T_distinct | 1 | 1 of 1 | - |
| post-transfer-admin | T_fresh_outputs | 1 | 1 of 1 | - |
| post-transfer-admin | T_known_root | 1 | 1 of 1 | - |
| post-transfer-admin | T_no_effects | 1 | 1 of 1 | - |
| post-transfer-admin | T_post | 1 | 1 of 1 | - |
| post-transfer-admin | T_post_mapping | 1 | 1 of 1 | - |
| post-transfer-admin | T_post_order | 1 | 1 of 1 | - |
| post-transfer-admin | T_unspent | 1 | 1 of 1 | - |
| post-transfer-admin | T_verified_canonical | 1 | 1 of 1 | - |
| post-transfer-admin | T_verified | 1 | 1 of 1 | - |
| post-transfer-admin | T_verified_root | 1 | 1 of 1 | - |

91 mutants

`DEP_FUNDER_ZERO` (zero-funder guard removed) fails its check and its core check with caller 0;
`check_core_deposit_zeroFundingAddress_nonzeroCaller` passes on it, as expected: with a nonzero
caller the caller-mismatch guard still rejects a zero funder.

## Every check

Columns: the run, the check, its verdict and path count, the expected verdict and count (and
assertion), Halmos's time for the check, the wall time and the scope's memory peak of the run.
"(differs)" marks a path count outside its expected value or range.

### caller

7 runs, 14 verdicts, run wall 43 s, highest peak 1.64 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| stock | `check_withdraw` | PASS | 154 | PASS 154 | 3.86 | 11.5 | 0.92 |
|  | `check_witnessHigh` | FAIL | 62 | FAIL 62 | 1.20 |  |  |
|  | `check_witnessLow` | FAIL | 62 | FAIL 62 | 1.07 |  |  |
| loop4 | `check_withdraw` | PASS | 64 | PASS 64 | 1.57 | 7.1 | 1.01 |
| loop8 | `check_withdraw` | PASS | 64 | PASS 64 | 1.78 | 7.0 | 0.92 |
| alias-debug | `check_withdraw` | PASS | 34 | PASS 34 | 1.13 | 6.2 | 0.92 |
| mutant-LATE_MARK | `check_withdraw` | FAIL | 17 | FAIL 17, NotMarkedAtPayout | 0.28 | 5.3 | 0.95 |
| mutant-PAY_CALLER | `check_withdraw` | FAIL | 17 | FAIL 17, PayoutArgs | 0.25 | 4.8 | 0.93 |
| replay | `WithdrawCallerReplay.test_stock_otherCaller` | PASS | - | PASS - | - | 1.3 | 1.64 |
|  | `WithdrawCallerReplay.test_stock_point` | PASS | - | PASS - | - |  |  |
|  | `WithdrawCallerReplay_LATE_MARK.test_replay_fails` | PASS | - | PASS - | - |  |  |
|  | `WithdrawCallerReplay_LATE_MARK.test_replay_kind` | PASS | - | PASS - | - |  |  |
|  | `WithdrawCallerReplay_PAY_CALLER.test_replay_fails` | PASS | - | PASS - | - |  |  |
|  | `WithdrawCallerReplay_PAY_CALLER.test_replay_kind` | PASS | - | PASS - | - |  |  |

### duplicate-lock

21 runs, 66 verdicts, run wall 153 s, highest peak 1.85 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| probe | `check_PROBE_lockSlotIsConcreteOne_expectFail` | FAIL | 1 | FAIL 1 | 0.13 | 5.1 | 1.11 |
| dup-full | `check_D5_dupAnyGuards` | PASS | 310 | PASS 310 | 4.87 | 15.7 | 1.14 |
|  | `check_D5_dupCore` | PASS | 55 | PASS 55 | 2.71 |  |  |
|  | `check_D5_dupReverts` | PASS | 56 | PASS 55 (differs) | 3.07 |  |  |
| dup-probe-full | `check_D5_dupProbe` | PASS | 55 | PASS 55 | 3.44 | 8.3 | 1.02 |
| lock-full | `check_X1_lockedDeposit` | PASS | 40 | PASS 40 | 1.41 | 9.6 | 1.12 |
|  | `check_X1_lockedTransfer` | PASS | 30 | PASS 30 | 1.05 |  |  |
|  | `check_X1_lockedWithdraw` | PASS | 20 | PASS 20 | 0.22 |  |  |
|  | `check_X1s_lockedDeposit` | PASS | 35 | PASS 35 | 0.93 |  |  |
|  | `check_X1s_lockedTransfer` | PASS | 25 | PASS 25 | 1.22 |  |  |
|  | `check_X1s_lockedWithdraw` | PASS | 15 | PASS 15 | 0.19 |  |  |
| lock-core-full | `check_SANITY_staticWriteHaltsEmpty` | PASS | 4 | PASS 4 | 0.05 | 7.9 | 1.09 |
|  | `check_WIT_X1_unlockedWithdrawSucceeds_expectFail` | FAIL | 3 | FAIL 3 | 0.19 |  |  |
|  | `check_X1acq_withdraw` | PASS | 6 | PASS 6 | 0.73 |  |  |
|  | `check_X1core_lockedDeposit` | PASS | 10 | PASS 10 | 0.25 |  |  |
|  | `check_X1core_lockedTransfer` | PASS | 40 | PASS 40 | 1.21 |  |  |
|  | `check_X1core_lockedWithdraw` | PASS | 10 | PASS 10 | 0.57 |  |  |
|  | `check_X1s_lockedWithdrawBenign` | PASS | 10 | PASS 10 | 0.24 |  |  |
| band | `check_D5_dupCore` | PASS | 8 | PASS 8 | 0.76 | 27.0 | 1.02 |
|  | `check_D5_dupReverts` | PASS | 8 | PASS 8 | 0.46 |  |  |
|  | `check_WIT_D5_newLeafSucceeds_expectFail` | FAIL | 39 | FAIL 39 | 1.50 |  |  |
|  | `check_WIT_X1_unlockedDepositSucceeds_expectFail` | FAIL | 39 | FAIL 39 | 1.85 |  |  |
|  | `check_WIT_X1_unlockedTransferSucceeds_expectFail` | FAIL | 78 | FAIL 76-81 | 6.59 |  |  |
|  | `check_X1acq_deposit` | PASS | 154 | PASS 154 | 9.13 |  |  |
|  | `check_X1core_lockedDeposit` | PASS | 10 | PASS 10 | 0.31 |  |  |
|  | `check_X1core_lockedTransfer` | PASS | 40 | PASS 40 | 1.69 |  |  |
| band-probe | `check_D5_dupProbe` | PASS | 8 | PASS 8 | 0.88 | 5.8 | 1.02 |
| mutant-SKIP-full | `check_D5_dupAnyGuards` | FAIL | 23 | FAIL 23 | 0.66 | 6.1 | 1.06 |
|  | `check_D5_dupCore` | FAIL | 5 | FAIL 5 | 0.27 |  |  |
|  | `check_D5_dupReverts` | FAIL | 5 | FAIL 5 | 0.27 |  |  |
| mutant-SKIP-probe | `check_D5_dupProbe` | FAIL | 5 | FAIL 5 | 0.32 | 5.3 | 1.06 |
| mutant-DUP-band | `check_D5_dupCore` | FAIL | 7 | FAIL 7 | 0.39 | 5.9 | 1.03 |
|  | `check_D5_dupReverts` | FAIL | 6 | FAIL 6 | 0.72 |  |  |
| mutant-DUP-probe | `check_D5_dupProbe` | FAIL | 7 | FAIL 7 | 0.77 | 5.4 | 1.02 |
| mutant-ARG-band | `check_D5_dupCore` | FAIL | 9 | FAIL 9 | 0.86 | 5.8 | 1.11 |
|  | `check_D5_dupReverts` | FAIL | 4 | FAIL 4 | 0.13 |  |  |
| mutant-ARG-probe | `check_D5_dupProbe` | FAIL | 4 | FAIL 4 | 0.16 | 4.8 | 1.02 |
| mutant-NR_W-full | `check_X1acq_withdraw` | FAIL | 3 | FAIL 3 | 0.20 | 5.7 | 1.02 |
|  | `check_X1core_lockedWithdraw` | FAIL | 3 | FAIL 3 | 0.52 |  |  |
|  | `check_X1s_lockedWithdrawBenign` | FAIL | 3 | FAIL 3 | 0.16 |  |  |
| mutant-NR_W-trip | `check_X1_lockedWithdraw` | FAIL | 5 | FAIL 5 | 0.07 | 4.8 | 1.02 |
|  | `check_X1s_lockedWithdraw` | FAIL | 4 | FAIL 4 | 0.05 |  |  |
| mutant-NR_D-trip | `check_X1_lockedDeposit` | FAIL | 5 | FAIL 5 | 0.07 | 4.8 | 1.02 |
|  | `check_X1s_lockedDeposit` | FAIL | 4 | FAIL 4 | 0.06 |  |  |
| mutant-NR_D-band | `check_X1acq_deposit` | FAIL | 4 | FAIL 4 | 0.73 | 5.8 | 1.02 |
|  | `check_X1core_lockedDeposit` | FAIL | 7 | FAIL 7 | 0.36 |  |  |
| mutant-NR_T-trip | `check_X1_lockedTransfer` | FAIL | 3 | FAIL 3 | 0.06 | 4.8 | 1.11 |
|  | `check_X1s_lockedTransfer` | FAIL | 2 | FAIL 2 | 0.06 |  |  |
| mutant-NR_T-band | `check_X1core_lockedTransfer` | FAIL | 8 | FAIL 6-7 (differs) | 1.25 | 5.9 | 1.14 |
| attempt-raw-calldata | `check_X1raw_lockedDeposit` | ERROR | 34 | ERROR 34 | 0.95 | 6.8 | 1.15 |
|  | `check_X1raw_lockedTransfer` | ERROR | 32 | ERROR 32 | 0.59 |  |  |
|  | `check_X1raw_lockedWithdraw` | ERROR | 34 | ERROR 34 | 0.61 |  |  |
| replay | `DuplicateLockReplayTest.test_D5_ARG_depositOfExistingLeafSucceeds` | PASS | - | PASS - | - | 1.3 | 1.85 |
|  | `DuplicateLockReplayTest.test_D5_DUP_secondDepositSucceeds` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_D5_SKIP_secondDepositSucceeds` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_D5_mutants_tripTokenReached` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_D5_stock_probeData` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_D5_stock_secondDepositReverts` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_acq_observation` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_callback_depositThenWithdraw` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_callback_withdrawThenDepositOrTransfer` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_direct_deposit` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_direct_transfer` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_direct_withdraw` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_static_withdrawBenign` | PASS | - | PASS - | - |  |  |
|  | `DuplicateLockReplayTest.test_X1_tripCex_reasonOnly` | PASS | - | PASS - | - |  |  |

### insert-callback

20 runs, 48 verdicts, run wall 1157 s, highest peak 3.09 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| probe-leaf-index | `check_PROBE_leafIndexSymbolic_expectFail` | FAIL | 2 | FAIL 2 | 0.13 | 4.9 | 1.12 |
| no-band | `check_D5a_depositLeafInTree_reverts` | PASS | 14 | PASS 14 | 0.83 | 6.9 | 1.00 |
|  | `check_T11a0_transferOut0InTree_reverts` | PASS | 24 | PASS 24 | 1.46 |  |  |
| withdraw-full | `check_X1_withdrawReentersDeposit` | PASS | 6 | PASS 6 | 1.02 | 7.9 | 1.00 |
|  | `check_X1_withdrawReentersTransfer` | PASS | 6 | PASS 6 | 0.66 |  |  |
|  | `check_X1_withdrawReentersWithdraw` | PASS | 6 | PASS 6 | 0.67 |  |  |
|  | `check_X2_withdrawSpentBeforeTokenCall` | PASS | 6 | PASS 6 | 0.83 |  |  |
| probe-new-leaf | `check_PROBE_depositNewLeafSucceeds_expectFail` | FAIL | 40 | FAIL 40 | 2.68 | 7.4 | 1.05 |
| band-deposit | `check_D5a_depositLeafInTree_reverts` | PASS | 14 | PASS 14 | 0.89 | 93.6 | 1.09 |
|  | `check_D5b_depositInsertsCommitment` | PASS | 154 | PASS 154 | 11.80 |  |  |
|  | `check_D5s_depositTwice_reverts` | PASS | 39 | PASS 39 | 5.50 |  |  |
|  | `check_X1_depositReentersDeposit` | PASS | 154 | PASS 154 | 15.61 |  |  |
|  | `check_X1_depositReentersTransfer` | PASS | 154 | PASS 154 | 16.14 |  |  |
|  | `check_X1_depositReentersWithdraw` | PASS | 154 | PASS 154 | 16.06 |  |  |
|  | `check_X2_depositTreeUpdatedBeforeTokenCall` | PASS | 154 | PASS 154 | 22.97 |  |  |
| band-transfer | `check_T11a0_transferOut0InTree_reverts` | PASS | 24 | PASS 24 | 1.93 | 85.1 | 1.00 |
|  | `check_T11a1_transferOut1InTree_reverts` | PASS | 312 | PASS 312 | 9.63 |  |  |
|  | `check_T11b_transferInsertsOutputsInOrder` | PASS | 304 | PASS 304-305 | 30.38 |  |  |
|  | `check_T11c_equalOutputs_reverts` | PASS | 156 | PASS 156 | 6.59 |  |  |
|  | `check_WIT_transferSucceeds_expectFail` | FAIL | 156 | FAIL 156 | 7.79 |  |  |
|  | `check_X1_transferNoTokenCall` | PASS | 304 | PASS 304 | 24.16 |  |  |
| mutant-DUP-deposit | `check_D5a_depositLeafInTree_reverts` | FAIL | 162 | FAIL 162 | 10.56 | 25.9 | 1.13 |
|  | `check_D5s_depositTwice_reverts` | FAIL | 78 | FAIL 77 (differs) | 10.56 |  |  |
| mutant-DUP-transfer | `check_T11a0_transferOut0InTree_reverts` | FAIL | 472 | FAIL 472 | 28.64 | 82.0 | 1.01 |
|  | `check_T11a1_transferOut1InTree_reverts` | FAIL | 464 | FAIL 464 | 27.06 |  |  |
|  | `check_T11c_equalOutputs_reverts` | FAIL | 309 | FAIL 309 | 21.16 |  |  |
| mutant-INS_D | `check_D5b_depositInsertsCommitment` | FAIL | 306 | FAIL 307-310 (differs) | 14.28 | 18.7 | 1.02 |
| mutant-SWAP_T | `check_T11b_transferInsertsOutputsInOrder` | FAIL | 306 | FAIL 304 (differs) | 29.54 | 34.3 | 1.01 |
| mutant-NR_D | `check_X1_depositReentersDeposit` | FAIL | 1066 | FAIL 1066 | 82.81 | 100.9 | 1.19 |
|  | `check_X1_withdrawReentersDeposit` | FAIL | 174 | FAIL 174 | 13.34 |  |  |
| mutant-NR_T | `check_X1_depositReentersTransfer` | FAIL | 3932 | FAIL 3922-3923 (differs) | 350.51 | 446.3 | 3.09 |
|  | `check_X1_withdrawReentersTransfer` | FAIL | 702 | FAIL 680-681 (differs) | 89.19 |  |  |
| mutant-NR_W | `check_X1_depositReentersWithdraw` | FAIL | 1644 | FAIL 1642 (differs) | 129.83 | 142.5 | 1.42 |
|  | `check_X1_withdrawReentersWithdraw` | FAIL | 44 | FAIL 44 | 2.79 |  |  |
| mutant-ORD_D | `check_X2_depositTreeUpdatedBeforeTokenCall` | FAIL | 155 | FAIL 154 (differs) | 11.89 | 17.1 | 1.14 |
| mutant-ORD_W | `check_X2_withdrawSpentBeforeTokenCall` | FAIL | 10 | FAIL 6 (differs) | 0.97 | 5.8 | 1.13 |
| core-withdraw | `check_X1core_withdrawReentersDeposit` | PASS | 6 | PASS ? | 1.01 | 7.1 | 1.06 |
|  | `check_X1core_withdrawReentersTransfer` | PASS | 6 | PASS ? | 0.64 |  |  |
|  | `check_X1core_withdrawReentersWithdraw` | PASS | 6 | PASS ? | 0.65 |  |  |
| core-deposit | `check_X1core_depositReentersDeposit` | PASS | 154 | PASS ? | 14.49 | 48.6 | 1.14 |
|  | `check_X1core_depositReentersTransfer` | PASS | 154 | PASS ? | 14.87 |  |  |
|  | `check_X1core_depositReentersWithdraw` | PASS | 154 | PASS ? | 14.47 |  |  |
| core-mutant-NR_D | `check_X1core_depositReentersDeposit` | FAIL | 14 | FAIL ? | 1.38 | 7.2 | 1.14 |
|  | `check_X1core_withdrawReentersDeposit` | FAIL | 10 | FAIL ? | 1.05 |  |  |
| core-mutant-NR_T | `check_X1core_depositReentersTransfer` | FAIL | 21 | FAIL ? | 1.78 | 8.3 | 1.01 |
|  | `check_X1core_withdrawReentersTransfer` | FAIL | 22 | FAIL ? | 1.73 |  |  |
| core-mutant-NR_W | `check_X1core_depositReentersWithdraw` | FAIL | 12 | FAIL ? | 0.96 | 6.5 | 1.02 |
|  | `check_X1core_withdrawReentersWithdraw` | FAIL | 10 | FAIL ? | 0.84 |  |  |

### owner-payout

28 runs, 52 verdicts, run wall 391 s, highest peak 1.52 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| payout | `check_W10_withdrawPaysAndBindsInputs` | PASS | 14 | PASS 14 | 2.40 | 8.7 | 1.25 |
|  | `check_WIT_withdrawSucceeds_expectFail` | FAIL | 35 | FAIL 35 | 1.05 |  |  |
| probe | `check_PROBE_storageWritingVerifierNeverAccepts` | PASS | 15 | PASS 15 | 0.50 | 5.7 | 1.13 |
| owner-guard | `check_G1_addToken_nonOwnerReverts` | PASS | 3 | PASS 3 | 0.46 | 6.0 | 1.21 |
|  | `check_G1_removeToken_nonOwnerReverts` | PASS | 3 | PASS 3 | 0.04 |  |  |
|  | `check_G1_setRegistry_nonOwnerReverts` | PASS | 3 | PASS 3 | 0.04 |  |  |
|  | `check_G1_setVerifier_nonOwnerReverts` | PASS | 3 | PASS 3 | 0.04 |  |  |
|  | `check_G1_transferOwnership_nonOwnerReverts` | PASS | 3 | PASS 3 | 0.04 |  |  |
|  | `check_G1core_addToken_nonOwnerFails` | PASS | 3 | PASS 3 | 0.05 |  |  |
|  | `check_G1core_removeToken_nonOwnerFails` | PASS | 3 | PASS 3 | 0.04 |  |  |
|  | `check_G1core_setRegistry_nonOwnerFails` | PASS | 3 | PASS 3 | 0.04 |  |  |
|  | `check_G1core_setVerifier_nonOwnerFails` | PASS | 3 | PASS 3 | 0.04 |  |  |
|  | `check_G1core_transferOwnership_nonOwnerFails` | PASS | 3 | PASS 3 | 0.04 |  |  |
| owner-effect | `check_G1_addToken_ownerEffect` | PASS | 8 | PASS 8 | 0.70 | 6.9 | 1.25 |
|  | `check_G1_removeToken_ownerEffect` | PASS | 7 | PASS 7 | 0.19 |  |  |
|  | `check_G1_setRegistry_ownerEffect` | PASS | 5 | PASS 5 | 0.16 |  |  |
|  | `check_G1_setVerifier_ownerEffect` | PASS | 5 | PASS 5 | 0.14 |  |  |
|  | `check_G1_transferOwnership_ownerEffect` | PASS | 5 | PASS 5 | 0.14 |  |  |
| sweep | `check_G1_sweep_nonOwnerKeepsAdminState` | PASS | 2480 | PASS 2479 (differs) | 133.88 | 199.6 | 1.13 |
|  | `check_WIT_sweepSomeCallSucceeds_expectFail` | FAIL | 2482 | FAIL 2478-2481 (differs) | 59.24 |  |  |
| mutant-PAY_SENDER | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 2.99 | 8.3 | 1.12 |
| mutant-PAY_AMT1 | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 14 | FAIL 14 | 2.10 | 7.4 | 1.11 |
| mutant-PAY_TOK | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 3.01 | 8.4 | 1.11 |
| mutant-PAY_TWICE | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 14 | FAIL 14 | 1.91 | 7.2 | 1.12 |
| mutant-PAY_RCP_HI | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 3.62 | 8.9 | 1.12 |
| mutant-PI_TOK | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 2.96 | 8.3 | 1.12 |
| mutant-PI_AMT | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 14 | FAIL 14 | 2.56 | 8.0 | 1.20 |
| mutant-PI_RCP | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 2.96 | 8.2 | 1.12 |
| mutant-PI_NUL_HI | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 4.26 | 9.6 | 1.25 |
| mutant-PI_TOK_HI | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 14 | FAIL 14 | 3.03 | 8.3 | 1.26 |
| mutant-PI_RCP_HI | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 4.62 | 10.1 | 1.25 |
| mutant-PI_ROOT_HI | `check_W10_withdrawPaysAndBindsInputs` | FAIL | 22 | FAIL 22 | 4.51 | 9.9 | 1.14 |
| mutant-OO_ADD | `check_G1_addToken_nonOwnerReverts` | FAIL | 5 | FAIL 5 | 0.58 | 6.1 | 1.25 |
|  | `check_G1core_addToken_nonOwnerFails` | FAIL | 5 | FAIL 5 | 0.16 |  |  |
| mutant-OO_REM | `check_G1_removeToken_nonOwnerReverts` | FAIL | 4 | FAIL 4 | 0.54 | 6.0 | 1.12 |
|  | `check_G1core_removeToken_nonOwnerFails` | FAIL | 4 | FAIL 4 | 0.15 |  |  |
| mutant-OO_SETV | `check_G1_setVerifier_nonOwnerReverts` | FAIL | 4 | FAIL 4 | 0.55 | 6.0 | 1.22 |
|  | `check_G1core_setVerifier_nonOwnerFails` | FAIL | 4 | FAIL 4 | 0.15 |  |  |
| mutant-OO_SETR | `check_G1_setRegistry_nonOwnerReverts` | FAIL | 4 | FAIL 4 | 0.55 | 6.0 | 1.12 |
|  | `check_G1core_setRegistry_nonOwnerFails` | FAIL | 4 | FAIL 4 | 0.15 |  |  |
| mutant-OO_OWN | `check_G1_transferOwnership_nonOwnerReverts` | FAIL | 4 | FAIL 4 | 0.55 | 6.0 | 1.12 |
|  | `check_G1core_transferOwnership_nonOwnerFails` | FAIL | 4 | FAIL 4 | 0.16 |  |  |
| mutant-EFF_ADD | `check_G1_addToken_ownerEffect` | FAIL | 9 | FAIL 9 | 0.73 | 6.0 | 1.12 |
| mutant-EFF_REM | `check_G1_removeToken_ownerEffect` | FAIL | 8 | FAIL 8 | 0.70 | 6.0 | 1.12 |
| mutant-EFF_SETV | `check_G1_setVerifier_ownerEffect` | FAIL | 6 | FAIL 6 | 0.56 | 5.9 | 1.22 |
| mutant-EFF_SETR | `check_G1_setRegistry_ownerEffect` | FAIL | 7 | FAIL 7 | 0.69 | 5.9 | 1.13 |
| mutant-EFF_OWN | `check_G1_transferOwnership_ownerEffect` | FAIL | 6 | FAIL 6 | 0.57 | 5.9 | 1.12 |
| events-fuzz | `OwnerEventsTest.testFuzz_addRemoveToken_emitTokenAddedRemoved` | PASS | - | PASS - | - | 1.5 | 1.52 |
|  | `OwnerEventsTest.testFuzz_nonOwner_reverts` | PASS | - | PASS - | - |  |  |
|  | `OwnerEventsTest.testFuzz_setRegistry_emitsRegistryUpdated` | PASS | - | PASS - | - |  |  |
|  | `OwnerEventsTest.testFuzz_setVerifier_emitsVerifierUpdated` | PASS | - | PASS - | - |  |  |
|  | `OwnerEventsTest.testFuzz_transferOwnership_emitsOwnershipTransferred` | PASS | - | PASS - | - |  |  |

### guards

45 runs, 95 verdicts, run wall 409 s, highest peak 1.26 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| probes | `check_PROBE_attestationRootNonCanonical_expectFail` | FAIL | 2 | FAIL 2 | 0.12 | 6.9 | 1.21 |
|  | `check_PROBE_constructorSlotsConcrete` | PASS | 1 | PASS 1 | 0.02 |  |  |
|  | `check_PROBE_currentRootArbitrary_expectFail` | FAIL | 2 | FAIL 2 | 0.13 |  |  |
|  | `check_PROBE_nullifierCanBeSpent_expectFail` | FAIL | 2 | FAIL 2 | 0.13 |  |  |
|  | `check_PROBE_nullifierCanBeUnspent_expectFail` | FAIL | 2 | FAIL 2 | 0.13 |  |  |
|  | `check_PROBE_nullifierKeysIndependent_expectFail` | FAIL | 3 | FAIL 3 | 0.14 |  |  |
|  | `check_PROBE_rootIndexArbitrary_expectFail` | FAIL | 2 | FAIL 2 | 0.12 |  |  |
|  | `check_PROBE_tokenCanBeSupported_expectFail` | FAIL | 3 | FAIL 3 | 0.13 |  |  |
|  | `check_PROBE_tokenCanBeUnsupported_expectFail` | FAIL | 3 | FAIL 3 | 0.13 |  |  |
|  | `check_PROBE_validRootCanBeFalse_expectFail` | FAIL | 2 | FAIL 2 | 0.13 |  |  |
|  | `check_PROBE_validRootCanBeTrue_expectFail` | FAIL | 2 | FAIL 2 | 0.47 |  |  |
| guards | `check_deposit_amountTooLarge` | PASS | 16 | PASS 16 | 0.82 | 29.3 | 1.23 |
|  | `check_deposit_nonCanonicalInput` | PASS | 76 | PASS 76 | 3.51 |  |  |
|  | `check_deposit_senderNotFundingAddress` | PASS | 28 | PASS 28 | 0.85 |  |  |
|  | `check_deposit_unsupportedToken` | PASS | 12 | PASS 12 | 0.24 |  |  |
|  | `check_deposit_zeroAmount` | PASS | 16 | PASS 16 | 0.38 |  |  |
|  | `check_deposit_zeroFundingAddress` | PASS | 22 | PASS 22 | 0.71 |  |  |
|  | `check_transfer_firstNullifierSpent` | PASS | 12 | PASS 12 | 0.76 |  |  |
|  | `check_transfer_identicalNullifiers` | PASS | 8 | PASS 8 | 0.18 |  |  |
|  | `check_transfer_nonCanonicalInput` | PASS | 132 | PASS 132 | 9.95 |  |  |
|  | `check_transfer_secondNullifierSpent` | PASS | 16 | PASS 16 | 0.62 |  |  |
|  | `check_transfer_unknownRoot` | PASS | 20 | PASS 20 | 1.06 |  |  |
|  | `check_withdraw_amountTooLarge` | PASS | 10 | PASS 10 | 0.21 |  |  |
|  | `check_withdraw_nonCanonicalInput` | PASS | 42 | PASS 42 | 2.63 |  |  |
|  | `check_withdraw_nullifierSpent` | PASS | 16 | PASS 16 | 0.52 |  |  |
|  | `check_withdraw_unknownRoot` | PASS | 18 | PASS 18 | 0.78 |  |  |
|  | `check_withdraw_unsupportedToken` | PASS | 8 | PASS 8 | 0.13 |  |  |
|  | `check_withdraw_zeroAmount` | PASS | 11 | PASS 10 (differs) | 0.21 |  |  |
|  | `check_withdraw_zeroRecipient` | PASS | 12 | PASS 12 | 0.35 |  |  |
| spent-sequence | `check_spent_withdrawThenReuseRejected` | PASS | 32 | PASS 32 | 4.99 | 10.2 | 1.25 |
| witnesses | `check_WIT_deposit_verifierReached_expectFail` | FAIL | 10 | FAIL 10 | 0.83 | 8.6 | 1.19 |
|  | `check_WIT_transfer_verifierReached_expectFail` | FAIL | 8 | FAIL 8 | 1.28 |  |  |
|  | `check_WIT_withdraw_poolStorageChanges_expectFail` | FAIL | 3 | FAIL 3 | 0.26 |  |  |
|  | `check_WIT_withdraw_stateChanges_expectFail` | FAIL | 3 | FAIL 3 | 0.27 |  |  |
|  | `check_WIT_withdraw_tokenMoves_expectFail` | FAIL | 3 | FAIL 3 | 0.28 |  |  |
|  | `check_WIT_withdraw_verifierReached_expectFail` | FAIL | 8 | FAIL 8 | 0.40 |  |  |
| core | `check_core_deposit_amountTooLarge` | PASS | 16 | PASS 16 | 0.74 | 23.9 | 1.19 |
|  | `check_core_deposit_nonCanonicalInput` | PASS | 76 | PASS 76 | 2.43 |  |  |
|  | `check_core_deposit_senderNotFundingAddress` | PASS | 28 | PASS 28 | 1.15 |  |  |
|  | `check_core_deposit_unsupportedToken` | PASS | 12 | PASS 12 | 0.27 |  |  |
|  | `check_core_deposit_zeroAmount` | PASS | 16 | PASS 16 | 0.40 |  |  |
|  | `check_core_deposit_zeroFundingAddress` | PASS | 22 | PASS 22 | 0.61 |  |  |
|  | `check_core_deposit_zeroFundingAddress_nonzeroCaller` | PASS | 22 | PASS 22 | 0.65 |  |  |
|  | `check_core_transfer_firstNullifierSpent` | PASS | 12 | PASS 12 | 0.41 |  |  |
|  | `check_core_transfer_identicalNullifiers` | PASS | 8 | PASS 8 | 0.23 |  |  |
|  | `check_core_transfer_nonCanonicalInput` | PASS | 132 | PASS 132 | 6.76 |  |  |
|  | `check_core_transfer_secondNullifierSpent` | PASS | 16 | PASS 16 | 0.51 |  |  |
|  | `check_core_transfer_unknownRoot` | PASS | 20 | PASS 20 | 0.79 |  |  |
|  | `check_core_withdraw_amountTooLarge` | PASS | 10 | PASS 10 | 0.17 |  |  |
|  | `check_core_withdraw_nonCanonicalInput` | PASS | 42 | PASS 42 | 1.61 |  |  |
|  | `check_core_withdraw_nullifierSpent` | PASS | 16 | PASS 16 | 0.41 |  |  |
|  | `check_core_withdraw_unknownRoot` | PASS | 18 | PASS 18 | 0.93 |  |  |
|  | `check_core_withdraw_unsupportedToken` | PASS | 8 | PASS 8 | 0.12 |  |  |
|  | `check_core_withdraw_zeroAmount` | PASS | 10 | PASS 10 | 0.16 |  |  |
|  | `check_core_withdraw_zeroRecipient` | PASS | 12 | PASS 12 | 0.26 |  |  |
| mutant-DEP_TOKEN | `check_deposit_unsupportedToken` | FAIL | 38 | FAIL 38 | 1.73 | 6.9 | 1.17 |
| mutant-DEP_AMOUNT_ZERO | `check_deposit_zeroAmount` | FAIL | 34 | FAIL 34 | 1.64 | 6.7 | 1.12 |
| mutant-DEP_AMOUNT_MAX | `check_deposit_amountTooLarge` | FAIL | 38 | FAIL 38 | 1.94 | 7.0 | 1.26 |
| mutant-DEP_FUNDER_ZERO | `check_deposit_zeroFundingAddress` | FAIL | 36 | FAIL 36 | 1.84 | 7.0 | 1.15 |
| mutant-DEP_FUNDER_CALLER | `check_deposit_senderNotFundingAddress` | FAIL | 38 | FAIL 38 | 1.84 | 7.0 | 1.15 |
| mutant-DEP_CANONICAL | `check_deposit_nonCanonicalInput` | FAIL | 76 | FAIL 76 | 3.25 | 8.3 | 1.26 |
| mutant-TR_DISTINCT | `check_transfer_identicalNullifiers` | FAIL | 56 | FAIL 56 | 3.23 | 8.4 | 1.13 |
| mutant-TR_SPENT0 | `check_transfer_firstNullifierSpent` | FAIL | 68 | FAIL 68 | 3.66 | 8.9 | 1.13 |
| mutant-TR_SPENT1 | `check_transfer_secondNullifierSpent` | FAIL | 68 | FAIL 68 | 4.82 | 10.1 | 1.13 |
| mutant-TR_ROOT | `check_transfer_unknownRoot` | FAIL | 42 | FAIL 42 | 2.64 | 7.8 | 1.12 |
| mutant-TR_CANONICAL | `check_transfer_nonCanonicalInput` | FAIL | 132 | FAIL 132 | 6.48 | 11.6 | 1.13 |
| mutant-WD_TOKEN | `check_withdraw_unsupportedToken` | FAIL | 28 | FAIL 28 | 1.47 | 6.6 | 1.14 |
| mutant-WD_AMOUNT_ZERO | `check_withdraw_zeroAmount` | FAIL | 26 | FAIL 26 | 1.45 | 6.6 | 1.13 |
| mutant-WD_AMOUNT_MAX | `check_withdraw_amountTooLarge` | FAIL | 30 | FAIL 30 | 1.79 | 6.9 | 1.12 |
| mutant-WD_RECIPIENT_ZERO | `check_withdraw_zeroRecipient` | FAIL | 26 | FAIL 26 | 1.68 | 6.9 | 1.14 |
| mutant-WD_SPENT | `check_withdraw_nullifierSpent` | FAIL | 28 | FAIL 28 | 1.62 | 6.9 | 1.12 |
| mutant-WD_ROOT | `check_withdraw_unknownRoot` | FAIL | 22 | FAIL 22 | 1.48 | 6.7 | 1.12 |
| mutant-WD_CANONICAL | `check_withdraw_nonCanonicalInput` | FAIL | 42 | FAIL 42 | 2.15 | 7.4 | 1.12 |
| core-mutant-DEP_TOKEN | `check_core_deposit_unsupportedToken` | FAIL | 38 | FAIL 38 | 1.58 | 6.9 | 1.12 |
| core-mutant-DEP_AMOUNT_ZERO | `check_core_deposit_zeroAmount` | FAIL | 34 | FAIL 34 | 1.40 | 6.8 | 1.12 |
| core-mutant-DEP_AMOUNT_MAX | `check_core_deposit_amountTooLarge` | FAIL | 38 | FAIL 38 | 1.65 | 6.9 | 1.15 |
| core-mutant-DEP_FUNDER_ZERO | `check_core_deposit_zeroFundingAddress` | FAIL | 36 | FAIL 36 | 1.66 | 7.1 | 1.19 |
| core-mutant-DEP_FUNDER_CALLER | `check_core_deposit_senderNotFundingAddress` | FAIL | 38 | FAIL 38 | 1.64 | 7.1 | 1.12 |
| core-mutant-DEP_CANONICAL | `check_core_deposit_nonCanonicalInput` | FAIL | 76 | FAIL 76 | 2.90 | 8.4 | 1.13 |
| core-mutant-TR_DISTINCT | `check_core_transfer_identicalNullifiers` | FAIL | 56 | FAIL 56 | 2.72 | 8.1 | 1.13 |
| core-mutant-TR_SPENT0 | `check_core_transfer_firstNullifierSpent` | FAIL | 68 | FAIL 68 | 3.34 | 8.8 | 1.12 |
| core-mutant-TR_SPENT1 | `check_core_transfer_secondNullifierSpent` | FAIL | 68 | FAIL 68 | 3.25 | 8.7 | 1.12 |
| core-mutant-TR_ROOT | `check_core_transfer_unknownRoot` | FAIL | 42 | FAIL 42 | 2.10 | 7.4 | 1.12 |
| core-mutant-TR_CANONICAL | `check_core_transfer_nonCanonicalInput` | FAIL | 133 | FAIL 132 (differs) | 5.56 | 10.9 | 1.12 |
| core-mutant-WD_TOKEN | `check_core_withdraw_unsupportedToken` | FAIL | 28 | FAIL 28 | 1.37 | 6.7 | 1.12 |
| core-mutant-WD_AMOUNT_ZERO | `check_core_withdraw_zeroAmount` | FAIL | 26 | FAIL 26 | 1.22 | 6.3 | 1.12 |
| core-mutant-WD_AMOUNT_MAX | `check_core_withdraw_amountTooLarge` | FAIL | 30 | FAIL 30 | 1.46 | 6.6 | 1.12 |
| core-mutant-WD_RECIPIENT_ZERO | `check_core_withdraw_zeroRecipient` | FAIL | 26 | FAIL 26 | 1.32 | 6.4 | 1.12 |
| core-mutant-WD_SPENT | `check_core_withdraw_nullifierSpent` | FAIL | 28 | FAIL 28 | 1.38 | 6.6 | 1.12 |
| core-mutant-WD_ROOT | `check_core_withdraw_unknownRoot` | FAIL | 22 | FAIL 22 | 1.15 | 6.2 | 1.12 |
| core-mutant-WD_CANONICAL | `check_core_withdraw_nonCanonicalInput` | FAIL | 42 | FAIL 42 | 1.70 | 6.8 | 1.15 |
| core-mutant-DEP_FUNDER_ZERO-nonzero-caller | `check_core_deposit_zeroFundingAddress_nonzeroCaller` | PASS | 22 | PASS 22 | 0.96 | 6.2 | 1.12 |
| spent-mutant-WD_SPENT | `check_spent_withdrawThenReuseRejected` | FAIL | 45 | FAIL 45 | 6.53 | 11.8 | 1.13 |
| spent-mutant-TR_SPENT0 | `check_spent_withdrawThenReuseRejected` | FAIL | 127 | FAIL 127 | 19.52 | 24.6 | 1.12 |
| spent-mutant-TR_SPENT1 | `check_spent_withdrawThenReuseRejected` | FAIL | 127 | FAIL 127 | 12.33 | 17.4 | 1.12 |

### ring-funding

13 runs, 15 verdicts, run wall 210 s, highest peak 1.27 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| ring-deposit | `check_FRW_deposit_index` | PASS | 173 | PASS 174-175 (differs) | 12.80 | 18.6 | 1.13 |
| ring-transfer | `check_FRW_transfer_index` | PASS | 689 | PASS 681 (differs) | 53.99 | 59.8 | 1.11 |
| ring-witnesses | `check_FRW_W_deposit_expectFail` | FAIL | 19 | FAIL 20 (differs) | 0.99 | 8.4 | 1.09 |
|  | `check_FRW_W_transfer_expectFail` | FAIL | 24 | FAIL 24-25 | 1.35 |  |  |
| deposit-order | `check_X2_depositTreeUpdatedBeforeTokenCall` | PASS | 156 | PASS 154 (differs) | 36.04 | 41.2 | 1.09 |
| funding-call | `check_D6_successBinding` | PASS | 154 | PASS 154 | 25.40 | 30.5 | 1.10 |
| mutant-D6 | `check_D6_successBinding` | FAIL | 6 | FAIL 6 | 1.09 | 6.1 | 1.11 |
| mutant-D6_CALLER | `check_D6_successBinding` | FAIL | 6 | FAIL 6 | 1.09 | 6.2 | 1.12 |
| mutant-ORD_D | `check_X2_depositTreeUpdatedBeforeTokenCall` | FAIL | 6 | FAIL 6 | 1.19 | 6.3 | 1.09 |
| funding-witness | `check_D6_successWitness_expectFail` | FAIL | 7 | FAIL 8 (differs) | 1.04 | 6.1 | 1.09 |
| reached-roots | `check_RW_postOpRootsOnly` | PASS | 6 | PASS 7-8 (differs) | 0.18 | 6.4 | 1.09 |
| mutant-M1 | `check_FRW_transfer_index` | FAIL | 12 | FAIL 12-13 | 1.15 | 7.0 | 1.27 |
| mutant-M2 | `check_FRW_deposit_index` | FAIL | 6 | FAIL 6 | 0.77 | 7.6 | 1.24 |
|  | `check_FRW_transfer_index` | FAIL | 10 | FAIL 10 | 0.91 |  |  |
| mutant-M3 | `check_RW_postOpRootsOnly` | FAIL | 5 | FAIL 4-5 | 0.26 | 6.3 | 1.22 |

### post-deposit-withdraw

30 runs, 30 verdicts, run wall 809 s, highest peak 1.05 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| D_amount_ne_zero | `check_D_amount_ne_zero` | PASS | 403 | PASS 400 (differs) | 18.11 | 22.7 | 1.05 |
| D_fresh_leaf | `check_D_fresh_leaf` | PASS | 400 | PASS 400 | 16.40 | 20.4 | 0.97 |
| D_guarded | `check_D_guarded` | PASS | 5736 | PASS 5736 | 262.11 | 265.9 | 0.97 |
| D_post | `check_D_post` | PASS | 5959 | PASS 5957-5974 | 162.77 | 168.0 | 1.03 |
| D_supported | `check_D_supported` | PASS | 400 | PASS 400-401 | 15.63 | 19.4 | 1.01 |
| D_token_calls | `check_D_token_calls` | PASS | 400 | PASS 400 | 31.51 | 35.1 | 0.98 |
| D_verified | `check_D_verified` | PASS | 407 | PASS 405-410 | 94.14 | 97.8 | 1.01 |
| D_witness | `check_D_witness` | FAIL | 400 | FAIL 400-407 | 23.03 | 27.0 | 0.99 |
| mutant-D_amount_ne_zero | `check_D_amount_ne_zero` | FAIL | 16 | FAIL 20-21 (differs) | 0.57 | 4.0 | 1.00 |
| mutant-D_fresh_leaf | `check_D_fresh_leaf` | FAIL | 20 | FAIL 22 (differs) | 0.74 | 4.2 | 1.05 |
| mutant-D_guarded | `check_D_guarded` | FAIL | 37 | FAIL 37 | 1.46 | 5.2 | 1.04 |
| mutant-D_post | `check_D_post` | FAIL | 530 | FAIL 529 (differs) | 16.08 | 20.1 | 0.99 |
| mutant-D_supported | `check_D_supported` | FAIL | 20 | FAIL 20-22 | 0.91 | 4.9 | 0.98 |
| mutant-D_token_calls | `check_D_token_calls` | FAIL | 19 | FAIL 17 (differs) | 0.82 | 4.7 | 0.98 |
| mutant-D_verified | `check_D_verified` | FAIL | 17 | FAIL 16 (differs) | 1.31 | 5.3 | 1.02 |
| mutant-W_amount_ne_zero | `check_W_amount_ne_zero` | FAIL | 13 | FAIL 13 | 0.18 | 4.1 | 0.98 |
| mutant-W_guarded | `check_W_guarded` | FAIL | 24 | FAIL 24 | 0.96 | 4.9 | 0.98 |
| mutant-W_known_root | `check_W_known_root` | FAIL | 16 | FAIL 15-16 | 0.21 | 4.2 | 0.97 |
| mutant-W_post | `check_W_post` | FAIL | 33 | FAIL 32-33 | 0.77 | 4.7 | 0.99 |
| mutant-W_token_calls | `check_W_token_calls` | FAIL | 14 | FAIL 13-14 | 0.23 | 4.2 | 0.97 |
| mutant-W_unspent | `check_W_unspent` | FAIL | 13 | FAIL 13 | 0.19 | 4.2 | 0.98 |
| mutant-W_verified | `check_W_verified` | FAIL | 13 | FAIL 13-14 | 0.90 | 4.9 | 0.99 |
| W_amount_ne_zero | `check_W_amount_ne_zero` | PASS | 124 | PASS 124 | 1.73 | 5.7 | 0.99 |
| W_guarded | `check_W_guarded` | PASS | 588 | PASS 588 | 16.63 | 20.6 | 1.00 |
| W_known_root | `check_W_known_root` | PASS | 164 | PASS 164 | 2.21 | 6.2 | 0.97 |
| W_post | `check_W_post` | PASS | 284 | PASS 284 | 4.52 | 8.4 | 0.98 |
| W_token_calls | `check_W_token_calls` | PASS | 124 | PASS 124 | 2.26 | 6.2 | 1.00 |
| W_unspent | `check_W_unspent` | PASS | 124 | PASS 124 | 1.81 | 5.8 | 0.98 |
| W_verified | `check_W_verified` | PASS | 124 | PASS 124-131 | 9.54 | 13.6 | 1.00 |
| W_witness | `check_W_witness` | FAIL | 124 | FAIL 124 | 2.01 | 6.2 | 0.97 |

### post-transfer-admin

37 runs, 37 verdicts, run wall 841 s, highest peak 1.02 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| A_add | `check_A_add` | PASS | 15 | PASS 15 | 0.23 | 4.5 | 1.01 |
| A_add_witness | `check_A_add_witness` | FAIL | 9 | FAIL 9 | 0.19 | 4.5 | 1.01 |
| A_owner | `check_A_owner` | PASS | 11 | PASS 11 | 0.21 | 4.4 | 0.98 |
| A_owner_witness | `check_A_owner_witness` | FAIL | 7 | FAIL 7 | 0.15 | 4.5 | 0.98 |
| A_registry | `check_A_registry` | PASS | 11 | PASS 10 (differs) | 0.32 | 4.8 | 0.98 |
| A_registry_witness | `check_A_registry_witness` | FAIL | 7 | FAIL 7 | 0.16 | 4.7 | 0.98 |
| A_remove | `check_A_remove` | PASS | 13 | PASS 13 | 0.23 | 4.7 | 0.98 |
| A_remove_witness | `check_A_remove_witness` | FAIL | 8 | FAIL 8 | 0.18 | 4.7 | 0.98 |
| mutant-A_add | `check_A_add` | FAIL | 8 | FAIL 8 | 0.18 | 4.6 | 0.98 |
| mutant-A_owner | `check_A_owner` | FAIL | 11 | FAIL 11 | 0.21 | 4.7 | 0.99 |
| mutant-A_registry | `check_A_registry` | FAIL | 11 | FAIL 11 | 0.22 | 4.7 | 1.00 |
| mutant-A_remove | `check_A_remove` | FAIL | 12 | FAIL 12 | 0.25 | 4.9 | 0.98 |
| mutant-T_distinct | `check_T_distinct` | FAIL | 29 | FAIL 29-31 | 1.31 | 5.9 | 0.98 |
| mutant-T_fresh_outputs | `check_T_fresh_outputs` | FAIL | 33 | FAIL 33-34 | 1.28 | 5.9 | 0.98 |
| mutant-T_known_root | `check_T_known_root` | FAIL | 29 | FAIL 30 (differs) | 1.34 | 5.9 | 0.98 |
| mutant-T_no_effects | `check_T_no_effects` | FAIL | 21 | FAIL 22 (differs) | 1.39 | 6.0 | 0.98 |
| mutant-T_post | `check_T_post` | FAIL | 1571 | FAIL 1499-1579 | 57.40 | 62.2 | 0.98 |
| mutant-T_post_mapping | `check_T_post` | FAIL | 56 | FAIL 50-52 (differs) | 2.05 | 6.6 | 0.98 |
| mutant-T_post_order | `check_T_post` | FAIL | 33 | FAIL 29 (differs) | 1.38 | 5.9 | 0.99 |
| mutant-T_unspent | `check_T_unspent` | FAIL | 29 | FAIL 29 | 1.33 | 5.8 | 0.98 |
| mutant-T_verified_canonical | `check_T_verified` | FAIL | 21 | FAIL 20 (differs) | 1.97 | 6.4 | 0.98 |
| mutant-T_verified | `check_T_verified` | FAIL | 24 | FAIL 22-23 (differs) | 1.94 | 6.4 | 0.98 |
| mutant-T_verified_root | `check_T_verified` | FAIL | 22 | FAIL 21 (differs) | 2.25 | 6.7 | 0.98 |
| T_distinct | `check_T_distinct` | PASS | 696 | PASS 696-697 | 27.82 | 32.3 | 0.98 |
| T_distinct_witness | `check_T_distinct_witness` | FAIL | 27 | FAIL 26-27 | 1.32 | 5.8 | 0.97 |
| T_fresh_outputs | `check_T_fresh_outputs` | PASS | 1305 | PASS 1307-1312 (differs) | 43.34 | 48.7 | 0.98 |
| T_fresh_outputs_witness | `check_T_fresh_outputs_witness` | FAIL | 30 | FAIL 31-32 (differs) | 1.25 | 5.5 | 0.98 |
| T_known_root | `check_T_known_root` | PASS | 708 | PASS 708 | 25.89 | 30.0 | 0.98 |
| T_known_root_witness | `check_T_known_root_witness` | FAIL | 27 | FAIL 27 | 1.22 | 5.2 | 0.98 |
| T_no_effects | `check_T_no_effects` | PASS | 696 | PASS 696-697 | 36.33 | 40.4 | 0.98 |
| T_no_effects_witness | `check_T_no_effects_witness` | FAIL | 24 | FAIL 24 | 1.22 | 5.4 | 0.98 |
| T_post | `check_T_post` | PASS | 8135 | PASS 8181-8196 (differs) | 302.85 | 308.8 | 1.02 |
| T_post_witness | `check_T_post_witness` | FAIL | 32 | FAIL 26-28 (differs) | 1.54 | 6.2 | 0.99 |
| T_unspent | `check_T_unspent` | PASS | 696 | PASS 696-697 | 29.28 | 33.8 | 0.98 |
| T_unspent_witness | `check_T_unspent_witness` | FAIL | 26 | FAIL 26 | 1.28 | 5.8 | 0.98 |
| T_verified | `check_T_verified` | PASS | 697 | PASS 697 | 123.09 | 127.5 | 0.98 |
| T_verified_witness | `check_T_verified_witness` | FAIL | 18 | FAIL 21 (differs) | 1.93 | 6.2 | 0.99 |

### root-window

15 runs, 61 verdicts, run wall 512 s, highest peak 2.44 GiB.

| Run | Check | Verdict | Paths | Expected | Halmos s | Run wall s | Peak GiB |
|---|---|---|---|---|---|---|---|
| reached | `check_P1_nullifierMonotone_symStorage_withdraw` | PASS | 15 | PASS 15 | 0.43 | 11.5 | 0.96 |
|  | `check_P2_transferSpentReverts` | PASS | 5 | PASS 5 | 0.10 |  |  |
|  | `check_P2_transferSpentReverts_symStorage` | PASS | 4 | PASS 4 | 0.09 |  |  |
|  | `check_P2_withdrawSpentReverts` | PASS | 5 | PASS 5 | 0.07 |  |  |
|  | `check_P2_withdrawSpentReverts_symStorage` | PASS | 5 | PASS 5 | 0.07 |  |  |
|  | `check_P2_withdrawTwiceSecondReverts` | PASS | 2 | PASS 2 | 0.14 |  |  |
|  | `check_P3_spentBeforePay` | PASS | 7 | PASS 7 | 0.15 |  |  |
|  | `check_P3b_freshReentryFails` | PASS | 8 | PASS 9 (differs) | 0.44 |  |  |
|  | `check_P3b_freshReentryGuardError` | PASS | 9 | PASS 8 (differs) | 0.80 |  |  |
|  | `check_P3b_noGuard_freshReentryFails_expectFail` | FAIL | 11 | FAIL 11 | 0.66 |  |  |
|  | `check_P3b_replayMatchesSetUp` | PASS | 1 | PASS 1 | 1.62 |  |  |
|  | `check_P4_knownRootsOnly_reached` | PASS | 5 | PASS 4 (differs) | 0.09 |  |  |
|  | `check_P4_zeroRootNotKnownAfterInsert` | PASS | 1 | PASS 1 | 0.01 |  |  |
|  | `check_P4v1_postTxRootsOnly` | PASS | 8 | PASS 5 (differs) | 0.14 |  |  |
|  | `check_W_P1_transferSucceeds_expectFail` | FAIL | 12 | FAIL 12 | 0.50 |  |  |
|  | `check_W_P2_firstWithdrawReachable_expectFail` | FAIL | 9 | FAIL 8 (differs) | 0.23 |  |  |
|  | `check_W_P3_withdrawSuccessReachable_expectFail` | FAIL | 7 | FAIL 7 | 0.25 |  |  |
|  | `check_W_P3b_withdrawSuccessReachable_expectFail` | FAIL | 7 | FAIL 8 (differs) | 0.87 |  |  |
| probes | `check_F40PROBE_nullifierSymbolic_expectFail` | FAIL | 2 | FAIL 2 | 0.16 | 5.6 | 0.96 |
|  | `check_F40PROBE_ownerSymbolic_expectFail` | FAIL | 3 | FAIL 3 | 0.16 |  |  |
|  | `check_F40PROBE_sizeSymbolic_expectFail` | FAIL | 2 | FAIL 2 | 0.15 |  |  |
|  | `check_F40PROBE_supportedTokenSymbolic_expectFail` | FAIL | 2 | FAIL 2 | 0.15 |  |  |
|  | `check_F40PROBE_validRootSymbolic_expectFail` | FAIL | 2 | FAIL 2 | 0.17 |  |  |
|  | `check_PROBE_ownerSymbolic_expectFail` | PASS | 1 | PASS 1 | 0.02 |  |  |
|  | `check_PROBE_sizeSymbolic_expectFail` | PASS | 1 | PASS 1 | 0.02 |  |  |
|  | `check_PROBE_spentNullifierSymbolic_expectFail` | PASS | 1 | PASS 1 | 0.02 |  |  |
|  | `check_PROBE_supportedTokenSymbolic_expectFail` | PASS | 1 | PASS 1 | 0.02 |  |  |
| fresh-depth40 | `check_F40_P1_addSupportedToken` | PASS | 5 | PASS 5 | 0.13 | 7.7 | 0.95 |
|  | `check_F40_P1_removeSupportedToken` | PASS | 4 | PASS 4 | 0.10 |  |  |
|  | `check_F40_P1_setAttestationRegistry` | PASS | 4 | PASS 4 | 0.09 |  |  |
|  | `check_F40_P1_setVerifier` | PASS | 4 | PASS 4 | 0.09 |  |  |
|  | `check_F40_P1_transferOwnership` | PASS | 4 | PASS 4 | 0.10 |  |  |
|  | `check_F40_P1_withdraw` | PASS | 17 | PASS 17 | 0.52 |  |  |
|  | `check_F40_P5_addSupportedToken` | PASS | 5 | PASS 5 | 0.09 |  |  |
|  | `check_F40_P5_removeSupportedToken` | PASS | 4 | PASS 4 | 0.08 |  |  |
|  | `check_F40_P5_setAttestationRegistry` | PASS | 4 | PASS 4 | 0.08 |  |  |
|  | `check_F40_P5_setVerifier` | PASS | 4 | PASS 4 | 0.08 |  |  |
|  | `check_F40_P5_transferOwnership` | PASS | 4 | PASS 4 | 0.08 |  |  |
|  | `check_F40_P5_withdraw` | PASS | 16 | PASS 15 (differs) | 0.31 |  |  |
|  | `check_F40_W_addSupportedToken_expectFail` | FAIL | 5 | FAIL 5 | 0.11 |  |  |
|  | `check_F40_W_removeSupportedToken_expectFail` | FAIL | 4 | FAIL 4 | 0.09 |  |  |
|  | `check_F40_W_setAttestationRegistry_expectFail` | FAIL | 4 | FAIL 4 | 0.09 |  |  |
|  | `check_F40_W_setVerifier_expectFail` | FAIL | 4 | FAIL 4 | 0.09 |  |  |
|  | `check_F40_W_transferOwnership_expectFail` | FAIL | 4 | FAIL 4 | 0.09 |  |  |
|  | `check_F40_W_withdraw_expectFail` | FAIL | 16 | FAIL 15 (differs) | 0.68 |  |  |
| depth-cap | `check_R256_deposit` | PASS | 8 | PASS 8 | 0.17 | 5.7 | 0.96 |
|  | `check_R256_transfer` | PASS | 22 | PASS 22 | 0.29 |  |  |
|  | `check_R256i_deposit` | PASS | 9 | PASS 8 (differs) | 0.18 |  |  |
|  | `check_R256i_transfer` | PASS | 22 | PASS 22 | 0.30 |  |  |
| cap-witness-deposit-255 | `check_RWc_deposit_expectFail` | FAIL | 11 | FAIL 10 (differs) | 2.81 | 7.6 | 0.95 |
| cap-witness-deposit-64 | `check_RWc_deposit_expectFail` | FAIL | 13 | FAIL 10 (differs) | 0.78 | 5.6 | 0.96 |
| cap-witness-transfer-64 | `check_RWc_transfer_expectFail` | FAIL | 26 | FAIL 26 | 2.26 | 7.1 | 0.96 |
| cap-witness-transfer-255 | `check_RWc_transfer_expectFail` | FAIL | 26 | FAIL 26 | 11.09 | 16.1 | 2.44 |
| band8-P5-deposit | `check_B_P5_deposit` | PASS | 4101 | PASS 4095 (differs) | 129.14 | 136.2 | 1.06 |
| band8-P1-deposit | `check_B_P1_deposit` | PASS | 3069 | PASS 3067 (differs) | 118.33 | 123.4 | 0.96 |
| band8-witness-deposit | `check_B_W_deposit_expectFail` | FAIL | 1553 | FAIL 1554 (differs) | 66.26 | 72.9 | 1.32 |
| band4-P5-transfer | `check_B_P5_transfer` | PASS | 810 | PASS 792 (differs) | 33.63 | 39.2 | 0.96 |
| band4-P1-transfer | `check_B_P1_transfer` | PASS | 907 | PASS 912 (differs) | 40.62 | 46.4 | 0.95 |
| band4-witness-transfer | `check_B_W_transfer_expectFail` | FAIL | 309 | FAIL 309 | 20.23 | 25.6 | 0.95 |
| replay | `P3bConcreteReplay.test_guarded_sameInputs_freshReentryBlockedByGuard` | PASS | - | PASS - | - | 1.3 | 1.63 |
|  | `P3bConcreteReplay.test_noGuard_cex_freshReentrySucceeds` | PASS | - | PASS - | - |  |  |
