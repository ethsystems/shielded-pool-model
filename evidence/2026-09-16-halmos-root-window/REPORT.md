> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-09-16.
> Sanitised for publication: see [../README.md](../README.md).

# REPORT: contract layer trial with Halmos

Worker: Claude Opus 5, 2026-09-16. Start 19:00:10, end 19:47 (47 minutes).
Budget 60 minutes. Work dir: a local cache directory (not copied here).

Input: the private implementation repository at `94e30f3f0b9fb4a3ba0d0a3b220c49c075c42672`,
before the fix in its PR #12
(only an untracked `.claude/`). `ShieldedPool.sol` is 383 lines, read in full.

## Summary

- Halmos 0.3.3 runs on the real `ShieldedPool.sol`. It needed one work-around
  for linked libraries (see Setup).
- **P2 (no double spend) and P3 (spend before pay): PASS.** For P2, withdraw
  and transfer also pass from **arbitrary pool storage**. That is a one-step
  proof over all states, not only reachable ones.
- **P1 (nullifier set only grows): PASS for withdraw from arbitrary storage.**
  Transfer, deposit and "any call": **OUT OF REACH** at `--loop 8`. The
  transfer and deposit checks passed 12 GB in under 80 s.
- **P4 (known roots only): PASS in the prefix-root form. The first form FAILED
  with a real counterexample.** It shows two places where the contract's root
  window differs from the Lean model. This is the main finding (see P4).
- **P5 (tree size never decreases): OUT OF REACH** (any-call form timed out).
- Every PASS line shows `bounds: []`: no loop unrolling bound was hit, so no path
  was cut. The results are still limited by the concrete setup (see Scope).

## Setup and costs

| Step | Wall time | Size |
|---|---|---|
| `python3 -m venv .venv && .venv/bin/pip install halmos` (Python 3.14.7) | 588 s | venv 117 MB |
| Copy Foundry project (`foundry.toml`, `contracts/`, `dependencies/`) | under 1 s | 10 MB |
| `forge build --ast --force` (solc 0.8.33, forge 1.5.1) | about 15 s | |
| Fast Halmos batch (9 checks) | 22 s incl. build, 2.8 s symbolic | |
| Each symbolic-storage check | 14 s incl. startup, under 1 s symbolic | |

Halmos install used the whole 10-minute setup box, but it finished.

Changes made to the copy only (the implementation checkout is untouched):

1. **Library linking.** Halmos resolves library placeholders only for the test
   contract itself. `ShieldedPool` uses external libraries `LeanIMT` and
   `PoseidonT3`, so `setUp` failed with `non-hexadecimal number found in fromhex()`.
   Fix: `foundry.toml` gets `libraries = [LeanIMT at 0xA1001, PoseidonT3 at 0xA1002]`.
   `setUp` deploys each library from `vm.getCode` and `vm.etch`es its runtime code
   at that address. The pool bytecode differs from a normal build only in the
   two linked addresses. Side effect: plain `forge test` in the copy now fails,
   because the fixed addresses hold no code outside this harness.
2. `out` symlink to `contracts/out`, because `vm.getCode` in Halmos reads `out/`.

Storage layout confirmed with `forge inspect ShieldedPool storageLayout`. It
matches CORRESPONDENCE.md section 2 exactly (slots 0-3 tree, 4-103 roots,
104 index, 105 `validRoots`, 106 `nullifiers`, 107 tokens, 108 verifier,
109 registry, 110 owner). That table was marked unverified; it is now verified.

## Harness

File: `proj/contracts/test/halmos/PoolSymbolic.t.sol`.

- `MockVerifier` from `src/mocks/MockCompositeVerifier.sol`: always returns true.
  Verifier soundness stays a named assumption (A1), as in the Lean model.
- `StubRegistry`: fixed attestation root 7, to keep PoseidonT5 off the path.
- `MockERC20` (OpenZeppelin ERC20) as the normal token. `HookToken` for P3: its
  `_update` hook reads `pool.nullifiers(n)` during the payout and then tries to
  re-enter `withdraw` with the same nullifier.
- `ShadowTree`: a separate LeanIMT that gets the same leaves one at a time, so
  the harness knows the root of every leaf prefix.
- Reached state from `setUp` (concrete): deposit leaf 1, deposit leaf 2,
  withdraw spending `0xa0`, transfer spending `0xa1`,`0xa2` with outputs 3 and 4.
  Result: 4 leaves, 3 spent nullifiers.

Common command (run from `proj/`, with `PATH` including `~/.foundry/bin` and
`FOUNDRY_LINT_LINT_ON_BUILD=false`):

```
../.venv/bin/halmos --contract PoolSymbolicTest --loop 8 --solver-timeout-assertion 60s --function '<regex>'
```

Any-call checks also used `--default-bytes-lengths 0,65`.

## Results per property

"Reached state" means: symbolic call arguments, one concrete prior state.
"Arbitrary storage" means `svm.enableSymbolicStorage(pool)`: every pool slot is
symbolic except verifier and registry addresses (pinned so calls resolve). That
over-approximates every reachable state, so a PASS there is a one-call
inductive step for that function.

### P1. Nullifier set only grows

| Test | Kind | Result | Time |
|---|---|---|---|
| `check_P1_nullifierMonotone_symStorage_withdraw` | arbitrary storage, withdraw | **PASS** (15 paths, bounds []) | 0.50 s |
| `check_P1_nullifierMonotone_symStorage_transfer` | arbitrary storage, transfer | **OUT OF REACH**: killed at 150 s cap | |
| `check_P1_nullifierMonotone_anyCall` | reached state, `createCalldata("ShieldedPool")`, any caller | **OUT OF REACH**: killed at 420 s cap | |
| `check_P1_nullifierMonotone_reached_deposit` | reached state, deposit | **OUT OF REACH**: 12.9 GB after 76 s, killed by the controller | |
| `check_P1_nullifierMonotone_reached_transfer` | reached state, transfer | **OUT OF REACH**: 12.8 GB (controller) / 16.8 GB peak RSS (`/usr/bin/time -l`) after 42 s, killed by the controller | |
| `check_P1_nullifierMonotone_twoCalls` | two arbitrary calls | not run | |

Why transfer and deposit are hard: both call `LeanIMT.insert`, which runs the
PoseidonT3 hash (hundreds of `mulmod` steps) on symbolic leaves. With symbolic
storage the tree depth is symbolic too, so the insert loop branches.

Honesty note on these timings: a killed batch from 19:16 (same checks) kept
running until 19:39, because my first `pkill` ran inside the sandbox and did
not kill it. The controller reported 4 to 6.4 GB per Halmos process and macOS
killing background processes. So the P1 any-call and P5 timeouts were measured
under contention. The later reached-state deposit and transfer runs were alone
and still passed 12 GB within 76 s, so P1 on insert paths is out of reach at
`--loop 8` on this machine, with or without contention. The controller asked
me not to rerun them; I did not.

By code reading (not a tool result): no function in `ShieldedPool.sol` writes
`false` to `nullifiers`. The only writes are `= true` at lines 225, 226, 281.
A grep-level argument, not a proof.

### P2. A spent nullifier cannot be spent again

| Test | Kind | Result | Time |
|---|---|---|---|
| `check_P2_withdrawSpentReverts_symStorage` | arbitrary storage | **PASS** (5 paths, bounds []) | 0.07 s |
| `check_P2_transferSpentReverts_symStorage` | arbitrary storage, either input spent | **PASS** (4 paths, bounds []) | 0.08 s |
| `check_P2_withdrawSpentReverts` | reached state | **PASS** (5 paths) | 0.06 s |
| `check_P2_transferSpentReverts` | reached state | **PASS** (4 paths) | 0.08 s |
| `check_P2_withdrawTwiceSecondReverts` | reached state, fresh `n`, withdraw twice | **PASS** (2 paths) | 0.12 s |
| `check_W_P2_firstWithdrawReachable_expectFail` | witness | **FAIL as intended**: first withdraw can succeed (n=0, amount=2^99) | 0.23 s |

The witness shows the "withdraw twice" PASS is not vacuous. The symbolic-storage
P2 results do not depend on the mock verifier: the nullifier check at lines 199,
200, 258 reverts before the verifier is called.

### P3. Nullifier is marked spent before the token transfer

| Test | Result | Time |
|---|---|---|
| `check_P3_spentBeforePay` | **PASS** (7 paths) | 0.11 s |
| `check_W_P3_withdrawSuccessReachable_expectFail` | **FAIL as intended**: a successful hooked withdraw exists | 0.23 s |

On every successful withdraw with `HookToken`: the hook fired, it saw
`nullifiers(n) == true` during the payout, and its re-entrant withdraw with the
same `n` failed. Reached state only, symbolic `n`, `amount`, `recipient`.

### P4. `isKnownRoot` accepts only roots the contract produced

| Test | Result | Time |
|---|---|---|
| `check_P4v1_postTxRootsOnly_expectFail` (produced = roots after each transaction) | **COUNTEREXAMPLE**: `r = 0x1e8c05563aa22ff357008db7a754ea0404695de07b950ce845b872a8bcff2ca9` | 0.13 s |
| `check_P4_knownRootsOnly_reached` (produced = root of every leaf prefix) | **PASS** (5 paths) | 0.09 s |
| `check_P4_zeroRootNotKnownAfterInsert` | **PASS** | 0.01 s |

The counterexample root is the root after leaf 3, **between the two insertions
of one transfer**. No transaction ends on it, but `_insertCommitment` puts it in
`validRoots` when the second output is inserted. The prefix form passes, so the
contract accepts exactly the prefix roots in its buffer (for this reached state).

This gives **two differences from the Lean model** (`Pool/Tx.lean:168`,
`Pool/State.lean:143,150`):

1. **Mid-transfer root.** The model pushes one root per transfer
   (`minted.length + 2`). The chain also accepts the `+1` root, and a transfer
   uses **two** of the 100 buffer slots. The on-chain window therefore covers as
   few as 50 transfers, while the model's `rootWindow` counts operations. The chain
   is more permissive here. It is still the root of a real tree prefix, so
   membership stays sound, but the model's window does not describe the chain.
2. **Empty-tree root.** The model starts with `window := [0]` and keeps 0 until
   it is pushed out. On chain, `isKnownRoot(0)` is true only while the tree is
   empty, because `_insertCommitment` skips a zero current root (line 368). The
   model is more permissive here.

Both are review points for CLAUSEMAP. Neither breaks `noOverWithdrawal`
directly, but the `rootInWindow` guard in the model is not the chain's guard.

### P5 (stretch). Tree size never decreases

`check_P5_treeSizeMonotone_anyCall`: **OUT OF REACH**, killed at 420 s cap
(under the contention described in P1). By code reading, `_tree.size` is written
only in `insert`, as `++index`. The pool never calls `update` or `remove`.

## Scope and bounds (read before using any PASS)

- **Bounded, not unbounded**, unless marked "arbitrary storage".
  Reached-state results cover one concrete prior state and one or two symbolic
  calls. They say nothing about other histories.
- **Arbitrary-storage results** (P1 withdraw, P2 withdraw, P2 transfer) are
  one-step results over all storage values. With the trivial base case they
  imply the property for every reachable state for that function. But: they cover
  one function each, not all entry points. `proof` and payload bytes are the
  empty literal. The token is one concrete `MockERC20`. Verifier and registry
  addresses are pinned.
- `--loop 8`. All PASS lines report `bounds: []`, so no path was cut by the
  loop bound. Default call depth, unlimited width and depth.
- Solver timeout for assertions 60 s. No assertion timed out in any PASS run.
- Trust base: Halmos symbolic EVM, solc 0.8.33 output, the SMT solver, OZ
  `ERC20` in the mock token, the mock verifier, the library-address change.
- Out of scope: verifier soundness, the real `AttestationRegistry`, other
  tokens (fee-on-transfer, rebasing), governance calls between steps.

## Map onto the Lean model's named assumptions

This is a reviewed table, not a theorem. No Lean statement refers to these
checks. Row ids are from (research record, 2026-09-16).

| Row / assumption | Lean side | Halmos evidence | Status |
|---|---|---|---|
| P1 nullifier monotone | `St.nullifiers` append-only, `noOverWithdrawal` | withdraw: PASS, arbitrary storage. transfer, deposit, any call: out of reach. Code reading: only `= true` writes | partial |
| P2 write-once / no re-spend | `St.nullifiers.Nodup`, `St.fresh` guard | withdraw and transfer revert on a spent nullifier from arbitrary storage; second withdraw reverts | discharged for the guard, per function, one step |
| P8 spend before pay, simpl. 9 | `Step` atomicity | P3 PASS with a re-entrant token: spent flag visible during payout, re-entry fails | discharged for withdraw, reached state only |
| Non-reentrancy (simpl. 9) | `Step` atomicity | re-entrant withdraw inside payout fails (P3) | withdraw only; deposit re-entry not checked here (existing forge test covers it) |
| P3 root window well-formed | `St.window`, `rootInWindow`, `pushWindow` | P4 prefix form PASS; **two mismatches found** (mid-transfer root, empty root) | **model differs from chain** |
| P4 tree grows | `St.minted` grow-only | P5 out of reach; code reading only | open |
| A1 verifier soundness | `CryptoHyp` | mock always true | stays assumed |
| A3 ERC-20 honesty | `St.balance` | one OZ mock, one hook token | stays assumed |
| A6 mapping-key injectivity | (new at L8) | Halmos models `keccak` mapping slots as injective | assumed inside the tool, same as A6 |

## Recommendation

**Halmos is worth keeping for the cheap, high-value rows (P2, P3/P8, root
window), and it already paid for itself with the P4 mismatch. It is not the route
to "all entry points, all states".**

- **Halmos (this trial).** Setup 10 min, checks in seconds when the path avoids
  Poseidon. Weak spots: symbolic Poseidon inside `LeanIMT.insert`, memory (over
  12 GB in under 80 s on insert paths), external-library linking, and results that are bounded
  unless you write per-function symbolic-storage checks. Next step if continued:
  abstract `PoseidonT3.hash` with a `vm.etch`ed stub that returns an
  uninterpreted-looking value (for example `keccak256` of the inputs). Nullifier
  and ordering properties do not depend on hash values. That should bring P1
  transfer/deposit and P5 into reach in minutes. Record the stub as an assumption.
- **Kontrol (K/KEVM).** Unbounded proofs with loop invariants and a real
  semantic base (KEVM). It reuses Foundry tests like these. Costlier: KEVM
  install (Docker or kup, GBs), long runs, and manual invariants for the
  `LeanIMT` loop. Good fit for making P1/P2 unbounded across all entry points.
- **Certora Prover.** CVL invariants plus `hook Sstore nullifiers` would state
  P1 over all functions and all states in one rule, with preserved blocks for
  induction. It handles `mulmod` by summarizing. Cost: a hosted service and an
  account key, and CVL is a second spec language to review. Best tool for the
  "all entry points" invariants if an account is available.
- **EVMYulLean directly (no evm-smith).** The only route that ends in a Lean
  theorem next to the model, so the correspondence table could become a proof.
  Cost is highest: a bytecode-level walk of a 383-line contract with two external
  libraries, and no automation. Do it only for P8 (spend before pay), after
  Halmos or Certora has settled which statements are true. The P4 mismatch shows
  why: check the statement cheaply before proving it expensively.

Suggested order: fix the model window (P4 findings) first, then Halmos with a
Poseidon stub for P1/P5, then Certora or Kontrol for all-function invariants.

## Files

- `proj/contracts/test/halmos/PoolSymbolic.t.sol` (harness, 17 `check_` tests)
- `proj/foundry.toml` (copy with the `libraries` addition)
- `run1.txt`, `run3.txt`, `run_*.txt` (raw Halmos output), `LOG.md`

