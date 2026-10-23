> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-10-07 (amended 2026-10-11).
> Sanitised for publication: see [../README.md](../README.md).

> Reviewed over six rounds, with one open item on this report (R5) and one on the review's basis note (R6), which
> is not included. Amended 2026-10-11: R5, C11 and C12 are applied in the text
> below at the place the reviewer named. R6 and C13 concern the review's basis note, not this report; they
> are recorded here as accepted. The amended text was given to Astra for a re-read on 2026-10-11
> (2026-10-11). Astra's verdicts: R5 CLOSED, C12 CLOSED (it recomputed the twelve
> precheck inequalities), C11 OPEN only for evidence: the goal-3 node constraint dumps were not tracked. They are now:
> `d/outputs/g3-*-node{11,13,14,16}-constraints.txt` and `d/outputs/g3-constraints-summary.txt`, extracted with
> `d/bin/kconstr.py` from the saved KCFGs on 2026-10-11 (node 16: 16 deposit / 20 transfer constraints; node 11 holds both
> `< 2^64` bounds and the combined bound). R6 and C13 stay open until the basis note is edited
> (one sentence each; the text is below). The items, as the round-6 review stated them:
> - R5 (applied, section "Proposed CLAIM1 wording", X2): the proposed X2 change dropped `t != vm` and targeted wording
>   that is not in CLAIM1.md:118. The X2 bullet now appends the reviewer's sentence and keeps the deposit and movement limits.
> - R6 (basis note, accepted): "the prank split blocks every symbolic-caller proof in Kontrol 1.0.255" is too wide. Read:
>   "the prank split blocked this symbolic-caller harness (and N5b's) in Kontrol 1.0.255."
> - C11 (applied, goal 3 result): "the only path constraint" was wrong. It now reads "the additional decoder branch
>   constraint": node 16 holds 16 (deposit) / 20 (transfer) constraints. Entry node 11 holds both independent bounds (proof
>   and note lengths < 2^64) and ceil32(proof) + ceil32(note) < 2^128 - 228 (deposit) / 2^128 - 292 (transfer). The
>   entry-length check (C4) was possible; it is input-domain evidence, not an S2 result.
> - C12 (applied, "Runs and costs"): "Every logged precheck passed its arithmetic" was false. The first precheck (01:15:47)
>   failed (11 >= 12), the job waited and retried, and all later prechecks passed.
> - C13 (basis note, accepted): the goal-3 OOM was not caused by the withdraw part (already removed); the unused S2 entry
>   points were removed after it.

# REPORT night-kontrol (track K): withdraw with a token at any address, symbolic caller, S2 with two symbolic byte strings

Writer: a Claude Opus 5.5 agent; reviewer: a Codex agent. Night of 2026-10-06/07. Work dir: the research-phase directory of this
report (W below; not copied here). Tags: [checked] = I ran it, with the log path;
[read] = source reading, with file:line.

## Verdict

1. **Goal 1 landed: SYMTOK scope A closed [checked].** `D4Withdraw.prove_W_success` with the token
   argument at any address above 0x11 (not the cheatcode account): PROOF PASSED, graph closed (225
   nodes, 36 terminals, 0 pending, 0 stuck, 0 vacuous). All six mutants FAIL with their target error
   at a node whose constraints all hold at a stated point, and each has a forge replay. A successful
   withdraw exists only on the two recording tokens. One new trusted rule: the NIGHT-LEMMAS
   bytes-prefix lemma (below).
2. **Goal 2 stopped: symbolic caller not closed [checked].** `prove_W2c_success` stalls on Kontrol's
   `vm.prank` account split (the N5b pattern). No verdict. Caller independence of `withdraw` stays a
   [read] argument.
3. **Goal 3 stopped: S2 with two symbolic byte strings not closed [checked].** All four proofs
   (two stock, two mutants) fail at the test entry, before the pool runs: the test function's own
   ABI decoder rejects a second `bytes` argument when the first is close to 2^64 bytes long. No S2
   result for a nonempty symbolic proof. The S1/S2 line "proof and payload both symbolic: not
   closed" stays.

## Goal 1: token at any address above 0x11 (CLAIM1 W6, W10)

### What changed [checked: `W/d/harness/D4.t.sol`, diff against SYMTOK's file]

One line in `prove_W_success`, beside SYMTOK's `vm.assume(token != address(vm));`:

```solidity
vm.assume(uint160(token) > 0x11);
```

Body, setUp and mutants are SYMTOK's. Why 0x11 [read]: SYMTOK's run stalled where the no-account
branch reached `#precompiled(token)` and forked on `#stackDelta`
(2026-10-06). The compiled KEVM rule
is `isPrecompiledAccount(A, SCHED) => 0 <Int A andBool A <=Int #precompiledAccountsUB(SCHED)`, and the
bound is at most 17 over all schedules (PRAGUE 17; OSAKA reuses it). Above 0x11 the guard is false.

### The bytes-prefix lemma [checked: `W/logs/g1-J1.txt`, `W/d/feasible/W_success.node217-*.txt`]

The first run (J1, no lemma) failed the stock proof at node 217 with `W10Calls()`. Node 217 is on the
no-code branch. Its last path constraint is

```
b"\x00 ... \x00\x01" (32 bytes) == b"\xa9\x05\x9c\xbb" +Bytes #range(#buf(32, rcp), 0, 28)
```

This is `SafeERC20._safeTransfer`'s `eq(mload(0x00), 1)` after a call that returned no data
(OZ 5.6.0-rc.1 `SafeERC20.sol:184-187`) [read]. Memory still holds the selector and `to`. The equality
is false for every `rcp` (byte 0 differs). Kontrol 1.0.255 did not decide it, so it explored an
impossible success. `kfeasible.py`: 40/41 constraints true at the no-code point; the false one is
this equality.

Fix: `W/d/lemmas/night-lemmas.k`, module `NIGHT-LEMMAS`, four `[simplification]` rules (`==K` both
ways, `#Equals` both ways). Each says: when `B1` and `B2` are concrete,
`lengthBytes(B2) <=Int lengthBytes(B1)` and `substrBytes(B1, 0, lengthBytes(B2)) =/=K B2`, then
`B1 == B2 +Bytes X` is false. Soundness [read]: equality would make `B2` a prefix of `B1`. The
reviewer checked the argument (round 3). Build:
`kontrol build --no-O2 --regen --require k/night-lemmas.k --module-import <C>:NIGHT-LEMMAS` for the
seven test contracts (`W/d/bin/build-L.sh`, `W/logs/g1-J0L.txt`, BUILD_EXIT=0).

### Verdicts [checked: `W/logs/g1-J1L.txt`]

`bash d/bin/check.sh d/expected-g1.tsv logs/g1-J1L.txt`: 7 as expected, 0 different. The log has one
`PROOF PASSED` (one claim: the stock proof) and six `PROOF FAILED` (the mutants). Wall 2288 s, peak
6.52 GB at the 8g cap.

### Stock graph [checked: `W/d/outputs/WA_success-summary.txt`]

- 225 nodes, 173 edges, 15 splits, 36 terminals, one leaf (the target); 0 pending, stuck, vacuous.
- The token CALL forks 10 ways at nodes 104 and 120: the nine existing accounts and a no-code
  default branch. No node has `#precompiled` or `#stackDelta`.
- Success terminals (withdraw returned, nullifier written, one recorded call): 226 and 232 with
  `token == TOKEN`, 228 and 233 with `token == other`. No other terminal is a success.
- Non-vacuity: node 226 is 28/28 true at `point-high.json`, node 228 is 28/28 true at `point-low.json`
  (`W/d/feasible/WA_success.node226.txt`, `.node228.txt`). Forge replays
  `Replay_W.test_W_success_original_high` and `_low` pass (`W/logs/replay-host-4.txt`).

### Mutants [checked: `W/d/outputs/A-mutants-summary.txt`, `W/d/feasible/A-M_*.txt`, `W/logs/replay-host-4.txt`]

| Mutant (change) | Node | Output | Path | kfeasible | Forge replay (host forge 1.8.3) |
|---|---|---|---|---|---|
| TOK (pays one fixed token) | 123 | 0x7fa6412e `W10WrongToken` | token != TOKEN | 32/32 point-low; 32/32 point-nocode | `Replay_M_TOK.test_replay_low_token_fails`, `test_replay_nocode_token_fails` |
| W6O (marks after payout) | 202 | 0xe3e0fc25 `W6NotMarkedAtPayout` | token == TOKEN | 28/28 point-high | `Replay_M_W6O.test_replay_token` |
| PIW (nullifier and root swapped) | 104 | 0x1987cd34 `W10Inputs` | n != r | 31/31 point-high | `Replay_M_PIW.test_replay` |
| NULHI (bit 253 dropped) | 97 | 0x1987cd34 `W10Inputs` | mask & n != n | 31/31 point-low-nhi | `Replay_M_NULHI.test_replay` |
| PAY (pays msg.sender) | 229 | 0x0bc6283d `W10Args` | token == other, rcp != test contract | 29/29 point-low | `Replay_M_PAY.test_replay` |
| SKIPV (verifier skipped) | 173 | 0x5b1cfd09 `W10VerifierBypassed` | token == TOKEN, acc == 0 | 25/25 point-high-reject | `Replay_M_SKIPV.test_replay_token` |

Every failing node's output is the target selector of that mutant. Replays: 23 of 23 pass. The TOK
kill at a no-code token (0x1234567) is a path that SYMTOK's two-token scope could not reach. It adds
a negative control. It does not add a successful token implementation. W6O is W6's control; the other
five are W10's.

Points (`W/d/feasible/point-*.json`): n = 1, a = 1, rcp = 0x1234, r = 0, acc = 1, empty proof; token
TOKEN (`point-high`), `other` = 0xc7183455...0bb1 (`point-low`) or 0x1234567 (`point-nocode`);
`-nhi`: n = 2^253 + 1; `-reject`: acc = 0. Storage: `supportedTokens[token] = 1` (slot
`keccak(token . 107)`, formula checked against SYMTOK's point). No point comes from Kontrol's printed
Model.

### Scope line (exact)

Withdraw success path. Token argument: any address t with t > 0x11 and t != the cheatcode account,
within a fixed-code environment: two armed recording tokens, seven other deployed contracts, no code
elsewhere. Successful withdrawals exist only on the two recording mocks. Fixed caller (the test
contract). Symbolic n, a, rcp, r, acc at full width. Symbolic pool storage except slot 108, slot 109
and the reentrancy slot. Proof length < 2^64, content symbolic. Comparison verifier mock. Recording
token mocks that move no balances. Kontrol 1.0.255, the patched `abi.md` (e249e9e2...7a88), the
NIGHT-LEMMAS bytes-prefix rule, gas off, KEVM keccak lemmas.

Not claimed: arbitrary token code or behaviour, token movement (A10 stays assumed), proof binding
(A2), addresses 0x00 to 0x11, a symbolic caller.

### Proposed CLAIM1 wording (CLAIM1.md not edited; the controller decides)

- **W6** (`CLAIM1.md:107`), evidence: after "SYMTOK proves the same for a symbolic choice between
  two recording tokens, with a fixed caller." add "night-kontrol re-proves it with the token argument
  t > 0x11, t != vm, within the stated fixed-code environment; successful withdrawals only on the two
  recording mocks; fixed caller; one added Kontrol lemma (bytes prefix). The order mutant fails
  feasibly." Status: replace the SYMTOK token scope with "token argument t > 0x11, t != vm, in a
  fixed-code environment (success only on two recording mocks); fixed caller". Keep the deployment
  and trust qualifications.
- **W10** (`CLAIM1.md:111`), evidence: add "night-kontrol: the same checks with the token argument
  t > 0x11, t != vm, in the fixed-code environment; five W10 controls fail feasibly, including the
  wrong-token payout at a no-code token; trust adds the NIGHT-LEMMAS bytes-prefix rule." Keep
  "Binding needs A2; actual movement needs A10" and the arbitrary-token-behaviour limit.
- **X2** (`CLAIM1.md:118`), evidence: append "night-kontrol re-proves the withdraw marking clause under the W6
  fixed-code scope: t > 0x11, t != vm, fixed caller, successful withdrawals only on the two recording mocks, with
  NIGHT-LEMMAS." Keep the deposit and movement limits. (R5 applied: the earlier bullet dropped `t != vm` and targeted
  wording that row does not contain.)

## Goal 2: symbolic caller (stopped)

Harness: SYMTOK's `prove_W2c_success` unchanged (scope B, `vm.prank(who)`, no assumption on `who`).
Job J3 from the lemma build, with the six mutants queued.

Result [checked: `W/logs/g2-J3.launch`, `W/d/outputs/J3-*-splits.txt`, `J3-*-kcfgsum.txt`]: no verdict.
I stopped the job at 669 s (rc 137 is my `docker kill`). Splits 35, 46, 47, 68 and 80 are each
11-way: `who` equal to one of ten fixed addresses (the nine accounts and 0xA1001), plus a default
branch with no constraint. The default branch of 35 is 46, and the default branch of 46 is 80, so the
split repeats with no progress. Splits 69 and 81 to 89 are two-way guard branches. At the stop: stock
143 nodes, 2 terminals, 63 leaves; PAY and TOK 132 nodes, 53 leaves each. This is N5b's
`foundry_loadAccount` stall.

Stop decision: the plan's rule was "stop at 60 min if the split re-splits at depth 2 or more". The
repeat was shown at 11 minutes, so I stopped then to give the time to goal 3. This is an early stop
by my decision, disclosed here.

Fallback [read]: the pool reads `msg.sender` only at `ShieldedPool.sol:99` (`onlyOwner`), `:108` and
`:110` (constructor) and `:149` (deposit). `withdraw` (`:246-289`) has none, and OZ `ReentrancyGuard`
does not read it. This is a source reading, not a checked result.

Proposed CLAIM1 wording: W6 and W10 keep "fixed caller", with the note "caller independence of
withdraw [read]; the symbolic-caller proof stalls on Kontrol's prank account split (night-kontrol J3)".

## Goal 3: S2 with proof and payload both symbolic

Plan (round 4): two new entry points in a trimmed copy of the S1/S2 harness
(`W/d/harness3/S2x.t.sol`), `prove_S2d2(c, t, a, bytes proof, bytes note)` and
`prove_S2t2(n0, n1, c0, c1, r, bytes proof, bytes note)`, with tree size, depth and current root
pinned to zero (slots 0, 1 and `keccak(0 . 2)`; remaining tree storage and root history symbolic).
Mutants S2D and S2T (specs dated 2026-10-01, `W/d/bin/mkmut3.sh`).

Builds [checked: `W/logs/g3-J5b.txt`, `g3-J5b2.txt`]: the first build hit the 8g cap (kompile OOM). I
removed the six unused entry points (blob, witness, empty-proof) from the trimmed file; the second
build passed (BUILD_EXIT=0). Host compile and replays: 4 of 4 (`W/logs/replay3-host-1.txt`).

Result [checked: `W/logs/g3-J5.txt`; `check.sh d/expected-g3.tsv logs/g3-J5.txt`: 2 as expected, 2
different]: all four proofs `PROOF FAILED` in under 50 s, each at node 16, status `EVMC_REVERT`,
output "No revert reason", one pending node (14). The additional decoder branch constraint is (C11 applied: node 16
holds 16 constraints for deposit and 20 for transfer, including both length bounds and the combined encoding bound;
entry node 11 holds both independent bounds, proof and note lengths < 2^64, and ceil32(proof) + ceil32(note) <
2^128 - 228 for deposit and < 2^128 - 292 for transfer. These entry bounds are input-domain evidence, not an S2 result.
Dumps: `d/outputs/g3-<proof>-v<run>-node<N>-constraints.txt` for nodes 11, 13, 14 and 16 of all four proofs and both
runs, counts in `d/outputs/g3-constraints-summary.txt`.)

- deposit: `2^64 - 193 < ceil32(lengthBytes(proof))`;
- transfer: `2^64 - 257 < ceil32(lengthBytes(proof))`.

Reading [read]: this is the test function's calldata decoder. With `proof` near 2^64 bytes, the
offset of the second `bytes` argument passes the decoder's 64-bit bound, so the call reverts before
`_fresh()` runs. No real call can carry such a proof, but Kontrol counts the revert as a failure and
stops (fail_fast). The pool is never reached on this path. The two mutant FAILED verdicts are not
kills: the output is not `S2Inputs()`.

Why no rerun: the round-4 plan allowed no other goal-3 harness tonight, and the council's last round
is this one. Candidate next steps [read, not tried]: put the length bound inside the test before
the pool call (for example one `bytes` argument split by a symbolic index, the S1/S2 blob design,
whose earlier run ended by a machine suspend, not a stall), or build the proof bytes inside the test
so the pool's own decoder, inside the `try`, sees them.

J5 ran twice [checked: `W/logs/g3-J5.launch`]: I replaced `launch.sh` while the goal-3 chain was
running, and the running shell read the new file. Both runs (138 s and 137 s) gave the same four
verdicts at node 16. Graphs: `W/w/g3/proj/contracts/out/proofs/` (untracked).

## Runs and costs [checked: `W/LOG.md`, the run lines]

| Run | What | Wall | Peak (cap 8g) | Outcome |
|---|---|---|---|---|
| g1-J0 | build, with the WAc probe | 137 s | 8.59 GB (cap) | haskell kompile exit 137 |
| g1-J0b | build, WAc removed | 120 s | 8.24 GB | BUILD_EXIT=0 |
| g1-J1 | scope A stock, TOK, W6O | 1195 s | 5.79 GB | stock FAILED (node 217); TOK, W6O FAILED |
| g1-J0L | build with NIGHT-LEMMAS | 78 s | 5.85 GB | BUILD_EXIT=0 |
| g1-J1L | scope A stock + six mutants | 2288 s | 6.52 GB | 7 of 7 as expected |
| g2-J3 | W2c stock, PAY, TOK (+4 queued) | 669 s | not read (killed) | stopped by me; prank split repeats |
| g3-J5b | goal-3 build | 99 s | 8.59 GB (cap) | BUILD_EXIT=1 (kompile OOM) |
| g3-J5b2 | goal-3 build, trimmed | 88 s | 8.59 GB (cap) | BUILD_EXIT=0 |
| g3-J5 (x2) | S2d2, S2t2, S2D, S2T | 138 s, 137 s | 4.51, 4.72 GB | 4 FAILED at node 16 (decoder) |

Host forge 1.8.3 replays: 18, 21, 22, 23 of the same file as it grew, all pass
(`W/logs/replay-host-1.txt` to `-4.txt`); goal 3: 4 of 4.

Every container: cap 8g with no swap, core dumps off, the Kontrol image
`runtimeverificationinc/kontrol:ubuntu-jammy-1.0.255`, one container at a time, the patched `abi.md`
mounted read-only. Gates before each start: `precheck.sh` (available - 3 GiB >= cap + every capped
user scope) and `crun.sh` (available >= cap + 3 GiB, plus `acir-deposit/scripts/gate.sh`). Round 5
found that `launch.sh` ignored the precheck exit status; it now enforces it and the 07:00 deadline
(a later fix). The first precheck (01:15:47) failed its arithmetic (available 14 GiB - 3 = 11 against cap 8 + capped scopes 4 = 12); the job waited and retried; every later precheck passed (C12 applied).

## Files

Tracked: `W/d/harness/` (D4.t.sol, Replay.t.sol), `W/d/harness3/` (S2x.t.sol, Replay3.t.sol, mutant
diffs), `W/d/lemmas/night-lemmas.k`, `W/d/bin/` (runner, gates, scripts), `W/d/expected-g*.tsv`,
`W/d/feasible/`, `W/d/outputs/`, `W/logs/`, `W/LOG.md`.

Untracked (large or private; listed): `W/w/` (Kontrol projects, kompiled definitions, saved KCFGs:
`w/proofs-J1` (J1, no lemma), `w/proofs-J1L` (goal 1), `w/proofs-J3` (goal 2), `w/g3/` (goal 3));
`W/d/src/` (the pool source, ethsystems/pocs `a04b8b3`, sha256 8cad5615...fac59c94, checked against
`W/d/src.sha256`); `W/d/deps/`; `W/d/kevm-patch/abi.md`.

## Checked versus read

[checked]: every verdict line and `check.sh` result; graph summaries; failing nodes, outputs and
constraints; each kfeasible line at its stated point; the forge replays; build and run costs; the
storage layout (forge inspect); the J3 split structure.

[read]: the precompile bound in the compiled KEVM definition; the lemma's soundness; the SafeERC20
reading of node 217; that `withdraw` does not read `msg.sender`; that the recording mocks move no
balances (A10).
