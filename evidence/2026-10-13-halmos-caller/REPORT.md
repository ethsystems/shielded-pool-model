> Frozen copy. Measured once in the research phase, not rerun here. Source date 2026-10-13.
> Sanitised for publication: see [../README.md](../README.md).

# REPORT halmos-caller: withdraw success path with a symbolic caller (Halmos)

Worker: Claude Opus 5.5, 2026-10-13 (resume of a first run). CLAIM1 is not edited.

Target [checked]: ethsystems/pocs `a04b8b3`, `ShieldedPool.sol` sha256 `8cad5615...`, from `git show` only.
All 12 source hashes are D5X1's (`SOURCES.sha256`, identical file); LeanIMT linked at `0xA1001` by the
D5X1 library patch (`libraries.txt`, identical). Tools [checked]: halmos 0.3.3 (yices 2.6.4 for
assertion queries, z3 4.12.6 for path pruning), forge 1.8.3, solc 0.8.37, optimizer 100 runs.

Tags: [checked] = a run whose log is in `logs/`. [read] = source reading, with file:line.

## Verdict

1. **Stock: PASS [checked].** `check_withdraw` holds on every path with a symbolic caller: 154 paths,
   1.86 s solver time, 4 s wall, peak 0.32 GB (`logs/g_S_full.txt`). The caller is `vm.prank(who)`
   with no assumption on `who`. Halmos keeps `msg.sender` symbolic in the pool frame and does not
   split on it.
2. **Teeth: both mutants FAIL [checked].** W6O (marking moved after the payout) fails at
   W6NotMarkedAtPayout. PAY (payout to `msg.sender`) fails at W10Args, and its trace shows the payout
   call `transfer(who, a)` with the symbolic caller. Both counterexamples replay concretely in forge.
3. **Non-vacuity [checked].** Both success witnesses FAIL as intended: a successful withdraw exists on
   each recording token in this environment.
4. **Reproduced [checked].** A fresh copy from `git show a04b8b3` gives identical source hashes, mutant
   hashes and diffs, verdicts and path counts (`logs/verify-fresh.txt`).

So the "fixed caller" limit of W6 and W10 closes under the Halmos scope below. This is a separate
result from night-kontrol's: Halmos samples five proof lengths; Kontrol covered every length below
2^64 with a fixed caller. No single run covers both.

## What the check asserts (`harness/Caller.t.sol`)

`check_withdraw` (`:215`) makes pool storage symbolic (`_fresh`, `:122`), arms both recording tokens,
pranks `who` and calls `withdraw` in a `try` (`_wd`, `:167`). Then `_body` (`:191`) asserts:

- any call: the verifier never saw inputs other than `[n, token, a, rcp, r]` (W10Inputs, `:197`);
- a successful call: the verifier said yes (W10VerifierBypassed, `:200`); exactly one recorded call
  reached the two tokens (W10Calls, `:203`) and it went to `token` (W10WrongToken, `:205`); the
  nullifier was already marked when that token was called (W6NotMarkedAtPayout, `:206`) and is marked
  after (W6NotMarkedAfter, `:207`); neither token recorded another selector (W10Calls, `:208-209`);
  the call was `transfer(rcp, a)` from the pool (W10Args, `:210-212`).

Witnesses `check_witnessHigh` (`:223`, token `TOKEN`) and `check_witnessLow` (`:231`, token `other`)
assert `!ok` with the verifier accepting, so they must FAIL.

## Exact scope

Withdraw success path, Halmos 0.3.3 EVM model with gas unmodelled. **Caller:** symbolic `msg.sender`
through `vm.prank(who)`, no assumption on `who`. **Arguments:** nullifier, amount, recipient, root
and the verifier's answer symbolic at full width; token argument any address `t` with `t > 0x11` and
`t != vm` (the night-kontrol exclusions), and Halmos never lets a symbolic address equal the test
contract (`sevm.py:2229-2244`) [read; the debug log lists the test contract among the code addresses]. **Environment:** fixed code. The token CALL branches over the
eight other deployed accounts (two LeanIMT copies, verifier, registry, the RecToken template, `TOKEN`,
`other`, pool) plus one empty-account branch (`logs/g_P_alias_debug.txt`) [checked]. Successful
withdrawals exist only on the two armed recording tokens. **Storage:** pool and registry storage
symbolic, except slot 108 (verifier), slot 109 (registry) and the reentrancy slot (1), as night-kontrol; other slots the constructor wrote (the owner) keep their values, as in D5X1.
**Bounds:** proof lengths 0, 1, 32, 65 and 1024 bytes, content symbolic; canonical ABI calldata; zero
value. Loop bound 8, never reached. **Mocks:** the comparison verifier (checks all five full-width
words, answers a symbolic `acc`) and two recording tokens that move no balances. Real LeanIMT at its
link address; PoseidonT3 is not executed on this path.

## Harness review (done before any run)

Against night-kontrol `d/harness/D4.t.sol` [checked by diff]: `CmpVerifier`, `SymRegistry`,
`RecToken`, `setUp`, `_fresh`, `_wd` and `_body` are the same, with three changes:

- `kevm.symbolicStorage` becomes `svm.enableSymbolicStorage`.
- `vm.prank(caller)` runs on every call, with `caller = who` symbolic.
- Each `revert W...()` becomes `assert(!(...))` with the error name as a comment. Halmos reports only
  assertion failures (`Panic(1)`) and the fail flag (`__main__.py:1089-1091`) [read]. A test-level
  revert drops the path. The only test-level reverts left in the body are the getter guards in
  `_get` and `_get1`, which call the two recording mocks and the pool's public `nullifiers` getter;
  these cannot fail on these paths [read]. So no path is dropped silently.

`check_withdraw` joins night-kontrol's scope A (`prove_W_success`) and its symbolic-caller probe
(`prove_W2c_success`). Against D5X1: same flags (`--loop 8 --solver-timeout-assertion 60s`), byte
lengths B5 = {0, 1, 32, 65, 1024} for the stock run and {0, 65} with `--early-exit` for mutants, same
runner (one systemd scope, MemoryMax 3G, swap 512M, SIGKILL at 900 s, memory gate, no `ulimit`).
`bin/mkmut.sh` has night-kontrol's W6O and PAY specs and mutation loop, unchanged [checked by diff].

**Loop bound.** 8, as D5X1. Halmos applies the bound only to branches whose condition is symbolic
(`sevm.py:2836-2870`) [read]. Every loop on this path has a constant trip count of 5: the pool's
`_requireCanonicalInputs` (`ShieldedPool.sol:360`) and the verifier's `_same` [read]. So the bound
never binds. No run logged a bounded-loop warning, and loop 4 and loop 8 give the same 64 paths for
bytes {0, 65} [checked].

## Runs

Every command runs in `project/`: `halmos --contract <C> --match-test <regex> --loop <L>
--solver-timeout-assertion 60s --default-bytes-lengths <B> [extra]`. Times are from
`bin/runall.sh` (`logs/RUNS.log`); halmos time is for the named check.

| Label | Contract, tests | Loop, bytes, extra | Result | Halmos time, wall, peak |
|---|---|---|---|---|
| S_full | D4Withdraw: withdraw, witnessHigh, witnessLow | 8, B5 | PASS 154 paths; FAIL 62; FAIL 62 | 1.86 s; 4 s; 0.32 GB |
| M_W6O | D4W_M_W6O: withdraw | 8, 0/65, `--early-exit -vv` | FAIL, 17 paths | 0.16 s; 2 s; 0.31 GB |
| M_PAY | D4W_M_PAY: withdraw | 8, 0/65, `--early-exit -vv` | FAIL, 17 paths | 0.16 s; 1 s; 0.31 GB |
| P_loop4 | D4Withdraw: withdraw | 4, 0/65 | PASS, 64 paths | 0.80 s; 1 s; 0.31 GB |
| P_loop8_b2 | D4Withdraw: withdraw | 8, 0/65 | PASS, 64 paths | 0.79 s; 2 s; 0.31 GB |
| P_alias_debug | D4Withdraw: withdraw | 8, 65, `--debug` | PASS, 34 paths | 0.41 s; 1 s; 0.32 GB |

Raw scan of every log (`bin/rawscan.sh`, from D5X1): no loop-bound warning, no NotConcreteError, no
ERROR, TIMEOUT, unknown, kill or traceback. The one warning is "unknown deployed bytecode" for the
LeanIMT copy etched at `0xA1001`, as in D5X1. No OOM kill. The first individual runs (12:11 to 12:14)
gave the same verdicts and path counts; the S_full wall there was 7 s, with the compile.

## Mutants

| Mutant | Change (`ShieldedPool.sol`) | Failing assertion | Counterexample | Concrete replay (forge, PASS) |
|---|---|---|---|---|
| W6O | `:283` and `:286`: nullifier marked after the payout | W6NotMarkedAtPayout (`Caller.t.sol:206`) | n 0, token `other`, a 2^127, rcp 2^159, r 0, acc 1, who 0, proof 65 bytes | `Replay_M_W6O`: Panic(1) at the point; the token saw the nullifier unspent, it is spent after |
| PAY | `:286`: pays `msg.sender` | W10Args (`Caller.t.sol:210`) | same values | `Replay_M_PAY`: Panic(1) at the point; with caller `0xBEEF` the token records `to = 0xBEEF` |

How the assertion was identified [checked: `logs/mutant-assertions.txt`]: every assertion gives the
same `Panic(1)`, so the `-vv` trace decides. The body reads one getter before each assertion, in a
fixed order. W6O's last getter before the panic is `spentSeen()` on the paid token; PAY's is `to()`,
after `others()` passed. PAY's trace also shows the pool's payout call `transfer(who, a)`: the
mutant's payout target is the symbolic caller, which a fixed-caller harness sees only when the
recipient differs from the test contract.

Replays (`harness/Replay.t.sol`, `logs/forge-replay.txt`): 6 of 6 pass [checked]. They use the same
`setUp` and body on a fresh pool with both tokens supported (empty tree, root 0 is known). Stock: the
body holds at the counterexample point and with caller `0xBEEF` on `TOKEN`.

## What was not checked

- Proof lengths other than the five sampled; non-canonical calldata. Night-kontrol covers lengths
  below 2^64 with a fixed caller. That `withdraw` neither reads `msg.sender` (`ShieldedPool.sol:246-289`)
  nor branches on proof bytes is [read], not checked jointly.
- Token addresses 0x00 to 0x11, the cheatcode account, the test contract; arbitrary token code or
  behaviour (only the two recording mocks succeed); actual token movement (A10).
- Proof binding (A2) and the production verifier: the verifier is a mock.
- Deposit and transfer. The caller matters for deposit (D6) and is outside this run.
- Re-entry beyond the recording token's one static read of `nullifiers`; gas; nonzero value.
- Halmos's EVM model is trusted, as for D5X1.

## Proposed CLAIM1 wording (CLAIM1.md not edited; the controller decides)

Current text at this branch's `CLAIM1.md:107` and `:111`. If night-kontrol's wording lands first,
the same sentences append after it.

- **W6, evidence:** after "SYMTOK proves the same for a symbolic choice between two recording tokens,
  with a fixed caller." add: "halmos-caller (Halmos 0.3.3) checks the same body with a symbolic
  caller (`vm.prank`, no assumption): token argument t > 0x11, t != vm, in a fixed-code environment
  (success only on the two recording mocks); proof lengths 0/1/32/65/1024; loop bound not reached.
  The order mutant fails (W6NotMarkedAtPayout), with a concrete replay."
- **W6, status:** replace "fixed caller" with "fixed caller in the Kontrol scope; any caller in the
  halmos-caller scope (sampled proof lengths)". Keep the token and deployment qualifications.
- **W10, evidence:** add: "halmos-caller: the same W10 checks hold for a symbolic caller in the scope
  stated in W6; the pay-the-caller mutant fails (W10Args), with the payout going to the symbolic
  caller; concrete replay."
- **W10, status:** in "Assumed (TOKENS, CRYPTO, REF: actual movement, proof binding, any caller and
  token)", change "any caller and token" to "any token"; append "; for any caller within halmos-caller
  scope". Keep "Binding needs A2; actual movement needs A10".

Other rows the controller may touch (not proposed in full): X2 can append "the withdraw marking
clause also holds for any caller within halmos-caller scope". The W10 blocker row "Generalize fixed
token/caller" keeps only the token part. S2's withdraw input order is also covered for any caller,
under the same sampled lengths.

## Reproduce

`HALMOS=<halmos> bin/verify.sh <pocs clone> <dependencies dir> <dest>`: copies the tracked
inputs, runs `bin/setup.sh` (private files by `git show a04b8b3`, hash check, library patch,
mutants), compares the mutant hashes and diffs, then `bin/runall.sh` (all six runs and the
replays). The dependencies dir used here: `pocs/private-payment/shielded-pool/dependencies` in a local
implementation checkout (read only). The runner needs the systemd user
bus, so the Claude Code session ran it outside its sandbox.

## Files

Tracked: `bin/` (setup, mkmut, run, runall, verify, gate, rawscan), `harness/` (Caller.t.sol, Replay.t.sol),
`diffs/` (mutant diffs and hashes), `logs/` (setup, every halmos log, RUNS.log, mutant-assertions,
forge-replay, verify-fresh, and `codex-run-1.log`, the first run's log, stopped by its provider's
content filter before any halmos run), `SOURCES.sha256`, `libraries.txt`. Untracked: `project/`
(the Foundry project with the pool source and dependencies; `.gitignore`).
