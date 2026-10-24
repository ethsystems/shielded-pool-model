# contract-halmos: bounded symbolic checks of `ShieldedPool.sol` at `a04b8b3` (Halmos)

This package runs Halmos 0.3.3 checks on the shielded-pool contract `ShieldedPool.sol` of
ethsystems/pocs (public) at `a04b8b3` (sha256 `8cad5615…`), and on the LeanIMT library it links.
Each check executes the contract symbolically from a stated start state with stated mocks, and
asserts a property on every path that Halmos explores. Each suite also runs mutants, copies of the
contract with one documented change, which must fail the named checks. `check.sh` exports the
sources from the pocs submodule, builds one Foundry project per suite, runs every check and mutant,
and compares each verdict and path count with `EXPECTED.tsv`. [RESULT.md](RESULT.md) records the run
of 2026-10-24.

These are bounded checks, not proofs about the deployed contract and not Lean theorems. A PASS
holds within the scope lines of its suite (below), under Halmos's EVM model, and nowhere else. The
package imports nothing from the model, and the model gate (`scripts/gate.sh`) never runs it.
Nothing here changes the claim in the parent README.

The checks were first written and run between 2026-09-29 and 2026-10-13, before this repository
existed. The reports of those runs (the withdraw-caller report of 2026-10-13 and the root-window
report of 2026-09-16 among them) are research-phase reports that this repository does not carry.
This package reruns the first runs that target the public contract; "Where it comes from" below
lists what is included and what is not.

## Common scope

Every suite shares these lines; each suite below adds its own.

- **Contract.** `ShieldedPool.sol` and the libraries as `foundry.toml` and `soldeer.lock` at
  `a04b8b3` name them, built by forge 1.8.3 with solc 0.8.37, optimizer on, 100 runs. One patch
  (`scripts/foundry-libraries.txt`): `foundry.toml` links `LeanIMT` at `0xA1001` and `PoseidonT3`
  at `0xA1002`, because Halmos fills link placeholders only in the test contract; each harness
  etches the library code at that address in `setUp`. The pool's code differs from a plain build
  only in those two addresses. Three suites add `ast = true` and `dynamic_test_linking = false`
  (`harness/<suite>/foundry-extra.txt`), as their first runs did.
- **Calls.** Canonical ABI calldata only (`abi.encodeCall` or Halmos's own), `msg.value` 0, one
  external call into the pool per check unless the suite says otherwise. `bytes` arguments take
  only the lengths listed per suite, with symbolic content. Halmos 0.3.3 cannot read calldata at a
  symbolic offset, so arbitrary calldata is out of reach (the duplicate-lock suite records the
  attempt as an expected ERROR).
- **Storage.** "Symbolic storage" means `svm.enableSymbolicStorage(pool)` on a pool deployed
  inside the check: every slot is symbolic when first read, except the slots the constructor wrote,
  which keep their values: `verifier` (slot 108), `attestationRegistry` (109), `owner` (110) and the
  ReentrancyGuard status (ERC-7201 slot `0x9b779b…c55f00`, value 1, NOT_ENTERED). A check may
  overwrite one of these (stated per suite). Halmos models mapping slots as injective in their keys.
- **Loop bound.** `--loop L` per run. Halmos applies the bound only to branches on a symbolic
  condition. A PASS counts only if no path reached the bound: `scripts/compare.py` treats a
  loop-bound warning, a solver "unknown" or an OOM kill in the log as a mismatch for every PASS of
  that run.
- **Hash.** Where a suite says "stub", `PoseidonT3.hash` is replaced by `keccak256` of the inputs
  reduced into the field, etched at the library address. A result under the stub says nothing about
  Poseidon values; it covers control flow, the storage writes and the call order. Without the stub,
  the real `PoseidonT3` is linked; on the "full" paths below no hash runs.
- **Semantics.** Halmos 0.3.3's EVM model with gas unmodelled. A path that would run out of gas on
  chain is still explored. The assertion solver timeout is 60 s; no assertion query timed out.
- **Mocks.** The verifier, the attestation registry and the tokens are mocks in every suite (named
  per suite). No check runs the production Honk verifiers, the real `AttestationRegistry`, or a real
  ERC-20.

## The suites

Check names carry the claim-board row they bear on where the first harness used one (`D5`, `X1`,
`T11`, `G1`, `W10`; the board is [../BOARD.md](../BOARD.md)).
`P1` to `P5` are the properties of the 2026-09-16 root-window report. Witnesses (`check_WIT_…`,
`check_W_…`, `…_expectFail`) must FAIL: each shows that the premises of the checks next to it admit
a successful call, so those PASS results are not vacuous.

### caller: the withdraw success path with a symbolic caller

`check_withdraw` holds on every path with a symbolic caller: the caller is `vm.prank(who)` with no
assumption on `who`, and Halmos keeps `msg.sender` symbolic in the pool frame. On every call the
comparison verifier saw no inputs other than `[n, token, a, rcp, r]`. On every successful call the
verifier said yes; exactly one recorded call reached the two tokens, on the token argument; it was
`transfer(rcp, a)` from the pool; the nullifier was already marked spent when the token was called
and is marked after; neither token recorded another selector.

- Token argument: any address `t` with `t > 0x11` and `t != vm`. Fixed-code environment: the token
  call can reach the eight other deployed accounts and one empty account, and succeeds only on the
  two recording tokens, which record their arguments and move no balances.
- Arguments: nullifier, amount, recipient, root and the verifier's answer symbolic at full width;
  proof lengths 0, 1, 32, 65 and 1024 bytes (0 and 65 for the mutants and the loop probes).
- Storage: pool and registry symbolic; slots 108, 109 and the reentrancy status (1) pinned; the
  owner keeps its constructor value.
- Loop bound 8, never reached: every loop on this path has a constant trip count of 5, and loop 4
  and loop 8 give the same paths.
- Mocks: the comparison verifier (checks all five full-width words, answers a symbolic bit), two
  recording tokens; the real LeanIMT at its link address; PoseidonT3 is not executed on this path.
- Mutants: LATE_MARK (nullifier marked after the payout) must fail at the assertion
  `NotMarkedAtPayout`, PAY_CALLER (pays `msg.sender`) at `PayoutArgs`. `scripts/locate.py` names the
  assertion from the `-vv` trace: the harness reads one getter before each assertion, and the last
  getter before `Panic(1)` names it (`harness/caller/assertions.tsv`). Six forge replays run both
  counterexamples concretely.

### duplicate-lock: duplicate-leaf rejection and entry rejection under the lock

- D5: a deposit whose commitment `c` is already a leaf (`leaves[c] != 0`, `0 < c < p`), every other
  deposit guard passing and the verifier accepting, reverts with exactly the 4-byte
  `LeafAlreadyExists` selector, and `svm.snapshotState()` is unchanged (no retained change to any
  account's storage, balance or code). A probe at the library address shows that the reverting call
  is `insert(_tree, c)` with the supplied `c`. With no guard premise at all (any caller, token,
  amount, funder, root, verifier answer, reentrancy status), such a deposit never succeeds.
- X1: with the reentrancy status set to ENTERED (2), deposit, transfer and withdraw revert with
  exactly `ReentrancyGuardReentrantCall()` and unchanged state, for a symbolic caller, symbolic
  arguments (token included) and symbolic storage. Every mock and the library are tripwires, so
  exact guard data excludes any external call before the revert. The same calls made by STATICCALL
  return the same data, so no state write precedes the revert. Separate, scoped observation (not the
  general property): on every successful withdraw (no tree bound) and deposit (depth 0..3), the
  status reads ENTERED at the token call.
- "Full" runs: no tree bound (size, depth, side nodes and leaves symbolic, any depth), real
  PoseidonT3 linked and not executed; proof and payload lengths 0, 1, 32, 65, 1024.
- "Band" runs: initial depth 0..3, `size <= 2^depth`, stub, `historicalRootIndex` pinned to 0,
  lengths 0 and 65.
- Loop bound 8. Mutants SKIP, ARG, DUP (library copy without the duplicate check) and NR_D, NR_T,
  NR_W (`nonReentrant` dropped); 14 forge replays. The arbitrary-calldata attempt
  (`check_X1raw_…`) must end in ERROR (`NotConcreteError`); it is a recorded tool limit.

### insert-callback: insertion, outputs order and token callbacks

- No tree bound, real PoseidonT3 (not executed): a deposit, or a transfer whose first output, is
  already a leaf reverts with `LeafAlreadyExists` and no state change (`D5a`, `T11a0`); a payout
  hook that re-enters deposit, transfer or withdraw from inside withdraw's token call always sees
  the inner call revert with the guard error (`X1_withdrawReenters…`); inside withdraw's token call
  the nullifier is already spent (`X2_withdraw…`).
- Depth 0..3, `size <= 2^depth`, stub, root index pinned to 0: second-output and equal-output
  rejection (`T11a1`, `T11c`), a second deposit of the same commitment reverts (`D5s`), deposit
  inserts its public commitment as the next leaf (`D5b`), transfer inserts its outputs in calldata
  order (`T11b`), deposit re-entry from `transferFrom` is blocked (`X1_depositReenters…`), transfer
  makes no token call (`X1_transferNoTokenCall`), and inside deposit's `transferFrom` the leaf, the
  size and the new root are already recorded (`X2_deposit…`).
- Proof and payload lengths 0 and 65; inner calls of the hooks use empty bytes. Loop bound 8.
- Mutants DUP, NR_D, NR_T, NR_W, ORD_D, ORD_W, INS_D, SWAP_T. The `X1core` checks assert only that
  the inner call did not succeed; on each NR mutant they fail, so the guard is what blocks it.

### owner-payout: the five owner functions and the withdraw payout

- G1, guard: for a symbolic owner and any other caller, each of `addSupportedToken`,
  `removeSupportedToken`, `setVerifier`, `setAttestationRegistry` and `transferOwnership` reverts with
  `OnlyOwner`, and `snapshotState` is unchanged. Tree, maps, owner, verifier and registry slots
  symbolic; reentrancy status NOT_ENTERED.
- G1, effect (run with `--storage-layout generic`): an owner call with a symbolic argument succeeds
  exactly when the stated precondition holds, then makes the stated update and leaves everything else
  unchanged: balances and code of every account, the storage of every other account, and pool
  storage at three fresh symbolic keys (any plain slot, any single-level mapping entry, any
  dynamic-array element). On revert: the stated error and no change. Nested mappings and
  struct-in-mapping shapes are not covered; the pool declares none.
- G1, sweep: any of the eight non-view functions with any arguments, from any non-owner caller,
  leaves owner, verifier, registry and `supportedTokens[y]` unchanged. Bounded: lengths 0 and 65,
  depth 0..3, stub, root index 0, one call.
- G1, events: forge fuzzing (concrete, 5000 runs per test), not Halmos: each successful owner call
  emits exactly one log with the stated signature; non-owner calls revert and emit nothing.
- W10: on every successful withdraw from a symbolic caller, one recorded `transfer(recipient,
  amount)` from the pool on the named token, and the verifier's inputs, recorded in two phases
  through storage, are `[n, t, a, rcp, r]` at full width. One token sits above `2^159`. Lengths 0 and 65;
  no tree bound.
- Loop bound 8. 22 mutants (five pay, seven public-input, five `onlyOwner`, five extra-write).

### guards: the eighteen pre-verifier guards

For each guard of deposit (`:145-149`, `:163`), transfer (`:195-204`, `:218`) and withdraw
(`:254-263`, `:275`): for every input that breaks the guard, the call reverts with the guard's
error, the verifier is not reached, and no storage, balance or code changes, even with an
accept-all verifier. Symbolic: calldata scalars, `msg.sender` (address 0 included), the nullifier,
supported-token, root-window and tree storage. Proof and payload lengths 0 and 65. Loop bound 8.
`check_spent_withdrawThenReuseRejected`: after a successful withdraw, reuse of the nullifier by
withdraw or transfer is rejected. One mutant per guard (`DEP_…`, `TR_…`, `WD_…`) must fail its
check and its core check, except that without the zero-funder guard the caller-mismatch guard still
rejects every nonzero caller (`check_core_deposit_zeroFundingAddress_nonzeroCaller` passes on that
mutant).

### ring-funding: the root ring update, the deposit funding call and the reached-history lookup

- Ring (`check_FRW_…`, `--storage-layout generic`): a fresh pool with every slot symbolic except
  verifier, registry and reentrancy status, owner symbolic, depth 0..3, stub, `historicalRootIndex`
  symbolic below 100. After one successful deposit or transfer: the selected slot holds the final
  root, the index advances to `(idx + 1) % 100`, the final root is valid, and an evicted nonzero old
  root that differs from the new root is no longer valid. Mutants M1 (the mid-transfer root is also
  recorded) and M2 (no eviction) replace `ShieldedPool.sol` in a variant project and must fail.
- Reached history (`check_RW_postOpRootsOnly`): after the concrete history deposit, deposit,
  withdraw, transfer (real PoseidonT3), `isKnownRoot(r)` holds only for the roots after each
  operation, not the mid-transfer root. Mutant M3 (inverted lookup) must fail.
- Deposit (`X2_deposit…`, `D6_successBinding`): depth 0..3, `size <= 2^depth`, stub, symbolic root
  index below 100, lengths 0 and 65. Inside `transferFrom` the leaf, size, root and ring slot are
  already recorded; on every successful deposit from a symbolic caller with an independent symbolic
  funding address, `caller == funder` and the single retained token call is
  `transferFrom(funder, pool, amount)`. Mutants D6, D6_CALLER, ORD_D.
- Loop bound 8. The mocks accept every proof; the token records calls and moves nothing.

### post-deposit-withdraw and post-transfer-admin: the postcondition fields

One check per field of the deposit, withdraw, transfer and owner-action postconditions: on every
successful call the field's statement holds (for example `known_root`: the root was the current
root or a valid root in the pre-state; `post`: without a nested call, the post-state equals the
model update of the pre-state at every plain slot and every single-level mapping entry, through one
symbolic frame probe). Both suites run with `--storage-layout generic`, loop bound 10, two solver
threads, lengths 0 and 65 (all four pairs for transfer).

- Withdraw: no tree bound, ring index symbolic in 0..99, two recording tokens (one above `2^159`).
- Deposit and transfer: initial depth 0..3, `size <= 2^depth`, stub; two inserts can reach depth 4.
- Owner actions: no restriction on tree size, depth or ring index.
- `verified` uses the two-phase storage recorder of the owner-payout suite; `guarded` attempts one
  callback per token with symbolic arguments (owner callbacks are outside the environment).
- One mutant per field (and four extra for transfer) must fail; each field has a witness.
  post-transfer-admin runs with `--panic-error-codes '*'`, as its first run did.

### root-window: the root-window and nullifier properties on the fixed contract

- Reached state (the `setUp` history: two deposits, a withdraw, a transfer), loop bound 8, default
  byte lengths, mock verifier, stub registry, stub hash: a spent nullifier is rejected by withdraw
  and transfer (P2); the nullifier is marked before the payout (P3); a payout hook that re-enters
  withdraw with a fresh unspent nullifier is stopped by the guard error, and on the NO_GUARD_W control
  the same re-entry succeeds (P3b, with a forge replay); `isKnownRoot` accepts exactly the prefix
  roots of the history (`check_P4_knownRootsOnly_reached`), and **only the post-operation roots**
  (`check_P4v1_postTxRootsOnly`): the root between the two inserts of a transfer is not accepted.
- Fresh pool, loop bound 44: P1 (spent flags stay set) and P5 (the commitment count never drops) for
  withdraw and the five owner functions at depth < 40, each with a deep witness; probes show that the
  fresh pool's owner, size, nullifiers, supported tokens and valid roots are symbolic.
- Depth cap: for any stored depth in `[256, 2^256 - 1)` deposit and transfer revert, with the root
  index pinned to 0 and with it symbolic; witnesses at depth 64 and 255 show success below the cap.
- Bands, root index pinned to 0: P1 and P5 for deposit at depth 0..7 (loop 12) and transfer at depth
  0..3 (loop 8), each with a witness at the band top.

## What the checks do not say

- Nothing about the deployed contract: [deployment/](../deployment/README.md) compares the Sepolia
  code with a build of the same sources; this package checks the source, built with fixed library
  addresses.
- Proof lengths, payload lengths and calldata other than those listed; non-canonical calldata.
- Tree depths outside each band; root indices other than 0 where pinned; other reachable states
  than the start states named; more than one call where a check makes one.
- The real Poseidon where a suite uses the stub (assumption A5 of the claim board); the production
  verifiers and proof binding; the real attestation registry; any real token: the recording tokens
  move no balances, so no check shows token receipt, fees, rebases or balance conservation.
- Owner policy: the owner-payout suite checks what the owner functions do, not who holds the key.
- Gas: unmodelled. A path that fails for gas on chain is explored here.
- Halmos itself: its EVM model, its storage model and its solvers are trusted (below). A PASS is a
  statement about Halmos's model of the bytecode.

The package never says "the contract is correct" or "verified". It says "within this scope, Halmos
0.3.3 found no counterexample, and each named mutant gives one".

## Trust base

- Halmos 0.3.3 (`halmos-0.3.3-py3-none-any.whl`, sha256 `3967291b…`), its EVM semantics, its
  symbolic storage model (injective mapping keys), its calldata generator and its loop handling,
  run on Python 3.12 (the first runs used 3.12.14). On Python 3.14 the same checks gave the same
  verdicts, but some runs explored up to half again as many paths, and one run
  (`guards/spent-mutant-TR_SPENT0`) was killed at the 8 GB cap in two of three tries; on 3.12 it
  needs 1.2 GB. `check.sh` therefore requires 3.12 (`TOOLS_UNPINNED=1` accepts another version, and
  the last line says so).
- Its solvers: yices 2.6.4 (`yices-smt2` from the `yices-solver` 2.6.4.post23 wheel, sha256
  `8b5598ac…`) for assertion queries, passed explicitly with `--solver-command`; z3 4.12.6 (the
  `z3-solver` 4.12.6.0 Python module) for branch pruning. A solver bug can turn a FAIL into a PASS.
- forge 1.8.3 (commit `cae51ad4`, binary sha256 `deb412a7…`) and solc 0.8.37+commit.f401782d
  (sha256 `5de843c2…`), as in [deployment/PINS.txt](../deployment/PINS.txt).
- The mocks, the stub and the harnesses in `harness/`: each check is only as good as its assertion
  and its mocks; the mutants and witnesses are controls against mistakes, not a proof that the
  assertion says what the scope line says.
- The pool sources: ethsystems/pocs at `a04b8b38969dfc2ee64de47edee7e396454204a8`, the submodule
  `pocs/`, exported with `git archive` of that commit, never from the working tree; every exported
  file must hash to its pinned blob id. The Solidity dependencies by the pinned `soldeer.lock`:
  three zips by sha256 and soldeer integrity, zk-kit.solidity by commit and tree id.
- Python 3 (3.11 or later), bash, git, curl, sha256sum, tar, and `systemd-run --user` when
  available (each run then gets its own scope with a memory cap; without it the runs are uncapped).

## Pins

[PINS.txt](PINS.txt) holds every pin `check.sh` reads: the pocs commit, the 14 blob ids of the
exported files and the pool's sha256, the three dependency zips and the zk-kit commit and tree,
forge, solc, halmos and the solver versions and hashes. [requirements.txt](requirements.txt) pins
every Python package of the Halmos environment by version and sha256 (from
`uv pip compile --generate-hashes`).

## Re-check

Start from a checkout of this repository with the submodule:

```
git clone --recurse-submodules https://github.com/ethsystems/shielded-pool-model.git
# or, in an existing checkout:
git submodule update --init contract-halmos/pocs
```

Install forge 1.8.3 as [deployment/README.md](../deployment/README.md) shows. Then:

```
cd contract-halmos
PYTHON=/path/to/python3.12 ./check.sh --venv   # creates .venv/ from requirements.txt (pip --require-hashes)
# expect the last line: CHECK PASS: 9 suites, <n> verdicts equal EXPECTED.tsv, ...
./check.sh caller guards     # only the named suites
```

Without `--venv`, `check.sh` installs nothing: it takes halmos from `HALMOS`, else `.venv/bin/halmos`,
else `PATH`, and the solver `yices-smt2` from the same directory. forge comes from `FORGE` or `PATH`;
solc from `SOLC`, an svm copy, or a checked download into `.deps/` (`SOLC_FETCH=0` forbids it).
`TOOLS_UNPINNED=1` accepts another build of the pinned versions (for example macOS), and the last
line says so. In order, `check.sh`:

1. checks that the halmos environment runs Python 3.12, halmos 0.3.3, the z3 module 4.12.6, yices 2.6.4 and its sha256, forge 1.8.3 at the pinned
   commit and sha256, and solc 0.8.37 and its sha256;
2. checks that `pocs/` holds `a04b8b3` and that the 14 files to export have the pinned blob ids;
3. fetches the three soldeer zips by the pinned lock (cached in `.deps/` by sha256), checks their
   sha256 and soldeer integrity, and fetches zk-kit.solidity at the lock rev and checks its tree id;
4. for each suite of `harness/SUITES.txt` (or the named ones), `scripts/setup-suite.sh` builds
   `work/<suite>/project/`: the `git archive` export and its blob check, the dependencies, the
   library-address patch, the suite's harness (and the harness of a suite its `requires.txt`
   names), the mutants from their diffs (`mutants/make.py`: strict application, sha256 against
   `MUTANTS.sha256`), and an offline build with the pinned solc; a suite with `variants.tsv` also
   gets one project per in-place mutant;
5. `scripts/run.py` runs every row of `harness/<suite>/runs.tsv`, each Halmos process in its own
   `systemd-run --user --scope` with `MemoryMax=8G` (`CAP`) when the user bus answers, killed after
   900 s (`TLIM`), and the forge replays;
6. `scripts/compare.py` compares every verdict with `EXPECTED.tsv`, names the failing assertion of
   the caller mutants, scans each log for loop-bound warnings, unknowns and OOM kills, and prints
   one `CHECK` line per verdict, a `PATHS` line per differing path count, and the last line.

Exit 0 means every verdict equals `EXPECTED.tsv`. Path counts are compared too, but a different
count alone does not fail the check: Halmos decides branch feasibility with a 1 ms solver timeout
(`--solver-timeout-branching`), so the number of explored paths depends on the machine and its
load, and `--early-exit` runs stop at the first counterexample while other paths are in flight.
`EXPECTED.tsv` keeps the counts of the first runs: one value, or a range where a first run and
its fresh rerun differed. `STRICT_PATHS=1` makes any difference fail. RESULT.md lists
every difference of the recorded run.

Cost on a Linux laptop (16 threads, 30 GB), measured 2026-10-24: 81 minutes for all nine suites
from a fresh clone, venv install included; insert-callback (21 min), post-deposit-withdraw (16 min)
and post-transfer-admin (15 min) take most of it, caller takes 36 s. The highest memory peak of a
run was 3.0 GiB. `work/` takes 1.5 GB and `.venv/` 200 MB. RESULT.md has the time and the peak of
every run.

## Layout

- `check.sh`: the check.
- `harness/<suite>/`: the Foundry test files of the suite, `runs.tsv` (one Halmos or forge run per
  row: contract, test regex, loop bound, byte lengths, environment, flags), and where needed
  `requires.txt`, `foundry-extra.txt`, `variants.tsv`, `assertions.tsv`. `harness/SUITES.txt`: the
  suites in run order.
- `mutants/<suite>/`: one unified diff per mutant file, `MUTANTS.tsv` (id, base file, diff, output,
  change) and `MUTANTS.sha256`; `mutants/make.py` applies them.
- `scripts/`: `setup-suite.sh`, `run.py`, `compare.py`, `locate.py`, `soldeer-integrity.py` (from
  `deployment/`), `foundry-libraries.txt`, `rename-map.txt`.
- `EXPECTED.tsv`: suite, run, check, verdict, path count, assertion.
- `PINS.txt`, `requirements.txt`, `RESULT.md`.
- `pocs/`: the git submodule, ethsystems/pocs at `a04b8b3`.

`work/`, `.deps/` and `.venv/` are created by `check.sh` and not tracked.

## Where it comes from

The harnesses, the mutants and the expected verdicts come from nine Halmos runs made between
2026-09-29 and 2026-10-13 on the pool at `a04b8b3`, the same file this package exports. Names were
changed: [scripts/rename-map.txt](scripts/rename-map.txt) gives the run label of each suite, as
the claim board ([../BOARD.md](../BOARD.md)) and the research-phase reports cite it, and maps each
earlier contract, test, mutant and run name to its name here. Check bodies are unchanged. Import
paths changed where the one-directory-per-suite layout moved a file, and the mutants were
regenerated from the public source with the same changes and new comments.

| Suite | First run |
|---|---|
| caller | 2026-10-13 (the withdraw-caller report of that date) |
| duplicate-lock | 2026-10-06 |
| owner-payout | 2026-10-01 |
| post-deposit-withdraw | 2026-10-01 |
| post-transfer-admin | 2026-10-01 |
| ring-funding | 2026-09-30 (the pool checks of that run) |
| guards | 2026-09-30 |
| insert-callback | 2026-09-30 |
| root-window | 2026-09-29 (rerun on the fixed contract) |

Not included:

- The first root-window run of 2026-09-16 (its report is not in this repository),
  and the depth-band and depth-40 runs of 2026-09-17 and 2026-09-18. They ran on the contract
  before its fix (one root per operation), a commit that is not public, so their input cannot be
  exported here. The counterexample of 2026-09-16 (a valid mid-transfer root) is therefore not
  reproducible from this repository. What is reproducible is its fixed form: on `a04b8b3` the same
  assertion (`check_P4v1_postTxRootsOnly`) passes and the prefix-root form passes (root-window
  suite), and the in-place mutant M1, which records the mid-transfer root again, fails the ring
  check (ring-funding suite).
- The verifier proof-length checks of the 2026-09-30 ring and funding run: they target the three
  Honk verifiers, not `ShieldedPool.sol`.
- Three extra transfer-band runs of 2026-09-29 (depth 0..7: 5 to 10 minutes and up to 5.6 GB each),
  and runs the first reports record as stopped or out of reach (a deposit band at depth 0..7 in the
  insert-callback setup, killed at 600 s).
