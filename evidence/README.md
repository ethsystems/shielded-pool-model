# evidence

Frozen copies of reports from the research phase that came before this
repository (2026-09-14 to 2026-10-13). Each was measured once in the
research phase, on the date given, and is not rerun here. No claim in
[CLAIMS.md](../CLAIMS.md) depends on this folder. The gate does not read
it, and nothing here is a re-check. The working record behind these
reports (logs, harnesses, saved proof graphs, judge verdicts) stays
private; these copies keep the reports, their numbers and their dates.

## Files

| File | Source date | What it shows | What it does not show |
|---|---|---|---|
| [2026-09-16-halmos-root-window/REPORT.md](2026-09-16-halmos-root-window/REPORT.md) | 2026-09-16 | Halmos 0.3.3 on the pool contract before the fix in the private implementation repository's PR #12: the first root-window check (`check_P4v1_postTxRootsOnly_expectFail`) returns a counterexample root between a transfer's two inserts in 0.13 s; no-double-spend (P2) and spend-before-pay (P3) checks pass | Unbounded results: the reached-state checks cover one concrete prior state; the code is the pre-fix contract, not the pin `a04b8b3` |
| [2026-10-01-client-coverage/REPORT.md](2026-10-01-client-coverage/REPORT.md) | 2026-10-01 (run 2026-09-30) | Verus checks of 38 more client functions on reviewed mirrors, 104 negative controls failing; all 110 relevant client functions at `a04b8b3` have a selected property (Aeneas 22, Verus 96, both 8) | That the client is verified: effects and production equivalence stay unproved, and the results hold under the library assumption A3 |
| [2026-10-01-client-coverage/LEDGER-row3.md](2026-10-01-client-coverage/LEDGER-row3.md) | 2026-10-06 | The research ledger's status words, its row 3 (client) and the A3 assumption | The other ledger rows |
| [2026-10-06-privacy-games/privacy.md](2026-10-06-privacy-games/privacy.md) | 2026-10-06 | The privacy game bounds proved in Lean, with their premises: hiding-based recipient bounds, random-oracle bounds for withdrawal, owner and sender that use no hiding premise, the commit-only bounds, and two proved counterexamples; the replay audited 1,487 declarations, 769 of them theorems | Privacy of the deployed system: every bound has premises that Poseidon is not shown to meet; interactive attackers stay open; the Lean sources are not in this repository |
| [2026-10-07-deploy-check/REPORT.md](2026-10-07-deploy-check/REPORT.md) | 2026-10-07 (amended 2026-10-11) | The deployment check (C1) on a local test chain: all 12 runtime codes equal a fresh offline build of `a04b8b3`; three planted deviations and four controls give the expected verdicts | A check of any public chain; it binds code and configuration at one block only |
| [2026-10-07-deploy-check/scripts/](2026-10-07-deploy-check/scripts/) | 2026-10-07 | The three scripts that report ran: `recheck-deploy.sh` (export, dependency check, offline build), `deploy-check.py` (compare with the chain), `soldeer-integrity.py` | A packaged check: they are copies, not wired into this repository and not run here; the test-chain fixtures and `tools/` they were run with are not copied |
| [2026-10-07-kontrol-night/REPORT.md](2026-10-07-kontrol-night/REPORT.md) | 2026-10-07 (amended 2026-10-11) | Kontrol 1.0.255: the withdraw success path passes with the token argument at any address above 0x11 (2288 s, 6.52 GB), with one trusted bytes-prefix rewrite rule; six mutants fail, 23 of 23 forge replays pass; the symbolic-caller run and the two-symbolic-byte-string run stop | A symbolic caller, arbitrary token behaviour, or a pool result for two symbolic byte strings |
| [2026-10-11-lessons/lessons.md](2026-10-11-lessons/lessons.md) | 2026-10-11 | The twelve lessons of the research retrospective | The rest of the retrospective; its chapter and section numbers point into the research record |
| [2026-10-13-claim-board/CLAIM1-board.md](2026-10-13-claim-board/CLAIM1-board.md) | 2026-10-13 (rows from 2026-10-02) | The 36-rule board for claim 1 (on-chain safety): 20 rows green within a stated scope (five of them Proved*), 16 assumed; its counting rule, assumption groups, conditions, and "Why not green" with one blocker per assumed row | A proof of claim 1: the claim is a target, and a green row is scoped, not deployment safety |
| [2026-10-13-findings/FINDINGS.md](2026-10-13-findings/FINDINGS.md) | 2026-10-13 | The findings register: 80 rows, one pool bug (F8), 29 errors in our own claims, 11 client defects, and the tool defects and limits, with the state of each on 2026-10-13 | Current upstream states; evidence for each row (this copy keeps only the date of each record) |
| [2026-10-13-halmos-caller/REPORT.md](2026-10-13-halmos-caller/REPORT.md) | 2026-10-13 | Halmos 0.3.3: the withdraw success path holds with a symbolic caller (154 paths); both mutants fail with concrete replays | Proof lengths other than 0, 1, 32, 65 and 1024 bytes; deposit and transfer |

## Read with care

These copies are frozen; some statements were already out of date when
they were copied:

- "No deployment outside the local test chain exists" (the claim board's
  C1 row, the deployment check's limits) was written before the first
  public test-network deployment.
- "24 fixtures" (lesson 5) is the research gate. This repository's gate
  test plants 26 cheats ([REVIEW.md](../REVIEW.md)).
- "CLAUSEMAP" and its simplification numbers are the research clause
  map. [SPEC-MAP.md](../SPEC-MAP.md) has 16 simplifications.
- Upstream states ("drafted, not posted", "open") are as of 2026-10-13.
- The contract and circuits cited are ethsystems/pocs `a04b8b3`. The
  private implementation repository's PR #16 (2026-10-08) changed the
  transfer circuit after that pin.
- Run labels (N5, D4, D5X1, SYMTOK, PATHLOCAL, GAS-LEMMA, PRIVPORT and
  others) and research commit hashes name research-phase work and are not
  defined here. Paths that a report gives relative to its own work
  directory (`W/...`, `logs/...`, `bin/...`) were not copied.

## What was changed in the copies

Each copy starts with a two-line frozen banner. Numbers and dates are
unchanged. For publication:

- Paths into the research record became "research record, DATE".
  Links between the copies point to the copies.
- Internal task ids, judge record ids, agent session names, branch
  names, machine names and local paths were removed. Model family names
  (Astra, Fable, Claude, Codex) were kept.
- Private repositories are named by role. The pin `a04b8b3` is public in
  ethsystems/pocs, so it is cited there.
- Removed content: one paragraph about an unconfirmed suspicion in other
  projects (findings register); the text of F14, which the register
  marks "keep private"; the harness-name table and the judge-id Evidence
  column of "Why not green" (claim board). The claim board keeps the
  sections from its header to "What is possible but expensive".
- Scripts: in `recheck-deploy.sh`, the `POCS` default path became a
  required variable and one comment names ethsystems/pocs; one comment in
  `soldeer-integrity.py` changed. No logic changed.

The repository licence section applies to these copies.
