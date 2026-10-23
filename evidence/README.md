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
| [2026-10-06-privacy-games/privacy.md](2026-10-06-privacy-games/privacy.md) | 2026-10-06 | The privacy game bounds proved in Lean, with their premises: hiding-based recipient bounds, random-oracle bounds for withdrawal, owner and sender that use no hiding premise, the commit-only bounds, and two proved counterexamples; the replay audited 1,487 declarations, 769 of them theorems | Privacy of the deployed system: every bound has premises that Poseidon is not shown to meet; interactive attackers stay open; the Lean sources are not in this repository |
| [2026-10-07-deploy-check/REPORT.md](2026-10-07-deploy-check/REPORT.md) | 2026-10-07 (amended 2026-10-11) | The deployment check (C1) on a local test chain: all 12 runtime codes equal a fresh offline build of `a04b8b3`; three planted deviations and four controls give the expected verdicts | A check of any public chain; it binds code and configuration at one block only |
| [2026-10-07-deploy-check/scripts/](2026-10-07-deploy-check/scripts/) | 2026-10-07 | The three scripts that report ran: `recheck-deploy.sh` (export, dependency check, offline build), `deploy-check.py` (compare with the chain), `soldeer-integrity.py` | A packaged check: they are copies, not wired into this repository and not run here; the test-chain fixtures and `tools/` they were run with are not copied |
| [2026-10-07-kontrol-night/REPORT.md](2026-10-07-kontrol-night/REPORT.md) | 2026-10-07 (amended 2026-10-11) | Kontrol 1.0.255: the withdraw success path passes with the token argument at any address above 0x11 except the cheatcode account, in a fixed-code environment where success exists only on two recording tokens, with one trusted bytes-prefix rewrite rule; six mutants fail (the stock proof and the mutants together: 2288 s, 6.52 GB peak); 23 of 23 forge replays pass; the symbolic-caller run and the two-symbolic-byte-string run stop | A symbolic caller, arbitrary token behaviour, or a pool result for two symbolic byte strings |
| [2026-10-13-claim-board/CLAIM1-board.md](2026-10-13-claim-board/CLAIM1-board.md) | 2026-10-13 (rows from 2026-10-02) | The 36-rule board for claim 1 (on-chain safety): 20 rows green within a stated scope (five of them Proved*), 16 assumed; its counting rule, assumption groups, conditions, and "Why not green" with one blocker per assumed row | A proof of claim 1: the claim is a target, and a green row is scoped, not deployment safety |
| [2026-10-13-findings/FINDINGS.md](2026-10-13-findings/FINDINGS.md) | 2026-10-13 | The findings register: 80 rows, one pool bug (F8), 29 errors in our own claims, 11 client defects, and the tool defects and limits, with the state of each on 2026-10-13 | Current upstream states; evidence for each row (this copy keeps only the date of each record) |
| [2026-10-13-halmos-caller/REPORT.md](2026-10-13-halmos-caller/REPORT.md) | 2026-10-13 | Halmos 0.3.3: the withdraw success path holds with a symbolic caller (154 paths); both mutants fail with concrete replays | Proof lengths other than 0, 1, 32, 65 and 1024 bytes; deposit and transfer |

## Read with care

These copies are frozen; some statements were already out of date when
they were copied:

- "No deployment outside the local test chain exists" (the claim board's
  C1 row, the deployment check's limits) was written before the first
  public test-network deployment.
- "CLAUSEMAP" and its simplification numbers are the research clause
  map. [SPEC-MAP.md](../SPEC-MAP.md) has 16 simplifications.
- Upstream states ("drafted, not posted", "open") are as of 2026-10-13.
- The contract and circuits cited are ethsystems/pocs `a04b8b3`. The
  private implementation repository's PR #16 (2026-10-08) changed the
  transfer circuit after that pin.
- Run labels (N5, D4, SYMTOK and others) name research-phase work done
  once; the glossary below says what each was. Research commit hashes
  are left as written. Paths that a report gives relative to its own
  work directory (`W/...`, `logs/...`, `bin/...`) were not copied.

## Glossary

The reports cite run labels and documents of the research phase. Each
label names work done once, on the date given; none of it reruns here.
Where this repository holds the same work, the entry says so.

Lean results over the model and the contract:

- D3: a conditional refinement of the contract to the model
  (`refineP_run`, `accepted_root_provenance`) under constructor,
  rollback, `NoSetVerifier`, `ValidRootsFresh` and `TreeAppend`
  premises, with free hash outputs.
- PATHLOCAL: the D3 refinement with path-local premises (`refinePL_run`,
  `PathFacts`, `PathTreeHyp`) in place of the global tree premises.
- N18: the abstract-hash tree and fold correspondence over the Lean
  insertion model, and the path binding theorem.
- N19: the field-to-Nat fold bridge; it composes N1's circuit fold
  equation with N18's membership-or-bad-event result.
- N11b, BALANCE: the external balance model (`Ext.credit`, `Ext.debit`,
  `NoOutsideDebit`, `TokenRollback`) and the bounds `refineB_w9` and
  `refineB_run`.
- GAS-LEMMA: a written EVM gas argument with Lean-checked arithmetic:
  under the EIP-7825 cap (2^24 gas), every canonical argument is below
  2,941,344 bytes. "The byte-length envelope (D1)" is the note of
  2026-10-01 behind it.
- Journey, NVJ: the composed withdraw journey theorem of row X3 and its
  toy instance.
- Yul proofs, "step 5", LEDGER row 7Y: Lean results over the via-IR Yul
  of the contract, about root retention.

Circuit and hash results:

- N1 (2026-10-01): under patched Lampe, the Merkle-fold equations of the
  extracted withdraw, transfer and deposit circuits, with depth bounds
  32, 32 and 20.
- Stages 2 to 8, `Stage8Rule3`, `ZcfNullifier`, "the deposit rules
  work": the source-route proofs over the Noir circuits extracted with a
  patched Lampe (the commitment, nullifier, ownership and depth
  equations of rows D4, T2, T4, T10, W3, W4 and W5). Not in this
  repository.
- "The ACIR deposit and verifier-rebuild work", `AcirLean`: the
  compiled-constraint proofs and the verifier rebuild. In this
  repository as [circuits-acir/](../circuits-acir/README.md) and
  [verifier-reproduction/](../verifier-reproduction/README.md).
- a9proto: the field-level hash agreement prototype. In this repository
  as [hash-agreement/](../hash-agreement/README.md).
- H1: the derivation of matching Poseidon parameters for Noir `hash_2`
  and Solidity `PoseidonT3`, checked on 300 input pairs and an
  eight-leaf path sequence.
- A0V: the input-0 membership repin of the model. PRIVPORT (2026-10-06):
  the port of the privacy games to the repinned model.

Contract runs, on the pool at `a04b8b3` unless the report says otherwise:

- N4: Halmos, the deposit success path with independent symbolic caller
  and funder; depth 0..3, a keccak stand-in for PoseidonT3, byte lengths
  0 and 65.
- N5, N5b (2026-10-01): Kontrol rejection proofs. N5 covers the deposit
  and transfer guards for proof and payload lengths 0..2^30; N5b the
  withdraw guards for proof lengths below 2^64, with a patched KEVM
  `abi.md`. The scope paragraph near the top of the board is theirs.
- N9b (2026-10-02): Halmos, the five owner functions of row G1.
- N12, N14: bounded tree checks at depth 0..3 with a keccak stand-in;
  N14 checks the new flag marking of row T12.
- N15b, N15c: scoped symbolic proofs of the insertion loop's storage
  effects (N15b), and the feasible concrete controls that replaced its
  withdrawn must-fail terminals (N15c).
- D2: a check that the real PoseidonT3 library is a pure function for
  canonical 68-byte delegatecalls; the stand-in results are not reproved
  over it.
- D4 (2026-10-06): Kontrol, the withdraw success path with a fixed token
  and a fixed caller (`D4Withdraw.prove_W_success`).
- SYMTOK (2026-10-06): D4 with a symbolic choice between two recording
  tokens.
- night-kontrol (2026-10-07): D4 with the token argument at any address
  above 0x11; [its report](2026-10-07-kontrol-night/REPORT.md).
- halmos-caller (2026-10-13): the same body with a symbolic caller in
  Halmos; [its report](2026-10-13-halmos-caller/REPORT.md).
- D5: Kontrol, canonical public inputs and input order observed in
  decoded mock bodies (rows S1, S2); empty deposit and transfer proofs,
  payload and withdraw proofs symbolic below 2^64.
- D5X1: Halmos, duplicate-leaf rejection and re-entry rejection with no
  tree-depth bound; byte lengths 0, 1, 32, 65 and 1024 (rows D5, X1).
- "The Halmos guard checks", "the bounded insert checks": earlier Halmos
  runs on the guards and on insertion, bytes 0 and 65, depth 0..3.
- NIGHT-LEMMAS: a K rewrite rule on byte-string prefixes, defined in the
  Kontrol report.
- TRACE: the local anvil test deployment, and its saved state, that the
  deployment check ran against.
- P1 to P5, P8: the contract properties of the Halmos root-window report.

Documents and process words:

- LEDGER: the research status ledger. Row 1 is the model theorems
  ([CLAIMS.md](../CLAIMS.md) here); row 2 the spec reading
  ([REVIEW.md](../REVIEW.md), part 5); row 3 the client; row 4 the
  circuit source under patched Lampe; row 6 the Halmos contract
  properties; row 7 exact root retention; rows 8 and 9 the privacy
  games. A1 to A13 are its assumption ids, restated in the board's
  "Conditions and assumptions".
- CLAIM1.md: the research board. Its copy is
  [CLAIM1-board.md](2026-10-13-claim-board/CLAIM1-board.md); line
  numbers in the reports refer to the original. WHY-NOT-GREEN was merged
  into it.
- CLAUSEMAP: the research clause map from spec to model;
  [SPEC-MAP.md](../SPEC-MAP.md) is its successor, with its own
  simplification numbers.
- CORRESPONDENCE.md: research notes on the contract's storage layout and
  its correspondence to the model. COVERAGE.md: a research coverage note
  with its own F1 to F9 numbering.
- "Chapter N", "section N": the research chapter log and the
  retrospective. Not included.
- Council, "Council C2", CARDS, "writeup plan v3": review and planning
  records of the research phase. A council is a writer and a reviewer
  from two model families over fixed rounds; C2 is the challenge that set
  the board's counting rule.
- Judges ("Astra judge", "Fable judge", "Claude judge", "Codex council
  reviewer"): a model of that family read the result.
  PASS-WITH-CORRECTIONS means it passed after the named corrections were
  applied. "Controller": the session that coordinated the workers.
- The private implementation repository and the private spec repository
  are named by role. The code pinned at `a04b8b3` is public in
  ethsystems/pocs; spec 2 at revision 4d4dce1 is public in
  ethsystems/specs.

## What was changed in the copies

Each Markdown copy starts with a two-line frozen banner. Numbers and
dates are unchanged. For publication:

- Pointers into the research record were removed. Where a report cited
  a record, only its date remains, as "(2026-09-30)"; the findings
  register's "Record date" column holds those dates. Links between the
  copies point to the copies.
- One third-party product name in F28 became "a provider content
  filter". Timezone offsets were removed from timestamps.
- Internal task ids, judge record ids, agent session names, research
  branch names, machine names and local paths were removed. Model family names
  (Astra, Fable, Claude, Codex) were kept.
- Private repositories are named by role. The pin `a04b8b3` is public in
  ethsystems/pocs, so it is cited there.
- Removed content: one paragraph about an unconfirmed suspicion in other
  projects, the text of F47 (an unconfirmed tool-defect suspicion), and
  the text, finder and status of F14 and F33 (PoC fixture details that the
  register marks "keep private"), all in the findings register; the harness-name table and the judge-id Evidence
  column of "Why not green" (claim board). The claim board keeps the
  sections from its header to "What is possible but expensive".
- Scripts: in `recheck-deploy.sh`, the `POCS` default path became a
  required variable and one comment names ethsystems/pocs; one comment in
  `soldeer-integrity.py` changed. No logic changed.

The repository licence section applies to these copies.
