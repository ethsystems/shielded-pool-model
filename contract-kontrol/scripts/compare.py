#!/usr/bin/env python3
"""Check the inventory, then compare the recorded verdicts and run statuses with EXPECTED.tsv.

Usage: compare.py [--inventory] <EXPECTED.tsv> <work-dir> <suite>[:<run>[,<run>...]]...
  A bare suite selects every run of harness/<suite>/runs.tsv; suite:run,... selects those runs only
  (check.sh adds the build when it selects a prove run). --inventory checks only the inventory of the
  named suites (no work dir is read); check.sh runs it before any build.

EXPECTED.tsv columns: suite, run, proof, verdict, failing, earlier.
- run: a run of harness/<suite>/runs.tsv, or for a controls or halmos run <run>-<part>, one per part
  that the run's own checker reports.
- proof: Contract.test of a Kontrol proof or a forge test, "build" for the build, the test or check
  name for a controls or halmos part, "all-checks" for the whole controls or halmos run.
- verdict: BUILT (build); PASSED or FAILED (Kontrol); PASS (forge replay); PASS, FAIL or FAIL:<reason>
  (controls, halmos).
- failing: for a FAILED proof, the failing nodes as <status>:<output hex>, sorted and comma-separated,
  exactly as scripts/kverdicts.py prints them; paths=... for a Halmos check; - otherwise.
- earlier: where the expected value comes from (a date of an earlier run, or "new"); not compared.

Inventory (a failure is an INVENTORY FAIL line, and the exit status is 1):
- runs.tsv names each run once, each of kind build, prove, forge, controls or halmos; at most one build,
  and a prove run only in a suite with a build.
- EXPECTED.tsv rows have 6 columns and no (suite, run, proof) twice. Every row belongs to a run of
  runs.tsv and every run of runs.tsv has rows. A build has the one row (build, BUILT); a prove run has
  PASSED and FAILED rows only, each FAILED row with its failing outputs; a forge run has PASS rows only;
  a controls or halmos run has its row "all-checks".
- Every mutant of mutants/<suite>/MUTANTS.tsv (id <name> or <library>_M_<name>) has a FAILED row of a
  Kontrol proof whose contract is named <...>_M_<name>, or else at least one replay row of such a
  contract; the INVENTORY line names the mutants that only a replay checks.

Comparison, per named suite:
- A selected run is void, and each of its expected verdicts a mismatch, when it has no log or no
  recorded line, or when:
  build and prove (scripts/kontrol-run.sh): the log has not exactly one "RUN start" and one "RUN end"
  line; the runner exit on the RUN end line differs from the command exit (124: timeout, 137: kill;
  a runner that gave up at its memory gate leaves no RUN end line); the command exit is not the
  expected one (build: 0, with exactly one BUILD_EXIT=0; prove: 0 when every expected verdict of the
  run is PASSED, else 1, as Kontrol exits); the log has not exactly one COMMAND_EXIT line equal to
  it; the log has a kill, a Python traceback, a crashed proof or a stopped gate; or its PROOF lines do
  not count the recorded verdicts.
  forge, controls and halmos (on the host): the log does not end with exactly one HOST_EXIT line
  (check.sh writes the exit status there at once); that exit is not the expected one (forge: 0 when
  every expected row is PASS, else 1; controls and halmos: 0 when the run's all-checks row is PASS,
  else 1); the log has a kill or a Python traceback; or, for forge, the "Ran ... tests passed"
  summary does not count the recorded PASS and FAIL lines.
- Every expected verdict of a selected run must be recorded with the same verdict and failing outputs,
  and every recorded verdict must be expected. A (run, proof) recorded twice, or a recorded line of a
  run that was not selected, is a mismatch.
- Runs of runs.tsv that the selection leaves out make the suite partial.
Exit 0 when every selected run matched and no suite is partial; 3 when every selected run matched and
some suite is partial; 1 on any mismatch or inventory failure; 2 on a usage error.
"""
import re
import sys
from collections import Counter
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
KINDS = {"build", "prove", "forge", "controls", "halmos"}
HOST = {"forge", "controls", "halmos"}
ANSI = re.compile(r"\x1b\[[0-9;]*m")
FATAL = re.compile(r"\bKilled\b|^Traceback \(most recent call last\)|Proof crashed|^RUN gate: gave up", re.M)
FORGE_SUMMARY = re.compile(r"^Ran \d+ test suites? in .*?: (\d+) tests? passed, (\d+) failed", re.M)


def rows(path: Path) -> list[list[str]]:
    """Tab-separated rows without the header line, empty lines and # comments."""
    return [l.split("\t") for l in path.read_text().splitlines()[1:] if l.strip() and not l.startswith("#")]


def plan(suite: str) -> list[tuple[str, str]]:
    """(kind, run) of each row of harness/<suite>/runs.tsv, in order."""
    return [(r[0], r[1]) for r in rows(PKG / "harness" / suite / "runs.tsv")]


def owner(run: str, kinds: dict[str, str]) -> str | None:
    """The run of runs.tsv that a recorded or expected run name belongs to."""
    if run in kinds:
        return run
    for r, k in kinds.items():
        if k in ("controls", "halmos") and run.startswith(r + "-"):
            return r
    return None


def mutant_name(mid: str) -> str:
    return mid.split("_M_")[-1]


def inventory(expected: list[list[str]], suites: list[str]) -> tuple[list[str], list[str]]:
    errs, notes = [], []
    for r in expected:
        if len(r) != 6:
            errs.append(f"EXPECTED.tsv row {r[:3]} does not have 6 columns")
    expected = [r for r in expected if len(r) == 6]
    errs += [f"EXPECTED.tsv names {k} {n} times" for k, n in Counter(tuple(r[:3]) for r in expected).items() if n > 1]
    for suite in suites:
        def err(msg: str, suite: str = suite) -> None:
            errs.append(f"{suite}: {msg}")
        p = plan(suite)
        kinds = dict((run, kind) for kind, run in p)
        for run, n in Counter(run for _, run in p).items():
            if n > 1:
                err(f"runs.tsv names run {run} {n} times")
        for kind, run in p:
            if kind not in KINDS:
                err(f"run {run} has unknown kind {kind}")
        builds = [run for kind, run in p if kind == "build"]
        if len(builds) > 1:
            err("runs.tsv has more than one build")
        if any(k == "prove" for k, _ in p) and not builds:
            err("runs.tsv has prove runs but no build")
        exp = [r for r in expected if r[0] == suite]
        by_run: dict[str, list[list[str]]] = {}
        for r in exp:
            o = owner(r[1], kinds)
            if o is None:
                err(f"EXPECTED.tsv run {r[1]} is not a run of runs.tsv")
            else:
                by_run.setdefault(o, []).append(r)
        for kind, run in p:
            rs = by_run.get(run, [])
            if not rs:
                err(f"run {run} of runs.tsv has no row in EXPECTED.tsv")
            elif kind == "build" and [(r[1], r[2], r[3]) for r in rs] != [(run, "build", "BUILT")]:
                err(f"build {run}: EXPECTED.tsv must have the one row ({run}, build, BUILT)")
            elif kind == "prove":
                for r in rs:
                    if r[1] != run or r[3] not in ("PASSED", "FAILED"):
                        err(f"prove run {run}: row {r[2]} has verdict {r[3]} (PASSED or FAILED)")
                    elif r[3] == "FAILED" and r[4] == "-":
                        err(f"prove run {run}: FAILED row {r[2]} names no failing output")
            elif kind == "forge" and any(r[1] != run or r[3] != "PASS" for r in rs):
                err(f"forge run {run}: every row must be PASS")
            elif kind in ("controls", "halmos") and not any(r[1] == run and r[2] == "all-checks" for r in rs):
                err(f"{kind} run {run}: no all-checks row")
        mf = PKG / "mutants" / suite / "MUTANTS.tsv"
        mids = [r[0] for r in rows(mf)] if mf.exists() else []
        replay_only = []
        for mid in mids:
            pat = re.compile(rf"_M_{re.escape(mutant_name(mid))}(_|\.)")
            hits = [r for r in exp if pat.search(r[2])]
            kont = [r for r in hits if kinds.get(owner(r[1], kinds) or "") == "prove" and r[3] == "FAILED"]
            if not kont and not hits:
                err(f"mutant {mid}: no row of EXPECTED.tsv checks it")
            elif not kont:
                replay_only.append(mid)
        notes.append(f"INVENTORY {suite}: {len(p)} runs, {len(exp)} expected verdicts, {len(mids)} mutants"
                     + (f" ({', '.join(replay_only)} checked by replays only)" if replay_only else ""))
    return errs, notes


def kontrol_status(kind: str, text: str, want: str, nrec: int) -> list[str]:
    reasons = []
    starts = re.findall(r"^RUN start ", text, re.M)
    ends = re.findall(r"^RUN end .*command_exit (\S+) .*runner_rc (\S+)", text, re.M)
    if len(starts) != 1 or len(ends) != 1:
        return [f"{len(starts)} RUN start and {len(ends)} RUN end lines (a runner that stopped or ran twice)"]
    ce, rc = ends[0]
    if rc != ce:
        reasons.append(f"runner exit {rc}, command exit {ce} (124: timeout, 137: kill)")
    if ce != want:
        reasons.append(f"command exit {ce}, expected {want}")
    cl = re.findall(r"^COMMAND_EXIT=(\d+)$", text, re.M)
    if cl != [ce]:
        reasons.append(f"COMMAND_EXIT lines {cl}, RUN end says {ce}")
    if kind == "build":
        bl = re.findall(r"^BUILD_EXIT=(\d+)$", text, re.M)
        if bl != ["0"]:
            reasons.append(f"BUILD_EXIT lines {bl}, expected one BUILD_EXIT=0")
    else:
        np = len(re.findall(r"PROOF (?:PASSED|FAILED)", text))
        if np != nrec:
            reasons.append(f"{np} PROOF lines, {nrec} recorded verdicts")
    return reasons


def host_status(kind: str, text: str, want: str, recorded: list[str]) -> list[str]:
    reasons = []
    lines = [l for l in text.splitlines() if l.strip()]
    hl = [l for l in lines if l.startswith("HOST_EXIT=")]
    if len(hl) != 1 or not lines or lines[-1] != hl[0]:
        return [f"{len(hl)} HOST_EXIT lines, the log must end with exactly one"]
    he = hl[0].split("=", 1)[1]
    if he != want:
        reasons.append(f"exit {he}, expected {want}")
    if kind == "forge":
        sums = FORGE_SUMMARY.findall(text)
        npass, nfail = recorded.count("PASS"), recorded.count("FAIL")
        if len(sums) != 1 or (int(sums[0][0]), int(sums[0][1])) != (npass, nfail):
            reasons.append(f"forge summary {sums}, recorded {npass} PASS and {nfail} FAIL")
    return reasons


def main() -> None:
    args = sys.argv[1:]
    only_inventory = bool(args) and args[0] == "--inventory"
    if only_inventory:
        args = args[1:]
    if len(args) < 3:
        print(__doc__.splitlines()[2], file=sys.stderr)
        sys.exit(2)
    exp_path, work, specs = Path(args[0]), Path(args[1]), args[2:]
    known = [l.split()[1] for l in (PKG / "harness" / "SUITES.txt").read_text().splitlines() if l.startswith("suite ")]
    selection: dict[str, list[str]] = {}
    for spec in specs:
        suite, _, lst = spec.partition(":")
        if suite not in known or suite in selection:
            print(f"usage: suite {suite} is unknown or named twice (harness/SUITES.txt)", file=sys.stderr)
            sys.exit(2)
        runs = [r for _, r in plan(suite)]
        sel = lst.split(",") if ":" in spec else runs
        bad = [r for r in sel if r not in runs] + [r for r, n in Counter(sel).items() if n > 1]
        if bad or not sel:
            print(f"usage: suite {suite}: unknown, repeated or no runs {bad} (runs: {', '.join(runs)})", file=sys.stderr)
            sys.exit(2)
        selection[suite] = sel
    expected = rows(exp_path)
    errs, notes = inventory(expected, list(selection))
    for n in notes:
        print(n)
    for e in errs:
        print(f"INVENTORY FAIL {e}")
    if only_inventory:
        sys.exit(1 if errs else 0)
    bad = len(errs)
    partial = []
    total = 0
    for suite, sel in selection.items():
        bad0 = bad
        p = plan(suite)
        kinds = dict((run, kind) for kind, run in p)
        logs = work / suite / "logs"
        exp = [r for r in expected if r[0] == suite]
        got: dict[tuple[str, str], tuple[str, str, str, str]] = {}
        dup = []
        res = logs / "results.tsv"
        for l in (res.read_text().splitlines() if res.exists() else []):
            f = l.split("\t")
            if len(f) != 7 or f[0] != suite:
                dup.append(f"results.tsv line {f[:3]} is malformed or of another suite")
                continue
            _s, run, proof, v, failing, nodes, t = f
            if (run, proof) in got:
                dup.append(f"{run} {proof} recorded twice")
            got[(run, proof)] = (v, failing, nodes, t)
        for d in dup:
            bad += 1
            print(f"CHECK DUPLICATE {suite} {d}")
        void = {}
        for run in sel:
            kind = kinds[run]
            mine = [r for r in exp if owner(r[1], kinds) == run]
            rec = [(k, v) for k, v in got.items() if owner(k[0], kinds) == run]
            log = logs / f"{run}.txt"
            reasons = []
            if not rec:
                reasons.append("no recorded verdict")
            if not log.exists():
                reasons.append("no log")
            else:
                text = ANSI.sub("", log.read_text(errors="replace"))
                reasons += sorted({m.group(0).strip() for m in FATAL.finditer(text)})
                if kind in ("build", "prove"):
                    want = "0" if kind == "build" or all(r[3] == "PASSED" for r in mine) else "1"
                    reasons += kontrol_status(kind, text, want, len(rec))
                else:
                    if kind == "forge":
                        want = "0" if all(r[3] == "PASS" for r in mine) else "1"
                    else:
                        want = "0" if any(r[1] == run and r[2] == "all-checks" and r[3] == "PASS" for r in mine) else "1"
                    reasons += host_status(kind, text, want, [v[0] for _, v in rec])
            if reasons:
                void[run] = reasons
            print(f"RUN {suite} {run} ({kind}): " + (f"VOID ({'; '.join(reasons)})" if reasons else "status as expected"))
        for es, run, proof, want, wfail, _earlier in exp:
            o = owner(run, kinds)
            if o not in sel:
                continue
            total += 1
            v, failing, nodes, t = got.pop((run, proof), ("MISSING", "-", "-", "-"))
            ok = v == want and (want != "FAILED" or failing == wfail) and (not wfail.startswith("paths=") or failing == wfail)
            tag = "ok  " if ok else "DIFF"
            if ok and o in void:
                ok, tag = False, "VOID"
            bad += not ok
            print(f"CHECK {tag} {suite} {run} {proof}: {v}"
                  + (f" {failing} (nodes {nodes})" if v == "FAILED" else "")
                  + ("" if ok or tag == "VOID" else f"; expected {want}" + (f" {wfail}" if want == "FAILED" else ""))
                  + (f" [{t}]" if t not in ("-", "?") else ""))
        for (run, proof), (v, failing, nodes, t) in sorted(got.items()):
            bad += 1
            o = owner(run, kinds)
            why = "not in EXPECTED.tsv" if o in sel else "a run that was not selected"
            print(f"CHECK DIFF {suite} {run} {proof}: {v} {failing}, {why}")
        left = [r for _, r in p if r not in sel]
        status = "FAIL" if bad > bad0 else ("PARTIAL" if left else "PASS")
        if left:
            partial.append(f"{suite}: ran {', '.join(sel)}; not selected {', '.join(left)}")
        print(f"CHECK {status} suite {suite}" + (f" (ran {', '.join(sel)}; not selected {', '.join(left)})" if left else "")
              + (f" ({len(void)} void runs)" if void else ""))
    print(f"SUMMARY {total} expected verdicts, {bad} mismatches, {len(partial)} partial suites")
    if bad:
        sys.exit(1)
    sys.exit(3 if partial else 0)


if __name__ == "__main__":
    main()
