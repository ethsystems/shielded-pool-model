#!/usr/bin/env python3
"""Check the inventory of each suite, then compare the recorded verdicts with EXPECTED.tsv.

Usage: compare.py [--inventory] <EXPECTED.tsv> <work-dir> <suite>...
  --inventory  check only the inventory (no work dir is read); check.sh runs it before any build.

EXPECTED.tsv columns: suite, run, check, verdict, paths, assertion.
- verdict: PASS, FAIL or ERROR for a Halmos check; PASS for a forge test (check = Contract.test).
- paths: the count of the frozen first run, a range lo-hi where two frozen runs of the same input
  differed, ? where the frozen record kept the verdict but not the count, or - for forge tests. Halmos decides branch feasibility with a 1 ms solver timeout, so
  a count can differ from run to run and machine to machine; a different count is reported as a
  PATHS line and counted, and fails the check only with STRICT_PATHS=1. A different verdict always fails.
- assertion: - , or the name of the assertion at which a FAIL must stop. scripts/locate.py reads it
  from the -vv trace of that run (harness/<suite>/assertions.tsv maps the trace to a name).

Inventory (a failure is an INVENTORY line, and the exit status is 1):
- runs.tsv of the suite has at least one run, and no run name twice; EXPECTED.tsv has at least one
  row for the suite and no (suite, run, check) twice; every run of runs.tsv has a row in
  EXPECTED.tsv, and every run of EXPECTED.tsv is in runs.tsv.

Comparison:
- Every recorded verdict must be expected, every expected verdict recorded. A (run, check) recorded
  twice is a mismatch. Every run of runs.tsv must have recorded verdicts and a log.
- A run is void, and each of its expected verdicts a mismatch, when its log has no SCOPE line or one
  whose rc differs from the recorded exit status, a kill ("Killed", an OOM kill, a stopped scope), a
  "[TIMEOUT]" or a Python traceback; when its exit status is not the one the expected verdicts give
  (0 when every expected verdict of the run is PASS, else 1: Halmos 0.3.3 and forge exit 1 when a
  check fails and 0 when all pass; a kill gives 137, a signal 128 + n, a crash 1 without verdicts);
  or, for a Halmos run, when the "Symbolic test result" lines do not count the recorded verdicts.
- A run log with a loop-bound warning or a solver "unknown" makes each PASS of that run a mismatch.
Exit 1 on any mismatch. The last line is SUMMARY <verdicts> <mismatches> <path differences>.
"""
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
ANSI = re.compile(r"\x1b\[[0-9;]*m")
SCAN = re.compile(r"loop unrolling bound|unrolling bound|NotConcreteError|\[TIMEOUT\]|solver returned unknown|"
                  r"Counterexample: unknown|Traceback|Killed", re.I)
FATAL = re.compile(r"\bKilled\b|\[TIMEOUT\]|^Traceback \(most recent call last\)", re.M)
RESULT_LINE = re.compile(r"^Symbolic test result: (\d+) passed; (\d+) failed", re.M)


def tsv(path: Path) -> list[list[str]]:
    """Rows of a tab-separated file without its header line and without # comments."""
    rows = [l.rstrip("\n").split("\t") for l in path.read_text().splitlines() if l.strip() and not l.startswith("#")]
    return rows[1:]


def read_expected(path: Path) -> list[list[str]]:
    rows = [l.split("\t") for l in path.read_text().splitlines()[1:] if l.strip()]
    for r in rows:
        if len(r) != 6:
            sys.exit(f"INVENTORY {path.name}: row {r} does not have 6 columns")
    return rows


def inventory(expected: list[list[str]], suites: list[str]) -> tuple[list[str], list[str]]:
    errs, notes = [], []
    keys = Counter((r[0], r[1], r[2]) for r in expected)
    errs += [f"EXPECTED.tsv names {k} {n} times" for k, n in keys.items() if n > 1]
    for suite in suites:
        def err(msg: str, suite: str = suite) -> None:
            errs.append(f"{suite}: {msg}")
        runs = [r[1] for r in tsv(PKG / "harness" / suite / "runs.tsv")]
        exp = [r for r in expected if r[0] == suite]
        if not runs:
            err("runs.tsv has no run")
        if not exp:
            err("EXPECTED.tsv has no row")
        for run, n in Counter(runs).items():
            if n > 1:
                err(f"runs.tsv names run {run} {n} times")
        exp_runs = {r[1] for r in exp}
        for run in sorted(set(runs) - exp_runs):
            err(f"run {run} of runs.tsv has no row in EXPECTED.tsv")
        for run in sorted(exp_runs - set(runs)):
            err(f"run {run} of EXPECTED.tsv is not in runs.tsv")
        notes.append(f"INVENTORY {suite}: {len(runs)} runs, {len(exp)} expected verdicts")
    return errs, notes


def main() -> None:
    args = sys.argv[1:]
    only_inventory = bool(args) and args[0] == "--inventory"
    if only_inventory:
        args = args[1:]
    exp_path, work, suites = Path(args[0]), Path(args[1]), args[2:]
    expected = read_expected(exp_path)
    if not suites:
        sys.exit("INVENTORY: no suite named")
    errs, notes = inventory(expected, suites)
    for n in notes:
        print(n)
    for e in errs:
        print(f"INVENTORY FAIL {e}")
    if only_inventory:
        sys.exit(1 if errs else 0)
    bad, paths_diff, total = len(errs), 0, 0
    strict = os.environ.get("STRICT_PATHS") == "1"
    for suite in suites:
        logs = work / suite / "logs"
        kinds = {r[1]: r[0] for r in tsv(PKG / "harness" / suite / "runs.tsv")}
        planned = list(kinds)
        exp = [r for r in expected if r[0] == suite]
        got, runs, dup = {}, {}, []
        lines = (logs / "results.tsv").read_text().splitlines() if (logs / "results.tsv").exists() else []
        for l in lines:
            s, run, check, v, p, t, wall, peak, rc, oom = l.split("\t")
            if s != suite:
                dup.append(f"results.tsv row of suite {s}")
                continue
            if (run, check) in got:
                dup.append(f"{run} {check} recorded twice ({got[(run, check)][0]}, then {v})")
            got[(run, check)] = (v, p)
            if run in runs and runs[run][:3] != (float(wall), peak, rc):
                dup.append(f"{run} recorded by two processes")
            runs[run] = (float(wall), peak, rc, oom)
        for d in dup:
            bad += 1
            print(f"CHECK DUPLICATE {suite} {d}")
        void, cut = {}, {}
        for run in planned:
            reasons = []
            if run not in runs:
                reasons.append("no recorded verdict")
            if not (logs / f"{run}.txt").exists():
                reasons.append("no log")
                void[run] = reasons
                print(f"SCAN {suite} {run}: VOID ({'; '.join(reasons)})")
                continue
            text = ANSI.sub("", (logs / f"{run}.txt").read_text(errors="replace"))
            hits = sorted({m.group(0).lower() for m in SCAN.finditer(text)})
            cut[run] = any("bound" in h or "unknown" in h for h in hits)
            reasons += sorted({m.group(0).strip() for m in FATAL.finditer(text)})
            wall, peak, rc, oom = runs.get(run, (0.0, "-", "-", "-"))
            scope = re.findall(r"^SCOPE rc=(-?\d+)", text, re.M)
            if len(scope) != 1:
                reasons.append(f"{len(scope)} SCOPE lines (a stopped scope or a killed wrapper)")
            elif scope[0] != rc:
                reasons.append(f"SCOPE rc={scope[0]}, recorded exit status {rc}")
            if oom not in ("0", "-"):
                reasons.append(f"oom_kill={oom}")
            want_rc = "0" if all(r[3] == "PASS" for r in exp if r[1] == run) else "1"
            if rc != want_rc:
                reasons.append(f"exit status {rc}, expected {want_rc}")
            vs = [v for (r, _c), (v, _p) in got.items() if r == run and v != "NONE"]
            if run in runs and not vs:
                reasons.append("no verdict in the log")
            if vs and kinds[run] == "halmos":
                counts = [tuple(map(int, m)) for m in RESULT_LINE.findall(text)]
                npass, nfail = sum(c[0] for c in counts), sum(c[1] for c in counts)
                if (npass, nfail) != (vs.count("PASS"), len(vs) - vs.count("PASS")):
                    reasons.append(f"result lines count {npass} passed, {nfail} failed; "
                                   f"{vs.count('PASS')} PASS and {len(vs) - vs.count('PASS')} other verdicts recorded")
            if reasons:
                void[run] = reasons
            print(f"SCAN {suite} {run}: wall {wall:.1f}s peak {peak} rc {rc} oom {oom} hits [{', '.join(hits)}]"
                  + (f" VOID ({'; '.join(reasons)})" if reasons else ""))
        for run in sorted(set(runs) - set(planned)):
            bad += 1
            print(f"CHECK EXTRA {suite} {run}: a run that runs.tsv does not name")
        n = 0
        for es, run, check, want, wpaths, wassert in exp:
            n += 1
            v, p = got.pop((run, check), ("MISSING", "-"))
            ok = v == want
            pok = True
            if ok and wpaths not in ("-", "?"):
                if "-" in wpaths:
                    lo, hi = map(int, wpaths.split("-"))
                    pok = p.isdigit() and lo <= int(p) <= hi
                else:
                    pok = p == wpaths
            note = ""
            if ok and run in void:
                ok, note = False, f" (run void: {'; '.join(void[run])})"
            if ok and v == "PASS" and cut.get(run):
                ok, note = False, " (log has a loop-bound warning or unknown)"
            if ok and wassert != "-":
                a = subprocess.run([sys.executable, str(PKG / "scripts" / "locate.py"), str(PKG / "harness" / suite / "assertions.tsv"),
                                    str(logs / f"{run}.txt")], capture_output=True, text=True).stdout.strip()
                ok = a == wassert
                note = f" assertion={a or 'none'}"
            total += 1
            bad += not ok
            if ok and not pok:
                paths_diff += 1
                bad += strict
                print(f"PATHS {suite} {run} {check}: {v} paths={p}, frozen run paths={wpaths}")
            print(f"CHECK {'ok' if ok else 'MISMATCH'} {suite} {run} {check}: {v} paths={p}"
                  + ("" if ok else f" expected {want} paths={wpaths}" + (f" assertion={wassert}" if wassert != "-" else "")) + note)
        for (run, check), (v, p) in sorted(got.items()):
            bad += 1
            total += 1
            n += 1
            print(f"CHECK EXTRA {suite} {run} {check}: {v} paths={p} (not in EXPECTED.tsv)")
        wall = sum(r[0] for r in runs.values())
        print(f"SUITE {suite}: {n} verdicts, {len(runs)} of {len(planned)} runs recorded, {len(void)} void, run wall {wall:.0f}s")
    print(f"SUMMARY {total} {bad} {paths_diff}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
