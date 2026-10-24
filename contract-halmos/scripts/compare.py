#!/usr/bin/env python3
"""Compare the recorded verdicts with EXPECTED.tsv.

Usage: compare.py <EXPECTED.tsv> <work-dir> <suite>...
EXPECTED.tsv columns: suite, run, check, verdict, paths, assertion.
- verdict: PASS, FAIL or ERROR for a Halmos check; PASS for a forge test (check = Contract.test).
- paths: an exact count, a range lo-hi where the count varied between runs of the same input
  (README.md says where), or - for forge tests.
- assertion: - , or the name of the assertion at which a FAIL must stop. scripts/locate.py reads it
  from the -vv trace of that run (harness/<suite>/assertions.tsv maps the trace to a name).
Every recorded verdict must be expected, every expected verdict recorded. A run log with a loop-bound
warning, an OOM kill or a solver "unknown" makes each PASS of that run a mismatch. Exit 1 on any mismatch.
"""
import re
import subprocess
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
ANSI = re.compile(r"\x1b\[[0-9;]*m")
SCAN = re.compile(r"loop unrolling bound|unrolling bound|NotConcreteError|\[TIMEOUT\]|solver returned unknown|"
                  r"Counterexample: unknown|Traceback|Killed", re.I)


def main() -> None:
    exp_path, work, suites = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3:]
    expected = [l.split("\t") for l in exp_path.read_text().splitlines()[1:] if l.strip()]
    bad = 0
    for suite in suites:
        logs = work / suite / "logs"
        got = {}
        runs = {}
        for l in (logs / "results.tsv").read_text().splitlines() if (logs / "results.tsv").exists() else []:
            s, run, check, v, p, t, wall, peak, rc, oom = l.split("\t")
            got[(run, check)] = (v, p)
            runs[run] = (float(wall), peak, rc, oom)
        scans = {}
        for run in runs:
            text = ANSI.sub("", (logs / f"{run}.txt").read_text(errors="replace"))
            hits = sorted({m.group(0).lower() for m in SCAN.finditer(text)})
            scans[run] = hits
            loop_cut = any("bound" in h for h in hits) or runs[run][3] not in ("0", "-") or any("unknown" in h for h in hits)
            scans[run] = (hits, loop_cut)
            print(f"SCAN {suite} {run}: wall {runs[run][0]:.1f}s peak {runs[run][1]} rc {runs[run][2]} oom {runs[run][3]} "
                  f"hits [{', '.join(hits)}]")
        n = 0
        for es, run, check, want, wpaths, wassert in expected:
            if es != suite:
                continue
            n += 1
            v, p = got.pop((run, check), ("MISSING", "-"))
            ok = v == want
            if ok and wpaths != "-":
                if "-" in wpaths:
                    lo, hi = map(int, wpaths.split("-"))
                    ok = p.isdigit() and lo <= int(p) <= hi
                else:
                    ok = p == wpaths
            note = ""
            if ok and v == "PASS" and run in scans and scans[run][1]:
                ok, note = False, " (log has a loop-bound warning, OOM kill or unknown)"
            if ok and wassert != "-":
                a = subprocess.run([sys.executable, str(PKG / "scripts" / "locate.py"), str(PKG / "harness" / suite / "assertions.tsv"),
                                    str(logs / f"{run}.txt")], capture_output=True, text=True).stdout.strip()
                ok = a == wassert
                note = f" assertion={a or 'none'}"
            bad += not ok
            print(f"CHECK {'ok' if ok else 'MISMATCH'} {suite} {run} {check}: {v} paths={p}"
                  + ("" if ok else f" expected {want} paths={wpaths}" + (f" assertion={wassert}" if wassert != "-" else "")) + note)
        for (run, check), (v, p) in sorted(got.items()):
            bad += 1
            n += 1
            print(f"CHECK EXTRA {suite} {run} {check}: {v} paths={p} (not in EXPECTED.tsv)")
        wall = sum(r[0] for r in runs.values())
        print(f"SUITE {suite}: {n} verdicts, {sum(1 for _ in runs)} runs, run wall {wall:.0f}s")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
