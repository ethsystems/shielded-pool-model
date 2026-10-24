#!/usr/bin/env python3
"""Compare the recorded verdicts with EXPECTED.tsv.

Usage: compare.py <EXPECTED.tsv> <work-dir> <suite>...
EXPECTED.tsv columns: suite, run, proof, verdict, failing, earlier.
- proof: Contract.test of a Kontrol proof, "build" for the build, or Contract.test of a forge replay.
- verdict: PASSED or FAILED (Kontrol), BUILT (build), PASS (forge replay).
- failing: for a FAILED proof, the failing nodes as <status>:<output hex>, sorted and comma-separated,
  exactly as scripts/kverdicts.py prints them; - otherwise.
- earlier: where the expected value comes from (a date of the earlier run, or "new"); not compared.
Each prove run named in harness/<suite>/runs.tsv either ran, and then every expected line of that run
must be recorded with the same verdict and failing outputs and nothing else may be recorded, or was
not selected on the command line, and then the suite result says "partial". Exit 1 on any mismatch.
"""
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent


def main() -> None:
    exp_path, work, suites = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3:]
    expected = [l.split("\t") for l in exp_path.read_text().splitlines()[1:] if l.strip() and not l.startswith("#")]
    bad_total = 0
    for suite in suites:
        res = work / suite / "logs" / "results.tsv"
        got = {}
        for l in res.read_text().splitlines() if res.exists() else []:
            s, run, proof, v, failing, nodes, t = l.split("\t")
            got[(run, proof)] = (v, failing, nodes, t)
        runs_ran = {r for r, _ in got}
        planned = [l.split("\t")[1] for l in (PKG / "harness" / suite / "runs.tsv").read_text().splitlines()[1:] if l.strip()]
        skipped = [r for r in planned if r not in runs_ran]
        bad = 0
        for es, run, proof, want, wfail, earlier in expected:
            if es != suite or run not in runs_ran:
                continue
            v, failing, nodes, t = got.pop((run, proof), ("MISSING", "-", "-", "-"))
            ok = v == want and (want != "FAILED" or failing == wfail) and (not wfail.startswith("paths=") or failing == wfail)
            bad += not ok
            print(f"CHECK {'ok  ' if ok else 'DIFF'} {suite} {run} {proof}: {v}"
                  + (f" {failing} (nodes {nodes})" if v == "FAILED" else "")
                  + ("" if ok else f"; expected {want}" + (f" {wfail}" if want == "FAILED" else ""))
                  + (f" [{t}]" if t not in ("-", "?") else ""))
        for (run, proof), (v, failing, nodes, t) in sorted(got.items()):
            bad += 1
            print(f"CHECK DIFF {suite} {run} {proof}: {v} {failing}, not in EXPECTED.tsv")
        bad_total += bad
        part = f" (partial: not run {', '.join(skipped)})" if skipped else ""
        print(f"CHECK {'PASS' if bad == 0 else 'FAIL'} suite {suite}{part}")
    sys.exit(1 if bad_total else 0)


if __name__ == "__main__":
    main()
