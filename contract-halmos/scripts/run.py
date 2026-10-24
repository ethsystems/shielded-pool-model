#!/usr/bin/env python3
"""Run every row of harness/<suite>/runs.tsv in a built project and record each verdict.

Usage: run.py <suite> <project-dir> <log-dir>
Env: HALMOS (the halmos 0.3.3 executable), YICES (the yices-smt2 binary), SOLC, CAP (memory cap of
each run, default 8G), TLIM (seconds, default 900), RUN_SCOPE (auto, 1 or 0: run each process in its
own systemd user scope with MemoryMax=CAP; auto uses one when systemd-run --user works), ONLY (a
regex on run names, for debugging; check.sh never sets it).

runs.tsv columns: kind, run, contract, test regex (or test file for kind forge), loop, byte lengths,
env (K=V,K=V or -), extra flags (or -). Every halmos run gets the same base command:
  halmos --root <project> --contract C --match-test RE --loop L --solver-timeout-assertion 60s
         --default-bytes-lengths B --solver-command "<yices-smt2> --smt2-model-format --bvconst-in-decimal" [flags]
Writes <log-dir>/<run>.txt (the raw output) and appends one line per verdict to <log-dir>/results.tsv:
suite, run, check, verdict, paths, halmos seconds, wall seconds, peak bytes, exit status.
"""
import os
import re
import resource
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
ANSI = re.compile(r"\x1b\[[0-9;]*m")
VERDICT = re.compile(r"^\[(PASS|FAIL|TIMEOUT|ERROR)\] ([A-Za-z0-9_]+)\(.*?\(paths: (\d+), time: ([0-9.]+)s", re.M)
FORGE = re.compile(r"^\[(PASS|FAIL)[^\]]*\] ([A-Za-z0-9_]+)\(", re.M)
SUITE_HDR = re.compile(r"^Ran \d+ tests? for [^:]+:(\w+)", re.M)


def scope_ok() -> bool:
    mode = os.environ.get("RUN_SCOPE", "auto")
    if mode == "0":
        return False
    ok = shutil.which("systemd-run") is not None and subprocess.run(
        ["systemd-run", "--user", "--scope", "-q", "true"], capture_output=True).returncode == 0
    if mode == "1" and not ok:
        sys.exit("RUN_SCOPE=1 but systemd-run --user --scope does not work here")
    return ok


def main() -> None:
    suite, proj, logs = sys.argv[1], Path(sys.argv[2]).resolve(), Path(sys.argv[3]).resolve()
    logs.mkdir(parents=True, exist_ok=True)
    halmos, yices = os.environ["HALMOS"], os.environ["YICES"]
    cap, tlim = os.environ.get("CAP", "8G"), os.environ.get("TLIM", "900")
    only = re.compile(os.environ["ONLY"]) if os.environ.get("ONLY") else None
    use_scope = scope_ok()
    rows = [l.rstrip("\n").split("\t") for l in (PKG / "harness" / suite / "runs.tsv").read_text().splitlines()
            if l.strip() and not l.startswith("#")][1:]
    res = (logs / "results.tsv").open("a")
    for kind, run, contract, regex, loop, nbytes, envs, flags in rows:
        if only and not only.search(run):
            continue
        env = dict(os.environ, FOUNDRY_OFFLINE="true", FOUNDRY_SOLC=os.environ["SOLC"], FOUNDRY_LINT_LINT_ON_BUILD="false")
        if envs != "-":
            env.update(kv.split("=", 1) for kv in envs.split(","))
        if kind == "halmos":
            cmd = [halmos, "--root", str(proj), "--contract", contract, "--match-test", regex, "--loop", loop,
                   "--solver-timeout-assertion", "60s", "--default-bytes-lengths", nbytes,
                   "--solver-command", f"{yices} --smt2-model-format --bvconst-in-decimal"]
            cmd += [] if flags == "-" else shlex.split(flags)
        elif kind == "forge":
            cmd = ["forge", "test", "--offline", "--match-path", f"contracts/test/{suite}/{regex}"]
            cmd += [] if flags == "-" else shlex.split(flags)
        else:
            sys.exit(f"{suite}/{run}: unknown kind {kind}")
        out = logs / f"{run}.txt"
        inner = "ulimit -c 0; timeout -s KILL \"$0\" \"$@\"; rc=$?; "
        if use_scope:
            inner += ("cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); "
                      "echo \"SCOPE rc=$rc peak_bytes=$(cat $cg/memory.peak) oom_kill=$(grep -E '^oom_kill ' $cg/memory.events | cut -d' ' -f2)\"; ")
        else:
            inner += "echo \"SCOPE rc=$rc\"; "
        inner += "exit $rc"
        wrap = ["bash", "-c", inner, tlim] + cmd
        if use_scope:
            wrap = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={cap}", "-p", "MemorySwapMax=512M"] + wrap
        with out.open("w") as f:
            f.write("CMD " + shlex.join(cmd) + "\n" + ("ENV " + envs + "\n"))
            f.flush()
            t0 = time.time()
            rc = subprocess.run(wrap, cwd=proj, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
            wall = time.time() - t0
        text = ANSI.sub("", out.read_text(errors="replace"))
        m = re.search(r"^SCOPE rc=(\d+)(?: peak_bytes=(\d+) oom_kill=(\d+))?", text, re.M)
        peak = m.group(2) if m and m.group(2) else str(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024) + "~rss"
        oom = m.group(3) if m and m.group(3) else "-"
        if kind == "halmos":
            found = [(n, v, p, t) for v, n, p, t in VERDICT.findall(text)]
        else:
            found, cur = [], None
            for line in text.splitlines():
                h = SUITE_HDR.match(line)
                if h:
                    cur = h.group(1)
                g = FORGE.match(line)
                if g and cur:
                    found.append((f"{cur}.{g.group(2)}", g.group(1), "-", "-"))
        if not found:
            found = [("-", "NONE", "-", "-")]
        for name, v, p, t in found:
            res.write(f"{suite}\t{run}\t{name}\t{v}\t{p}\t{t}\t{wall:.1f}\t{peak}\t{rc}\t{oom}\n")
        res.flush()
        print(f"run {suite}/{run}: wall {wall:.1f}s peak {peak} rc {rc}: "
              + "; ".join(f"{v} {n} ({p})" for n, v, p, _ in found), flush=True)
    res.close()


if __name__ == "__main__":
    main()
