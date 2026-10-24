#!/usr/bin/env python3
"""Run every row of harness/<suite>/runs.tsv in a built project and record each verdict.

Usage: run.py <suite> <project-dir> <log-dir>
       run.py --preflight      check what the runner needs, print the runner line, run nothing
Env: HALMOS (the halmos 0.3.3 executable), YICES (the yices-smt2 binary), SOLC, CAP (memory cap of
each run, default 8G), TLIM (seconds, default 900), RUN_SCOPE (auto, 1 or 0: run each process in its
own systemd user scope with MemoryMax=CAP; auto uses one when the scope probe works), ONLY (a
regex on run names, for debugging; check.sh never sets it).

The runner needs Linux, bash, and GNU coreutils timeout (each run is killed after TLIM seconds) on
PATH. A scope also needs systemd-run --user and cgroup v2 with memory.peak (Linux 5.19 or later),
read through /proc/self/cgroup and /sys/fs/cgroup. The probe runs one scope with the same settings
and reads those files; RUN_SCOPE=1 fails if it does not work, auto falls back to no scope (runs are
not memory-capped, the peak is the largest child RSS so far) and says so. Without a scope an OOM kill
shows only as exit status 137, which compare.py counts as a mismatch.

runs.tsv columns: kind, run, contract, test regex (or test file for kind forge), loop, byte lengths
(or - for Halmos's default), env (K=V,K=V or -), extra flags (or -). Every halmos run gets the same base command:
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


PROBE = ("cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); "
         "echo \"peak_bytes=$(cat $cg/memory.peak) oom_kill=$(grep -E '^oom_kill ' $cg/memory.events | cut -d' ' -f2)\"")


def need(cond: bool, msg: str) -> None:
    if not cond:
        sys.exit(f"FAIL runner: {msg}")


def preflight() -> tuple[bool, str]:
    """Check the runner's tools; return (use a scope, the runner line)."""
    need(sys.platform.startswith("linux"), f"the runner needs Linux (this is {sys.platform})")
    for t in ("bash", "timeout", "cut", "grep", "cat"):
        need(shutil.which(t) is not None, f"{t} not found on PATH (the runner needs bash and GNU coreutils)")
    need(subprocess.run(["timeout", "-s", "KILL", "5", "true"], capture_output=True).returncode == 0,
         "timeout -s KILL 5 true fails (the runner needs GNU coreutils timeout)")
    cap, tlim = os.environ.get("CAP", "8G"), os.environ.get("TLIM", "900")
    mode = os.environ.get("RUN_SCOPE", "auto")
    need(mode in ("auto", "0", "1"), f"RUN_SCOPE={mode}, expected auto, 1 or 0")
    why = "RUN_SCOPE=0"
    if mode != "0":
        if shutil.which("systemd-run") is None:
            why = "systemd-run not found"
        else:
            p = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={cap}", "-p", "MemorySwapMax=512M",
                                "bash", "-c", PROBE], capture_output=True, text=True)
            if p.returncode == 0 and re.fullmatch(r"peak_bytes=\d+ oom_kill=\d+\n", p.stdout):
                return True, f"runner: one systemd user scope per run, MemoryMax={cap}, MemorySwapMax=512M, killed after {tlim} s"
            last = ((p.stderr or p.stdout).strip().splitlines() or ["no output"])[-1]
            why = f"the scope probe failed: {last}"
        need(mode != "1", f"RUN_SCOPE=1 but {why}")
    return False, f"runner: NO scope ({why}): runs are not memory-capped, peaks are child RSS; killed after {tlim} s"


def main() -> None:
    if sys.argv[1:] == ["--preflight"]:
        print(preflight()[1])
        return
    suite, proj, logs = sys.argv[1], Path(sys.argv[2]).resolve(), Path(sys.argv[3]).resolve()
    logs.mkdir(parents=True, exist_ok=True)
    halmos, yices = os.environ["HALMOS"], os.environ["YICES"]
    cap, tlim = os.environ.get("CAP", "8G"), os.environ.get("TLIM", "900")
    only = re.compile(os.environ["ONLY"]) if os.environ.get("ONLY") else None
    use_scope, line = preflight()
    print(f"{suite}: {line}", flush=True)
    rows = [l.rstrip("\n").split("\t") for l in (PKG / "harness" / suite / "runs.tsv").read_text().splitlines()
            if l.strip() and not l.startswith("#")][1:]
    res = (logs / "results.tsv").open("a")
    for kind, run, contract, regex, loop, nbytes, envs, flags in rows:
        if only and not only.search(run):
            continue
        env = dict(os.environ, FOUNDRY_OFFLINE="true", FOUNDRY_SOLC=os.environ["SOLC"], FOUNDRY_LINT_LINT_ON_BUILD="false")
        if envs != "-":
            env.update(kv.split("=", 1) for kv in envs.split(","))
        # PROJECT=<variant> selects the variant project <project>-<variant> (scripts/setup-suite.sh).
        wd = Path(f"{proj}-{env.pop('PROJECT')}") if envs != "-" and "PROJECT=" in envs else proj
        if kind == "halmos":
            cmd = [halmos, "--root", str(wd), "--contract", contract, "--match-test", regex, "--loop", loop,
                   "--solver-timeout-assertion", "60s"]
            cmd += [] if nbytes == "-" else ["--default-bytes-lengths", nbytes]
            cmd += ["--solver-command", f"{yices} --smt2-model-format --bvconst-in-decimal"]
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
            rc = subprocess.run(wrap, cwd=wd, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
            wall = time.time() - t0
        text = ANSI.sub("", out.read_text(errors="replace"))
        m = re.search(r"^SCOPE rc=(\d+)(?: peak_bytes=(\d+) oom_kill=(\d+))?", text, re.M)
        peak = m.group(2) if m and m.group(2) else str(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024) + "~rss"
        oom = m.group(3) if m and m.group(3) else "-"
        if use_scope and not m:
            # No SCOPE line: systemd stopped the scope (an OOM kill stops the whole unit).
            oom = "killed"
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
