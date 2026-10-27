#!/usr/bin/env python3
"""Read the verdicts of one kontrol prove log and the failing nodes of its saved proofs.

Usage: kverdicts.py <suite> <run> <prove-log> <proofs-dir>
Prints one tab-separated line per proof verdict in the log:
  suite, run, proof (Contract.test), verdict (PASSED, FAILED or CRASHED), failing (one entry per
  failing node: <status>:<output hex>, sorted, comma-separated; - for none), nodes (the failing node
  ids, for reading the graph; - for none), time (Kontrol's printed time).
The verdict and the "Failing nodes" list come from Kontrol's own output. The status and the exact
output bytes of each failing node come from the saved graph (<proofs-dir>/<proof id>/kcfg), because
the log prints the output bytes as text and drops the unprintable ones.
"""
import ast
import json
import os
import re
import sys


def cell(t, name):
    if isinstance(t, dict):
        if t.get("node") == "KApply" and t.get("label", {}).get("name") == name:
            return t["args"][0] if t["args"] else t
        for v in t.values():
            r = cell(v, name)
            if r is not None:
                return r
    elif isinstance(t, list):
        for v in t:
            r = cell(v, name)
            if r is not None:
                return r
    return None


def node(pd, nid):
    f = os.path.join(pd, "kcfg", "nodes", f"{nid}.json")
    if os.path.exists(f):
        return json.load(open(f))
    k = json.load(open(os.path.join(pd, "kcfg", "kcfg.json")))
    return [x for x in k["nodes"] if x["id"] == nid][0]


def show(pd, nid):
    ct = node(pd, nid)["cterm"]
    st = cell(ct, "<statusCode>")
    status = st["label"]["name"].split("_NETWORK")[0] if st and st.get("node") == "KApply" else "?"
    out = cell(ct, "<output>")
    if out and out.get("node") == "KToken":
        try:
            return status, ast.literal_eval(out["token"]).hex() or "empty"
        except Exception:
            return status, "symbolic"
    return status, "symbolic"


def main() -> None:
    suite, run, log, proofs = sys.argv[1:5]
    text = open(log, errors="replace").read()
    crashed = set(re.findall(r"Proof crashed: (\S+)", text))
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = re.search(r"PROOF (PASSED|FAILED)", lines[i])
        if not m:
            i += 1
            continue
        name, j = "", i + 1
        while j < len(lines) and "Time:" not in lines[j] and "PROOF" not in lines[j]:
            name += lines[j].strip()
            j += 1
        t = lines[j].replace("⏳", "").replace("Time:", "").strip() if j < len(lines) and "Time:" in lines[j] else "?"
        failing = []
        k = j + 1
        while k < len(lines) and "PROOF" not in lines[k]:
            fm = re.match(r"\s*Node id: (\d+)", lines[k])
            if fm:
                failing.append(int(fm.group(1)))
            if lines[k].startswith("Join the Runtime Verification"):
                break
            k += 1
        verdict = "CRASHED" if name in crashed else m.group(1)
        short = name.split("%")[-1]
        test = re.sub(r"\(.*$", "", short)
        entries = []
        pd = os.path.join(proofs, name)
        for nid in failing:
            if os.path.isdir(pd):
                st, out = show(pd, nid)
                entries.append(f"{st}:{out}")
            else:
                entries.append("?:no-graph")
        print("\t".join([suite, run, test, verdict, ",".join(sorted(entries)) or "-",
                         ",".join(map(str, sorted(failing))) or "-", t]))
        i = k


if __name__ == "__main__":
    main()
