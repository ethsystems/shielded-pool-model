#!/usr/bin/env python3
"""Print the length bounds of the `bytes` arguments at the entry of each saved proof.

Usage: klengths.py <proofs-dir> [node-id]
For each proof directory (one per proof, as Kontrol saves them under contracts/out/proofs), prints the
path constraints of the given node (default 11, the test entry in these harnesses) that mention
`lengthBytes`, as plain prefix terms. With the stock KEVM a `bytes` argument carries
`lengthBytes(b) <= 1073741824` (2^30) and `< 2^64`; with the patched KEVM only `< 2^64`. README.md and
RESULT.md use this to show which KEVM a run used, from the graph itself.
"""
import json
import os
import sys


def show(t):
    n = t.get("node")
    if n == "KToken":
        return t["token"]
    if n == "KVariable":
        return t["name"]
    if n == "KApply":
        a = t["args"]
        return t["label"]["name"] + ("(" + ", ".join(show(x) for x in a) + ")" if a else "")
    if n == "KSequence":
        return " ~> ".join(show(x) for x in t["items"])
    return str(n)


def main() -> None:
    root = sys.argv[1]
    nid = int(sys.argv[2]) if len(sys.argv) > 2 else 11
    for d in sorted(os.listdir(root)):
        if ".setUp()" in d or not os.path.isdir(os.path.join(root, d, "kcfg")):
            continue
        f = os.path.join(root, d, "kcfg", "nodes", f"{nid}.json")
        if os.path.exists(f):
            node = json.load(open(f))
        else:
            nodes = [x for x in json.load(open(os.path.join(root, d, "kcfg", "kcfg.json")))["nodes"] if x["id"] == nid]
            if not nodes:
                print(f"{d.split('%')[-1]}\tno node {nid}")
                continue
            node = nodes[0]
        cs = [show(c) for c in node["cterm"].get("constraints", [])]
        lens = [c for c in cs if "lengthBytes" in c and ("_<Int_" in c or "_<=Int_" in c)]
        print(f"{d.split('%')[-1]}\t" + (" ; ".join(lens) or "no length constraint"))


if __name__ == "__main__":
    main()
