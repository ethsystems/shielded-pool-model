#!/usr/bin/env python3
"""Name the assertion at which a Halmos counterexample stops.

Usage: locate.py <assertions.tsv> <halmos -vv log>
Every assertion gives the same Panic(1), so the trace decides. The harness reads one getter before
each assertion, in a fixed order; the last test-level STATICCALL before the first Panic(1) revert
names the assertion through assertions.tsv (getter, assertion). Prints the name, or nothing.
"""
import re
import sys

ANSI = re.compile(r"\x1b\[[0-9;]*m")
PANIC1 = "0x4e487b71" + "0" * 63 + "1"


def main() -> None:
    table = dict(l.split("\t")[:2] for l in open(sys.argv[1]).read().splitlines()[1:] if l.strip())
    lines = ANSI.sub("", open(sys.argv[2], errors="replace").read()).splitlines()
    for i, line in enumerate(lines):
        if "REVERT " + PANIC1 in line:
            indent = len(line) - len(line.lstrip())
            for prev in reversed(lines[:i]):
                pi = len(prev) - len(prev.lstrip())
                m = re.match(r"STATICCALL \S+::(\w+)\(", prev.strip())
                if m and pi == indent + 4:
                    print(table.get(m.group(1), f"unmapped:{m.group(1)}"))
                    return
            return


if __name__ == "__main__":
    main()
