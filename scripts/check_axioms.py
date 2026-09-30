#!/usr/bin/env python3
"""Compare CheckInventory output against INVENTORY.md and the axiom allowlist."""
import re, sys
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
inv = {}
for l in open(sys.argv[1]).read().splitlines():
    if l.strip() and not l.startswith("#") and "::" in l:
        name, typ = l.split("::", 1)
        inv[name.strip()] = " ".join(typ.split())
out = open(sys.argv[2]).read()
# '@name : type' lines from #check (pp.all); may wrap, so join on blank-line blocks
checks = {}
for m in re.finditer(r"^@?([\w.']+) : (.+?)(?=^\S|\Z)", out, re.M | re.S):
    checks[m.group(1)] = " ".join(m.group(2).split())
axioms = {}
for m in re.finditer(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]", out):
    axioms[m.group(1)] = {re.sub(r"\.\{[^}]*\}$", "", a.strip()) for a in m.group(2).split(",") if a.strip()}
for m in re.finditer(r"'([\w.']+)' does not depend on any axioms", out):
    axioms[m.group(1)] = set()
rc = 0
for name, typ in inv.items():
    if name not in checks:
        print(f"FAIL missing declaration or no #check output: {name}"); rc = 1; continue
    if checks[name] != typ:
        print(f"FAIL type mismatch: {name}\n  pristine: {typ}\n  actual:   {checks[name]}"); rc = 1
    if name not in axioms:
        print(f"FAIL no axiom report: {name}"); rc = 1; continue
    extra = axioms[name] - ALLOW
    if extra:
        print(f"FAIL forbidden axioms in {name}: {sorted(extra)}"); rc = 1
print("axiom/type census OK" if rc == 0 else "axiom/type census FAILED")
sys.exit(rc)
