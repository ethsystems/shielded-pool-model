#!/usr/bin/env python3
"""Generate CheckInventory.lean from statements/INVENTORY.md."""
import sys
lines = open(sys.argv[1]).read().splitlines()
names = [l.split("::")[0].strip() for l in lines
         if l.strip() and not l.startswith("#") and "::" in l]
print("import LeanShieldedPool")
print("set_option pp.all true")
for n in names:
    print(f"#check @{n}")
    print(f"#print axioms {n}")
