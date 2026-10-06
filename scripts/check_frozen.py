#!/usr/bin/env python3
"""Check the frozen surface against a pins file (sha256sum format).

Usage: check_frozen.py <pins-file> <tree-root>
       check_frozen.py --write <pins-file> <tree-root>

Every file matching FROZEN must be pinned, every pinned file must exist,
and every hash must match. The census checks theorem types; these pins
also freeze the bodies of the statement definitions. Rewrite the pins only
as a deliberate, reviewed change: git log statements/FROZEN.sha256 is the
change log of the frozen surface.
"""
import hashlib
import pathlib
import sys

FROZEN = [
    "LeanShieldedPool.lean",
    "LeanShieldedPool/Pool/*.lean",
    "LeanShieldedPool/Statements/*.lean",
    "LeanShieldedPool/Proofs/*.lean",
    "LeanShieldedPool/Extensions/*.lean",
    "LeanShieldedPool/Draft/NonVacuity.lean",
    "statements/INVENTORY.md",
    "controls/*.lean",
    "AXIOMS.md",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "scripts/gate.sh",
    "scripts/gate_test.sh",
    "scripts/mk_check.py",
    "scripts/check_axioms.py",
    "scripts/check_frozen.py",
]


def frozen_files(root):
    return sorted({p.relative_to(root).as_posix()
                   for g in FROZEN for p in root.glob(g) if p.is_file()})


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main(argv):
    write = argv[:1] == ["--write"]
    if write:
        argv = argv[1:]
    pins_path, root = pathlib.Path(argv[0]), pathlib.Path(argv[1])
    files = frozen_files(root)
    if write:
        pins_path.write_text("".join(f"{digest(root / f)}  {f}\n" for f in files))
        print(f"wrote {len(files)} pins to {pins_path}")
        return 0
    pins = {}
    for line in pins_path.read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            h, p = line.split(None, 1)
            pins[p.strip()] = h
    bad = [f"unpinned: {f}" for f in files if f not in pins]
    bad += [f"missing: {p}" for p in pins if not (root / p).is_file()]
    bad += [f"changed: {p}" for p in pins
            if (root / p).is_file() and digest(root / p) != pins[p]]
    for b in bad:
        print(b)
    if bad:
        return 1
    print(f"frozen surface OK ({len(pins)} files)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
