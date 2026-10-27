#!/usr/bin/env python3
"""Generate the mutants of one suite from their documented diffs.

Usage: make.py <suite> <project-dir>

mutants/<suite>/MUTANTS.tsv names each mutant: id, base file, diff, output path, description.
The base is a file of the exported project (pool: contracts/src/ShieldedPool.sol; internal-leanimt
and leanimt: the zk-kit library sources under dependencies/). Each diff is a unified diff against
that base. It is applied strictly: every context and removed line must equal the base line at its
position, with no offset and no fuzz. The result must have the sha256 of mutants/<suite>/MUTANTS.sha256.
The mutants are written under <project-dir>/contracts/test/<suite>/mutants/.
"""
import hashlib
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASES = {
    "pool": "contracts/src/ShieldedPool.sol",
    "internal-leanimt": "dependencies/zk-kit-v1/packages/lean-imt/contracts/InternalLeanIMT.sol",
    "leanimt": "dependencies/zk-kit-v1/packages/lean-imt/contracts/LeanIMT.sol",
}
HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def apply(base: list[str], diff: list[str], name: str) -> list[str]:
    out, pos, i = [], 0, 0
    while i < len(diff) and not diff[i].startswith("@@"):
        i += 1
    if i == len(diff):
        sys.exit(f"{name}: no hunk")
    while i < len(diff):
        m = HUNK.match(diff[i])
        if not m:
            sys.exit(f"{name}: bad hunk header {diff[i]!r}")
        start = int(m.group(1)) - 1 if m.group(2) != "0" else int(m.group(1))
        if start < pos:
            sys.exit(f"{name}: overlapping hunks")
        out += base[pos:start]
        pos = start
        i += 1
        while i < len(diff) and not diff[i].startswith("@@"):
            line = diff[i]
            tag, text = line[:1], line[1:]
            if tag in (" ", "-"):
                if pos >= len(base) or base[pos] != text:
                    sys.exit(f"{name}: line {pos + 1} of the base is {base[pos] if pos < len(base) else 'EOF'!r}, the diff expects {text!r}")
                pos += 1
                if tag == " ":
                    out.append(text)
            elif tag == "+":
                out.append(text)
            elif line.startswith("\\"):
                pass
            else:
                sys.exit(f"{name}: bad diff line {line!r}")
            i += 1
    return out + base[pos:]


def main() -> None:
    suite, proj = sys.argv[1], Path(sys.argv[2])
    d = HERE / suite
    pins = {}
    for line in (d / "MUTANTS.sha256").read_text().splitlines():
        h, f = line.split()
        pins[f] = h
    rows = [l.split("\t") for l in (d / "MUTANTS.tsv").read_text().splitlines()[1:] if l.strip()]
    dest = proj / "contracts" / "test" / suite / "mutants"
    dest.mkdir(parents=True, exist_ok=True)
    made = set()
    for mid, base, diff, outname, _desc in rows:
        src = (proj / BASES[base]).read_text().split("\n")
        res = "\n".join(apply(src, (d / diff).read_text().split("\n")[:-1], f"{suite}/{mid}"))
        got = hashlib.sha256(res.encode()).hexdigest()
        if pins.get(outname) != got:
            sys.exit(f"{suite}/{mid}: {outname} has sha256 {got}, pinned {pins.get(outname)}")
        (dest / outname).write_text(res)
        made.add(outname)
    if made != set(pins):
        sys.exit(f"{suite}: MUTANTS.sha256 names {sorted(set(pins) - made)} that no row makes")
    print(f"mutants {suite}: {len(rows)} diffs applied, {len(made)} files, sha256 equal MUTANTS.sha256")


if __name__ == "__main__":
    main()
