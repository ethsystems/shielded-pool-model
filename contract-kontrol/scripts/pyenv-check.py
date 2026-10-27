"""Check the Python environment that runs Halmos against requirements-halmos.txt and PINS.txt.

Usage: <python of the environment> -I pyenv-check.py <requirements-halmos.txt> <PINS.txt> [--print-pins]

- Every distribution that requirements.txt names is installed once, at its pinned version. The
  only other distribution allowed is pip (the venv's own; the runs never import it).
- Every file that the RECORD of a pinned distribution lists with a hash has that sha256 (console
  scripts excepted: check.sh runs `python -I -m halmos`, never a script in bin/). A package
  directory holds no file that its RECORD does not list (bytecode caches excepted: check.sh runs
  Python with -X pycache_prefix, so caches inside the environment are never read).
- Every entry of site-packages belongs to an installed distribution (no stray .pth file or module).
- The RECORD digest of each pinned distribution equals its pyenv_record_sha256 pin in PINS.txt. The
  digest is the sha256 of the sorted "path,hash" lines of its RECORD, without the dist-info files
  and the console scripts, so it does not depend on the install location or the installer. The
  pins are those of the Linux x86_64 wheels for CPython 3.12.

Exit 0 when all holds; 3 when only digests differ (another build of the pinned versions, for
example macOS wheels); 1 otherwise. --print-pins prints the pin lines of this environment.
"""
import base64
import hashlib
import importlib.metadata as md
import os
import re
import site
import sys
from pathlib import Path


def norm(name: str) -> str:
    return re.sub(r"[-_.]+", "-", name).lower()


def main() -> None:
    req, pins_file = Path(sys.argv[1]), Path(sys.argv[2])
    want = dict(m.groups() for m in re.finditer(r"^([A-Za-z0-9_.-]+)==(\S+)", req.read_text(), re.M))
    want = {norm(k): v for k, v in want.items()}
    pins = {}
    for m in re.finditer(r"^pyenv_record_sha256 ([0-9a-f]{64}) ([A-Za-z0-9_.-]+)==(\S+)", pins_file.read_text(), re.M):
        pins[norm(m.group(2))] = (m.group(3), m.group(1))
    fails, digests, owned, nfiles = [], {}, set(), 0
    seen = {}
    for d in md.distributions():
        n = norm(d.metadata["Name"])
        if n in seen:
            fails.append(f"{n} is installed twice ({seen[n]}, {d.version})")
        seen[n] = d.version
        owned |= {Path(str(f)).parts[0] for f in (d.files or []) if not str(f).startswith("..")}
    for n, v in sorted(want.items()):
        if seen.get(n) != v:
            fails.append(f"{n} is {seen.get(n, 'not installed')}, requirements.txt pins {v}")
    for n in sorted(set(seen) - set(want) - {"pip"}):
        fails.append(f"{n} {seen[n]} is installed but not in requirements.txt")
    if set(pins) != set(want) or any(pins[n][0] != want[n] for n in pins):
        fails.append("the pyenv_record_sha256 pins of PINS.txt do not name the versions of requirements.txt")
    for d in md.distributions():
        n = norm(d.metadata["Name"])
        if n not in want:
            continue
        scripts = {e.name for e in d.entry_points if e.group in ("console_scripts", "gui_scripts")}
        recorded, lines = set(), []
        for f in d.files or []:
            p = str(f)
            recorded.add(Path(p))
            if p.startswith("..") and Path(p).name in scripts:
                continue
            if f.hash is None:
                continue
            if not Path(p).parts[0].endswith(".dist-info"):
                lines.append(f"{p},{f.hash.mode}={f.hash.value}")
            loc = Path(d.locate_file(f))
            if not loc.is_file():
                fails.append(f"{n}: {p} is in RECORD but missing or unreadable")
                continue
            h = base64.urlsafe_b64encode(hashlib.sha256(loc.read_bytes()).digest()).rstrip(b"=").decode()
            if f"sha256={h}" != f"{f.hash.mode}={f.hash.value}":
                fails.append(f"{n}: {p} has sha256={h}, its RECORD says {f.hash.mode}={f.hash.value}")
            nfiles += 1
        digests[n] = hashlib.sha256("\n".join(sorted(lines)).encode()).hexdigest()
        base = Path(d.locate_file(""))
        for top in {Path(str(f)).parts[0] for f in d.files or [] if not str(f).startswith("..")}:
            if top.endswith(".dist-info") or top == "__pycache__" or not (base / top).is_dir():
                continue
            for root, dirs, files in os.walk(base / top):
                dirs[:] = [x for x in dirs if x != "__pycache__"]
                for x in files:
                    rel = (Path(root) / x).relative_to(base)
                    if rel not in recorded:
                        fails.append(f"{n}: {rel} is not in its RECORD")
    for sp in site.getsitepackages() + ([site.getusersitepackages()] if site.ENABLE_USER_SITE else []):
        if not Path(sp).is_dir():
            continue
        for e in sorted(os.listdir(sp)):
            if e != "__pycache__" and e not in owned:
                fails.append(f"{sp}/{e} belongs to no installed distribution")
    if "--print-pins" in sys.argv:
        for n in sorted(digests):
            print(f"pyenv_record_sha256 {digests[n]} {n}=={want[n]}")
    for f in fails:
        print(f"FAIL pyenv: {f}")
    if fails:
        sys.exit(1)
    off = [n for n in sorted(digests) if digests[n] != pins[n][1]]
    for n in off:
        print(f"UNPINNED pyenv: {n} {want[n]} RECORD digest {digests[n]}, pinned {pins[n][1]}")
    print(f"pyenv: {len(want)} distributions at the versions of requirements.txt, {nfiles} files equal their RECORD "
          f"hashes, no stray entry in site-packages; {len(want) - len(off)} of {len(want)} RECORD digests equal PINS.txt")
    sys.exit(3 if off else 0)


if __name__ == "__main__":
    main()
