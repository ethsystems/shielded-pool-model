#!/usr/bin/env bash
# Check for circuits-lampe (see README.md). Needs bash, git, python3, sha256sum and elan; lake
# picks the toolchain from lean-toolchain. The first run fetches the Lampe fork, Mathlib and its
# dependencies, and Mathlib's prebuilt oleans (lake exe cache get).
#
#   scripts/check.sh    expect the last line: CHECK PASS: ...
#
# Env: JOBS (modules and controls compiled at once; default 1), LEAN_NUM_THREADS (default 1),
# POCS (a checkout of ethsystems/pocs for the circuit-source pins; default
# ../circuits-acir/pocs; the stage is skipped when it is missing).
#
# Stages, in order: tools; pins of the extracted sources (and of the circuit sources when POCS
# is there) and of the Lampe commit; source scan; the rename check; regeneration of the lookup
# certificates and of the Poseidon constants; build (the extracted packages with lake, then
# every proof module with scripts/build.py, one module per job, the flags of the original
# runs); census against statements/; controls against controls/EXPECTED.tsv.
set -uo pipefail
cd "$(dirname "$0")/.."
PKG="$(pwd)"
export PYTHONDONTWRITEBYTECODE=1 LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
JOBS="${JOBS:-1}"
pin() { sed -n "s/^# $1 \(.*\)$/\1/p" PINS.sha256 | head -1; }
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }
step() { echo "== $1 (${SECONDS}s)"; }

step tools
lv="$(lake --version 2>/dev/null)" || fail tools "lake not found (install elan)"
grep -q "Lean version 4.33.1" <<<"$lv" || fail tools "lake is '$lv', want Lean 4.33.1"
python3 -c 'import sys; assert sys.version_info >= (3, 11)' || fail tools "python3 3.11 or later needed (tomllib)"
echo "tools: $lv"

step pins
grep '  extracted/' PINS.sha256 | sha256sum --quiet --strict -c || fail pins "an extracted source differs from PINS.sha256"
listed="$(grep '  extracted/' PINS.sha256 | cut -c67- | LC_ALL=C sort)"
present="$(find extracted -name '*.lean' -not -path '*/.lake/*' | LC_ALL=C sort)"
[ "$listed" = "$present" ] || fail pins "extracted/ holds other .lean files than PINS.sha256 lists"
echo "pins: $(wc -l <<<"$present") extracted sources match"
POCS="${POCS:-$PKG/../circuits-acir/pocs}"
if [ -e "$POCS/.git" ]; then
  commit="$(pin pocs_commit)"; dir="$(pin pocs_dir)"; n=0
  while read -r sum f; do
    got="$(git -C "$POCS" cat-file blob "$commit:$dir/${f#pool/}" 2>/dev/null | sha256sum | cut -d' ' -f1)"
    [ "$got" = "$sum" ] || fail pins "$f at pocs $commit is not the pinned source"
    n=$((n + 1))
  done < <(grep '  pool/' PINS.sha256)
  echo "pins: $n circuit sources at pocs $commit match"
else
  echo "pins: no pocs checkout at $POCS; circuit-source pins not checked"
fi
rev="$(pin lampe_rev)"; repo="$(pin lampe_repo)"
form="$(python3 - "$rev" "$repo" <<'PY'
import json, pathlib, sys, tomllib
rev, repo = sys.argv[1:]
want = {'Lampe': 'Lampe', 'std-1.0.0-beta.21': 'stdlib/lampe'}
req = {r['name']: r for r in tomllib.load(open('lakefile.toml', 'rb')).get('require', [])}
man = {p['name'].strip('«»'): p for p in json.load(open('lake-manifest.json'))['packages']}
forms = set()
for name, sub in want.items():
    r, m = req.get(name), man.get(name)
    assert r is not None and m is not None, f'{name}: no require or no manifest entry'
    if 'git' in r:
        assert r['git'] == repo and r.get('rev') == rev and r.get('subDir') == sub, f'lakefile.toml {name}: {r}'
        assert m['type'] == 'git' and m['url'] == repo and m['rev'] == rev and m.get('subDir') == sub, \
            f'lake-manifest.json {name}: {m}'
        forms.add('git')
    else:
        assert r.get('path') == f'.lampe/{sub}', f'lakefile.toml {name}: {r}'
        assert m['type'] == 'path' and pathlib.Path(m['dir']).resolve() == pathlib.Path('.lampe', sub).resolve(), \
            f'lake-manifest.json {name}: {m} does not resolve to .lampe/{sub}'
        forms.add('path')
assert len(forms) == 1, 'Lampe and the stdlib are required in different forms'
print(forms.pop())
PY
)" || fail pins "the Lampe requires of lakefile.toml or lake-manifest.json are not at lampe_rev $rev"
if [ "$form" = git ]; then
  echo "pins: Lampe and its stdlib required from $repo at $rev (lakefile.toml and lake-manifest.json)"
else
  head="$(git -C .lampe rev-parse HEAD 2>/dev/null || true)"
  [ "$head" = "$rev" ] || fail pins "local Lampe checkout .lampe is at '$head', not lampe_rev $rev"
  echo "pins: local Lampe checkout at $rev (path form of lakefile.toml)"
fi

step scan
hits="$(find . -name '*.lean' -not -path '*/.lake/*' -not -path './.lampe/*' -not -path './build/*' -print0 \
  | xargs -0 grep -nE '\b(sorry|admit|native_decide|implemented_by|extern|unsafe|skipKernelTC)\b|^\s*(axiom|opaque) ' \
  | grep -v '^./scripts/' || true)"
[ -z "$hits" ] || { echo "$hits" | head -20; fail scan "forbidden word in a Lean file"; }
grep -nE 'skipKernelTC|debug\.' lakefile.toml extracted/*/lakefile.toml extracted/deps/*/lakefile.toml && fail scan "kernel option in a lakefile"
echo "scan: no sorry, admit, native_decide, axiom, opaque, extern, implemented_by, unsafe or skipKernelTC"

step rename
python3 scripts/check-rename.py || fail rename "a module differs from its original in more than names and comments"

step regenerate
T="$(mktemp -d "${TMPDIR:-/tmp}/circuits-lampe.XXXXXX")"; trap 'rm -rf "$T"' EXIT
python3 scripts/gen-lookup.py "$T" > /dev/null || fail regenerate "gen-lookup.py failed"
for ns in Deposit/VerifyLookup Deposit/ConfigLookup Deposit/HashLookup Deposit/MerkleLookup Withdraw/Lookup Transfer/Lookup; do
  diff -rq "$T/$ns" "$ns" > /dev/null && cmp -s "$T/$ns.lean" "$ns.lean" || fail regenerate "$ns differs from gen-lookup.py output"
done
echo "regenerate: 6 certificate modules (59 leaves each) equal the generator output"
python3 scripts/gen-constants3.py || fail regenerate "Poseidon constants"

step build
lake exe cache get > build-cache.log 2>&1 || { tail -5 build-cache.log; fail build "lake exe cache get"; }
rm -f build-cache.log
mkdir -p build
lake build Lampe «std-1.0.0-beta.21» «poseidon-0.0.0» «binary_merkle_root-0.0.0» «deposit-0.0.0» \
  «withdraw-0.0.0» «transfer-0.0.0» > build/lake.log 2>&1 || { tail -20 build/lake.log; fail build "lake build of Lampe and the extracted packages (build/lake.log)"; }
echo "build: Lampe, its stdlib and the extracted packages"
python3 scripts/build.py --jobs "$JOBS" > build/build.log 2>&1; ec=$?
grep -E '^(FAIL|SKIP)' build/build.log | head -20; tail -1 build/build.log
[ "$ec" -eq 0 ] || fail build "a proof module does not compile (build/logs/)"

step census
python3 scripts/census.py || fail census "see above"

step controls
python3 scripts/controls.py --jobs "$JOBS" > build/controls.log 2>&1; ec=$?
grep '^CONTROL ' build/controls.log | head -20; tail -1 build/controls.log
[ "$ec" -eq 0 ] || fail controls "see build/controls/ and controls/EXPECTED.tsv"

echo "CHECK PASS: pins, scan, rename check, regeneration, build, census and controls (${SECONDS}s)"
