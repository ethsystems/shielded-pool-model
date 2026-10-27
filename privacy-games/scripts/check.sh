#!/usr/bin/env bash
# Check for privacy-games (see README.md). Needs bash, git, python3 (3.11 or later), sha256sum
# and elan; lake picks the toolchain from lean-toolchain. The first run fetches VCV-io, Mathlib
# and their dependencies, and Mathlib's prebuilt oleans (lake exe cache get); it builds VCV-io's
# modules that the games import from source.
#
#   scripts/check.sh    expect the last line: CHECK PASS: ...
#
# Env: JOBS (controls compiled at once; default 1), LEAN_NUM_THREADS (default 2; lake also
# runs this many jobs at once).
#
# Stages, in order: tools; pins (lakefile, manifest, model files, and the checkouts already
# fetched); source scan; the rename check; fetch (lake exe cache get) and the pins of every
# fetched checkout; build (lake build, no warning allowed in a package module); census against
# statements/; controls against controls/EXPECTED.tsv; the pins of the checkouts once more.
set -uo pipefail
# The helper scripts validate with assert statements, which PYTHONOPTIMIZE would strip.
unset PYTHONOPTIMIZE
cd "$(dirname "$0")/.."
export PYTHONDONTWRITEBYTECODE=1 LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
JOBS="${JOBS:-1}"
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }
step() { echo "== $1 (${SECONDS}s)"; }
mkdir -p build

step tools
lv="$(lake --version 2>/dev/null)" || fail tools "lake not found (install elan)"
grep -q "Lean version 4.33.1" <<<"$lv" || fail tools "lake is '$lv', want Lean 4.33.1"
python3 -c 'import sys; assert sys.version_info >= (3, 11)' || fail tools "python3 3.11 or later needed"
git --version > /dev/null || fail tools "git not found"
echo "tools: $lv"

step pins
python3 scripts/pins.py || fail pins "see above"

step scan
hits="$(find . -path ./.lake -prune -o -path ./build -prune -o -name '*.lean' -print0 | xargs -0 grep -nE \
  '\b(sorry|admit|native_decide|implemented_by|extern|unsafe|skipKernelTC)\b|^\s*(axiom|opaque) |decide \+native|Lean\.ofReduceBool' \
  || true)"
[ -z "$hits" ] || { echo "$hits" | head -20; fail scan "forbidden word in a Lean file"; }
grep -nE 'skipKernelTC|debug\.' lakefile.toml && fail scan "kernel option in lakefile.toml"
n="$(find . -path ./.lake -prune -o -path ./build -prune -o -name '*.lean' -print | wc -l)"
echo "scan: $n Lean files (the model files are scanned by the gate); no sorry, admit, native_decide, axiom, opaque, extern, implemented_by, unsafe or skipKernelTC"

step rename
python3 scripts/check-rename.py || fail rename "a module differs from its first form in more than names and comments"

step fetch
lake exe cache get > build/cache.log 2>&1 || { tail -5 build/cache.log; fail fetch "lake exe cache get (build/cache.log)"; }
echo "fetch: $(tail -1 build/cache.log)"
python3 scripts/pins.py --fetched || fail pins "see above"

step build
t0=$SECONDS
lake build > build/lake.log 2>&1 || { grep -E 'error' build/lake.log | head -20; fail build "lake build (build/lake.log)"; }
warn="$(grep -E 'warning:' build/lake.log | grep -v '\.lake/packages' || true)"
[ -z "$warn" ] || { echo "$warn" | head -10; fail build "a warning in a package module"; }
echo "build: $(tail -1 build/lake.log) ($((SECONDS - t0))s)"

step census
t0=$SECONDS
census="$(python3 scripts/census.py)"; ec=$?
echo "$census"
[ "$ec" -eq 0 ] || fail census "see above"
echo "census: $((SECONDS - t0))s"

step controls
t0=$SECONDS
python3 scripts/gen-controls.py --check || fail controls "controls/ differs from scripts/gen-controls.py"
python3 scripts/controls.py --jobs "$JOBS" > build/controls.log 2>&1; ec=$?
grep '^CONTROL BAD' build/controls.log | head -20; tail -1 build/controls.log
[ "$ec" -eq 0 ] || fail controls "see build/controls.log, build/controls/ and controls/EXPECTED.tsv"
echo "controls: $((SECONDS - t0))s"

step "pins after the build and the controls"
python3 scripts/pins.py --fetched || fail pins "see above"

counts="$(sed -n 's/^CENSUS PASS: \([0-9]*\) modules, \([0-9]*\) declarations, \([0-9]*\) theorems written.*/\1 modules, \2 declarations, \3 theorems/p' <<<"$census")"
ctl="$(tail -1 build/controls.log | sed -n 's/^CONTROLS PASS: \([0-9]*\) planted.*/\1 planted failures rejected/p')"
echo "CHECK PASS: pins, scan, rename check, build, census ($counts; standard axioms only) and controls ($ctl) (${SECONDS}s)"
