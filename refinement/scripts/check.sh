#!/usr/bin/env bash
# Check for the refinement package (see README.md). Needs bash, git, python3, sha256sum and elan;
# lake picks the toolchain from lean-toolchain. The first run fetches Mathlib's checkout and
# prebuilt oleans into ../.lake/packages (shared with the parent package); the fold-bridge
# stage also fetches the Lampe fork and builds part of ../circuits-lampe.
#
#   scripts/check.sh    expect the last line: CHECK PASS: ...
#
# Env: JOBS (controls and circuits-lampe modules compiled at once; default 1), LEAN_NUM_THREADS
# (default 1), FOLD_BRIDGE=0 (skip the fold-bridge stages; the last line then says so),
# CIRCUITS_LAMPE (the circuits-lampe package; default ../circuits-lampe).
#
# Stages, in order: tools; pins of the model files and of the circuits-lampe files the package
# rests on; source scan; the rename check; regeneration of the generated controls; build (lake);
# census against statements/; controls against controls/EXPECTED.tsv; then the fold bridge:
# build in the circuits-lampe workspace, its census and its controls.
set -uo pipefail
cd "$(dirname "$0")/.."
export PYTHONDONTWRITEBYTECODE=1 LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
JOBS="${JOBS:-1}"
FOLD_BRIDGE="${FOLD_BRIDGE:-1}"
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }
step() { echo "== $1 (${SECONDS}s)"; }

step tools
lv="$(lake --version 2>/dev/null)" || fail tools "lake not found (install elan)"
grep -q "Lean version 4.33.1" <<<"$lv" || fail tools "lake is '$lv', want Lean 4.33.1"
python3 -c 'import sys; assert sys.version_info >= (3, 10)' || fail tools "python3 3.10 or later needed"
echo "tools: $lv"

step pins
python3 scripts/pins.py || fail pins "a pinned file differs (PINS.sha256)"

step scan
python3 scripts/scan.py || fail scan "forbidden word (see above)"

step rename
python3 scripts/check-rename.py || fail rename "a module differs from its original in more than names and comments"

step regenerate
python3 scripts/gen-controls.py --check || fail regenerate "generated controls"

step build
mkdir -p build
lake exe cache get > build/cache.log 2>&1 || { tail -5 build/cache.log; fail build "lake exe cache get"; }
t0=$SECONDS
lake build > build/lake.log 2>&1 || { grep -E 'error' build/lake.log | head -20; fail build "lake build (build/lake.log)"; }
grep -E 'Build completed' build/lake.log
echo "build: $(find Refinement Tree Balance Journey Gas -name '*.lean' | wc -l) modules in $((SECONDS - t0))s"

step census
python3 scripts/census.py || fail census "see above"

step controls
python3 scripts/controls.py --jobs "$JOBS" > build/controls.log 2>&1; ec=$?
grep -E '^(fail|pass) ' build/controls.log; tail -1 build/controls.log
[ "$ec" -eq 0 ] || { grep '^CONTROL ' build/controls.log; fail controls "see build/controls/ and controls/EXPECTED.tsv"; }

if [ "$FOLD_BRIDGE" = 0 ]; then
  echo "CHECK PASS: pins, scan, rename check, regeneration, build, census and controls; fold bridge skipped (FOLD_BRIDGE=0) (${SECONDS}s)"
  exit 0
fi

step "fold bridge: build"
python3 scripts/build-fold-bridge.py --jobs "$JOBS" || fail fold-bridge "build (build/fold-bridge/)"

step "fold bridge: census"
python3 scripts/census.py --target fold-bridge || fail fold-bridge "census"

step "fold bridge: controls"
python3 scripts/controls.py --target fold-bridge --jobs "$JOBS" > build/controls-fold-bridge.log 2>&1; ec=$?
grep -E '^(fail|pass) ' build/controls-fold-bridge.log; tail -1 build/controls-fold-bridge.log
[ "$ec" -eq 0 ] || { grep '^CONTROL ' build/controls-fold-bridge.log; fail fold-bridge "controls (fold-bridge/controls/EXPECTED.tsv)"; }

echo "CHECK PASS: pins, scan, rename check, regeneration, build, census and controls, of the package and of the fold bridge (${SECONDS}s)"
