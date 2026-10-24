#!/usr/bin/env bash
# Client check (see README.md): Verus on the reviewed mirrors of the shielded-pool client at
# ethsystems/pocs a04b8b3, the mirrors against the pinned source, the negative controls, and the
# coverage arithmetic over the 110 relevant client functions. Last line: CHECK PASS or CHECK FAIL.
#   ./check.sh
# Needs bash, git, python3 (3.10+), sha256sum, unzip, rustup, the pocs submodule
# (git submodule update --init client-verus/pocs), and Verus 0.2026.09.13.671956e for x86-64 Linux.
# Env: VERUS_DIR (an unpacked verus-x86-linux release directory; default .deps/verus-x86-linux,
# unpacked from VERUS_ZIP or downloaded), VERUS_ZIP (the release zip), VERUS_FETCH=0 (never
# download), POCS (default ./pocs), JOBS (parallel Verus runs; default 4), WORK (default ./work),
# STRICT=1 (a control must fail with its recorded diagnostic; a solver resource limit does not
# count), TOOLS_UNPINNED=1 (accept a Verus or rustc build whose hashes differ from the pins; the
# versions must still match). Relative paths are taken from the caller's directory.
set -uo pipefail
CALLER="$(pwd)"
rel() { case "$1" in /*|"") printf '%s' "$1" ;; *) printf '%s/%s' "$CALLER" "$1" ;; esac; }
VERUS_DIR="$(rel "${VERUS_DIR:-}")"
VERUS_ZIP="$(rel "${VERUS_ZIP:-}")"
cd "$(dirname "$0")"
PKG="$(pwd)"
POCS="$(rel "${POCS:-$PKG/pocs}")"
WORK="$(rel "${WORK:-$PKG/work}")"
JOBS="${JOBS:-4}"
UNPINNED=""
pin() { sed -n "s/^$1 \(.*\)$/\1/p" "$PKG/PINS.txt" | head -1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }
unpinned() { [ "${TOOLS_UNPINNED:-0}" = 1 ] || fail tools "$1 (TOOLS_UNPINNED=1 accepts another build of the same version)"; UNPINNED="$UNPINNED $2"; }
hint() {
  echo "  Verus: $(pin verus_url)"
  echo "    (sha256 $(pin verus_zip_sha256)); check.sh downloads it into .deps/ unless VERUS_FETCH=0,"
  echo "    or set VERUS_ZIP=/path/to/the.zip or VERUS_DIR=/path/to/verus-x86-linux"
  echo "  Rust: rustup toolchain install $(pin rust_toolchain) --profile minimal"
}

# --- 1. tools ------------------------------------------------------------------------
command -v python3 >/dev/null || fail tools "python3 not found"
command -v rustup >/dev/null || { hint; fail tools "rustup not found"; }
if [ -z "$VERUS_DIR" ]; then
  VERUS_DIR="$PKG/.deps/verus-x86-linux"
  if [ ! -x "$VERUS_DIR/verus" ]; then
    mkdir -p "$PKG/.deps"
    if [ -z "$VERUS_ZIP" ]; then
      VERUS_ZIP="$PKG/.deps/$(basename "$(pin verus_url)")"
      if [ ! -f "$VERUS_ZIP" ] || [ "$(sha "$VERUS_ZIP")" != "$(pin verus_zip_sha256)" ]; then
        [ "${VERUS_FETCH:-1}" = 1 ] || { hint; fail tools "no Verus at $VERUS_DIR and VERUS_FETCH=0"; }
        echo "tools: downloading $(pin verus_url) ($(pin verus_zip_size) bytes)"
        curl -sSfL -o "$VERUS_ZIP.part" "$(pin verus_url)" && mv "$VERUS_ZIP.part" "$VERUS_ZIP" || fail tools "cannot download $(pin verus_url)"
      fi
    fi
    [ "$(sha "$VERUS_ZIP")" = "$(pin verus_zip_sha256)" ] || fail tools "$VERUS_ZIP has sha256 $(sha "$VERUS_ZIP"), pinned $(pin verus_zip_sha256)"
    rm -rf "$PKG/.deps/verus-x86-linux" && unzip -q "$VERUS_ZIP" -d "$PKG/.deps" || fail tools "cannot unpack $VERUS_ZIP"
    echo "tools: unpacked $VERUS_ZIP (sha256 $(pin verus_zip_sha256))"
  fi
fi
[ -x "$VERUS_DIR/verus" ] || { hint; fail tools "no verus binary in $VERUS_DIR"; }
python3 - "$VERUS_DIR/version.json" "$(pin verus_version)" "$(pin verus_commit)" <<'PY' || { hint; fail tools "Verus at $VERUS_DIR is not release $(pin verus_version)"; }
import json, sys
v = json.load(open(sys.argv[1]))['verus']
sys.exit(0 if (v['version'], v['commit']) == (sys.argv[2], sys.argv[3]) else 1)
PY
for f in verus rust_verify vstd.vir z3; do
  key="$(tr . _ <<<"$f")_sha256"
  [ "$(sha "$VERUS_DIR/$f")" = "$(pin "$key")" ] || unpinned "$f has sha256 $(sha "$VERUS_DIR/$f"), pinned $(pin "$key")" "$f"
done
"$VERUS_DIR/z3" --version | grep -qF "Z3 version $(pin z3_version)" || fail tools "z3 is not $(pin z3_version)"
TC="$(pin rust_toolchain)"
rv="$(RUSTUP_TOOLCHAIN="$TC" rustc -vV 2>&1)" || { hint; fail tools "rustup has no toolchain $TC: $rv"; }
grep -qF "commit-hash: $(pin rustc_commit)" <<<"$rv" || fail tools "rustc of $TC is not commit $(pin rustc_commit)"
drv="$(ls "$(RUSTUP_TOOLCHAIN="$TC" rustc --print sysroot)"/lib/librustc_driver-*.so 2>/dev/null | head -1)"
[ -n "$drv" ] || fail tools "no librustc_driver in the $TC sysroot"
[ "$(sha "$drv")" = "$(pin rustc_driver_sha256)" ] || unpinned "librustc_driver of $TC has sha256 $(sha "$drv"), pinned $(pin rustc_driver_sha256)" librustc_driver
echo "tools: Verus $(pin verus_version) ($VERUS_DIR), z3 $(pin z3_version), rustc $TC ($(pin rustc_commit | cut -c1-9))${UNPINNED:+; unpinned build:$UNPINNED}"

# --- 2. the mirrors against the pinned source ---------------------------------------------
[ -e "$POCS/.git" ] || fail source "no pocs checkout at $POCS (run: git submodule update --init client-verus/pocs)"
python3 "$PKG/scripts/source-check.py" "$POCS" || fail source "see the SOURCE lines above"

# --- 3. Verus: mirrors, probes, controls --------------------------------------------------
rm -rf "$WORK"; mkdir -p "$WORK"
RUSTUP_TOOLCHAIN="$TC" python3 "$PKG/scripts/verus-run.py" "$VERUS_DIR" "$WORK" "$JOBS" | tee "$WORK/verus.out" | grep -v '^VERUS ok '
[ "${PIPESTATUS[0]}" -eq 0 ] || fail verus "see the VERUS lines above and $WORK/logs/"

# --- 4. coverage --------------------------------------------------------------------------
python3 "$PKG/scripts/coverage.py" "$WORK/results.json" || fail coverage "see the COVERAGE lines above"
python3 - "$WORK/results.json" "$SECONDS" "${UNPINNED:-}" <<'PY'
import json, sys
s = json.load(open(sys.argv[1]))['summary']
rl = len(s['controls_rlimit'])
print(f"CHECK PASS: 110 functions (Verus 96 re-checked, Aeneas 22 frozen, both 8); "
      f"{s['mirrors']} mirror files, {s['verified_items']} verified items; "
      f"{s['controls_rejected']} of {s['controls']} controls rejected"
      + (f" ({rl} at the solver resource limit)" if rl else '')
      + f"; {s['probes']} probes; {sys.argv[2]}s" + (f"; unpinned build:{sys.argv[3]}" if sys.argv[3] else ''))
PY
