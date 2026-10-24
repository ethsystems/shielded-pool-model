#!/usr/bin/env bash
# Halmos checks of ShieldedPool.sol at ethsystems/pocs a04b8b3 (see README.md). Needs Linux, bash,
# git, python3, curl, sha256sum, tar, GNU coreutils timeout, the pocs submodule (git -C contract-halmos
# submodule update --init pocs), forge 1.8.3, solc 0.8.37, and halmos 0.3.3 with its solvers (--venv
# makes one); systemd-run --user for the memory caps (scripts/run.py).
#   ./check.sh [--venv] [suite...]   build each suite from a fresh export of the pin, run every
#                                    Halmos check and mutant of harness/<suite>/runs.tsv and the
#                                    forge replays, compare with EXPECTED.tsv; last line CHECK PASS|FAIL
#   --venv  create .venv/ with python3 -m venv and install requirements.txt with pip
#           --require-hashes (downloads from PyPI), unless .venv/ exists; without it check.sh never
#           installs anything and takes halmos from HALMOS, else .venv/bin/halmos, else PATH.
#           Either way scripts/pyenv-check.py checks the environment against requirements.txt and
#           the RECORD pins of PINS.txt, and Halmos runs as <its python> -I -m halmos.
# Env: HALMOS, PYTHON (the Python 3.12 that --venv uses; default python3.12 from PATH), FORGE (default: from PATH), SOLC (solc 0.8.37; default: the svm copy, else a download
# into DEPS_CACHE), POCS (default ./pocs), DEPS_CACHE (default ./.deps), SOLC_FETCH=0 (never
# download solc), TOOLS_UNPINNED=1 (accept a forge, solc or yices binary whose sha256 is not the
# pinned Linux x86_64 build, or a Python environment whose RECORD digests differ from PINS.txt; its
# versions must still match), CAP (memory cap per run, default 8G),
# TLIM (seconds per run, default 900), RUN_SCOPE (auto|1|0, see scripts/run.py), WORK (default ./work),
# STRICT_PATHS=1 (a path count that differs from EXPECTED.tsv fails the check; see scripts/compare.py).
# Relative paths are taken from the caller's directory.
set -uo pipefail
CALLER="$(pwd)"
rel() { case "$1" in /*|"") printf '%s' "$1" ;; *) printf '%s/%s' "$CALLER" "$1" ;; esac; }
FORGE="$(rel "${FORGE:-$(command -v forge || true)}")"
[ -z "${SOLC:-}" ] || SOLC="$(rel "$SOLC")"
[ -z "${HALMOS:-}" ] || HALMOS="$(rel "$HALMOS")"
cd "$(dirname "$0")"
PKG="$(pwd)"
POCS="$(rel "${POCS:-$PKG/pocs}")"
DEPS_CACHE="$(rel "${DEPS_CACHE:-$PKG/.deps}")"
WORK="$(rel "${WORK:-$PKG/work}")"
UNPINNED=""

pin() { sed -n "s/^$1 \([^ ]*\).*$/\1/p" "$PKG/PINS.txt" | head -1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }

VENV=0; SUITES=()
for a in "$@"; do
  case "$a" in
    --venv) VENV=1 ;;
    -*) echo "usage: ./check.sh [--venv] [suite...]" >&2; exit 2 ;;
    *) [ -d "$PKG/harness/$a" ] || fail usage "no suite $a"; SUITES+=("$a") ;;
  esac
done
[ ${#SUITES[@]} -gt 0 ] || mapfile -t SUITES < <(sed -n 's/^suite //p' "$PKG/harness/SUITES.txt")
T="$(mktemp -d "${TMPDIR:-/tmp}/contract-halmos.XXXXXX")"
trap 'rm -rf "$T"' EXIT

# --- 0. inventory: runs, expected verdicts and mutants agree (scripts/compare.py) ----------
python3 "$PKG/scripts/compare.py" --inventory "$PKG/EXPECTED.tsv" "$WORK" "${SUITES[@]}" > "$T/inventory.txt" \
  || { cat "$T/inventory.txt"; fail inventory "runs.tsv, EXPECTED.tsv and MUTANTS.tsv disagree (INVENTORY FAIL lines above)"; }
cat "$T/inventory.txt"

# --- 1. tools ------------------------------------------------------------------------
binpin() { # name, binary, pinned sha256
  [ "$(sha "$2")" = "$3" ] && return 0
  [ "${TOOLS_UNPINNED:-0}" = 1 ] || fail tools "$1 binary sha256 $(sha "$2") is not the pinned build $3 (TOOLS_UNPINNED=1 accepts another build of the same version)"
  UNPINNED="$UNPINNED $1"
}
command -v python3 >/dev/null || fail tools "python3 not found"
python3 "$PKG/scripts/run.py" --preflight > "$T/runner.txt" || fail tools "the runner cannot run here (FAIL runner line above; see README.md, Re-check)"
if [ "$VENV" = 1 ]; then
  [ ! -x "$PKG/.venv/bin/halmos" ] || echo "venv: .venv/ exists, not reinstalled; checked below"
  [ -x "$PKG/.venv/bin/halmos" ] || {
    PY="${PYTHON:-$(command -v "python$(pin python_version)" || true)}"
    [ -n "$PY" ] && [ -x "$PY" ] || fail tools "no python$(pin python_version) found for the venv (set PYTHON=/path/to/python$(pin python_version))"
    "$PY" -m venv "$PKG/.venv" && PIP_DISABLE_PIP_VERSION_CHECK=1 "$PKG/.venv/bin/pip" install -q --require-hashes --no-deps -r "$PKG/requirements.txt" \
      || fail tools "cannot install requirements.txt into .venv/"; }
  HALMOS="$PKG/.venv/bin/halmos"
fi
if [ -z "${HALMOS:-}" ]; then
  if [ -x "$PKG/.venv/bin/halmos" ]; then HALMOS="$PKG/.venv/bin/halmos"; else HALMOS="$(command -v halmos || true)"; fi
fi
[ -n "$HALMOS" ] && [ -x "$HALMOS" ] || fail tools "halmos not found: run ./check.sh --venv, or set HALMOS=/path/to/halmos ($(pin halmos_version))"
# The python of the halmos environment: the venv's own, else the script's interpreter line.
HPY="$(dirname "$HALMOS")/python"; [ -x "$HPY" ] || HPY="$(head -1 "$HALMOS" | sed -n 's/^#!//p')"
[ -x "$HPY" ] || fail tools "cannot find the python of $HALMOS"
pyv="$("$HPY" -c 'import sys; print("%d.%d" % sys.version_info[:2])' 2>/dev/null)"
if [ "$pyv" != "$(pin python_version)" ]; then
  [ "${TOOLS_UNPINNED:-0}" = 1 ] || fail tools "the halmos environment runs Python '$pyv', pinned $(pin python_version) (TOOLS_UNPINNED=1 accepts another; see README.md, Trust base)"
  UNPINNED="$UNPINNED python$pyv"
fi
"$HPY" -I "$PKG/scripts/pyenv-check.py" "$PKG/requirements.txt" "$PKG/PINS.txt" > "$T/pyenv.txt"; prc=$?
cat "$T/pyenv.txt"
case $prc in
  0) ;;
  3) [ "${TOOLS_UNPINNED:-0}" = 1 ] || fail tools "the halmos environment holds other builds of the pinned versions (UNPINNED pyenv lines above; TOOLS_UNPINNED=1 accepts them)"
     UNPINNED="$UNPINNED pyenv" ;;
  *) fail tools "the halmos environment differs from requirements.txt (FAIL pyenv lines above; remove .venv/ and run ./check.sh --venv)" ;;
esac
# Halmos runs as <python> -I -m halmos: no script in bin/, no PYTHON* variable, no user site, and
# bytecode only from a fresh cache under $T (never a __pycache__ inside the environment).
HBIN="$(dirname "$HALMOS")"
mkdir -p "$T/bin" "$T/pyc"
printf '#!/bin/sh\nexec "%s" -I -X pycache_prefix="%s" -m halmos "$@"\n' "$HPY" "$T/pyc" > "$T/bin/halmos" && chmod +x "$T/bin/halmos"
HALMOS="$T/bin/halmos"
hv="$("$HALMOS" --version 2>/dev/null)"
[ "$hv" = "halmos $(pin halmos_version)" ] || fail tools "halmos is '$hv', pinned $(pin halmos_version)"
z3v="$("$HPY" -I -X pycache_prefix="$T/pyc" -c 'import z3; print(z3.get_version_string())' 2>/dev/null)"
[ "$z3v" = "$(pin z3_version)" ] || fail tools "z3 python module is '$z3v', pinned $(pin z3_version)"
YICES="$HBIN/yices-smt2"
[ -x "$YICES" ] || fail tools "no yices-smt2 in $HBIN (the yices-solver package installs it)"
"$YICES" --version 2>/dev/null | head -1 | grep -qx "Yices $(pin yices_version)" || fail tools "$YICES is not Yices $(pin yices_version)"
binpin yices "$YICES" "$(pin yices_sha256)"
[ -n "$FORGE" ] && [ -x "$FORGE" ] || fail tools "forge not found (set FORGE=/path; $(pin foundry_asset))"
v="$("$FORGE" --version 2>/dev/null | tr '\n' ' ')"
grep -qF "Version: $(pin forge_version)" <<<"$v" && grep -qF "$(pin forge_commit)" <<<"$v" || fail tools "forge is '$v', pinned $(pin forge_version) at $(pin forge_commit)"
binpin forge "$FORGE" "$(pin forge_sha256)"
solc_ver="$(pin solc_version)"; solc_sha="$(pin solc_sha256)"
if [ -z "${SOLC:-}" ]; then
  for s in "$HOME/.svm/${solc_ver%%+*}/solc-${solc_ver%%+*}" "${XDG_DATA_HOME:-$HOME/.local/share}/svm/${solc_ver%%+*}/solc-${solc_ver%%+*}" "$DEPS_CACHE/solc-$solc_ver"; do
    [ -x "$s" ] && { SOLC="$s"; break; }
  done
fi
if [ -z "${SOLC:-}" ]; then
  [ "${SOLC_FETCH:-1}" = 1 ] || fail tools "no solc ${solc_ver%%+*} found and SOLC_FETCH=0"
  mkdir -p "$DEPS_CACHE"
  curl -sSfL -o "$T/solc" "$(pin solc_url)" || fail tools "cannot download $(pin solc_url)"
  [ "$(sha "$T/solc")" = "$solc_sha" ] || fail tools "downloaded solc has sha256 $(sha "$T/solc"), pinned $solc_sha"
  chmod +x "$T/solc" && mv "$T/solc" "$DEPS_CACHE/solc-$solc_ver" && SOLC="$DEPS_CACHE/solc-$solc_ver"
fi
"$SOLC" --version 2>/dev/null | grep -qF "Version: $solc_ver" || fail tools "solc $SOLC is not $solc_ver"
binpin solc "$SOLC" "$solc_sha"
# Halmos calls forge by name: put the checked forge first on PATH.
ln -s "$FORGE" "$T/bin/forge"
export PATH="$T/bin:$PATH" SOLC HALMOS YICES
echo "tools: halmos $(pin halmos_version) ($HPY -I -m halmos, Python $pyv), z3 $z3v, yices $(pin yices_version) ($YICES), forge $(pin forge_version) ($FORGE), solc $solc_ver ($SOLC)${UNPINNED:+; unpinned build:$UNPINNED}"
cat "$T/runner.txt"

# --- 2. source -----------------------------------------------------------------------
commit="$(pin pocs_commit)"; dir="$(pin pocs_dir)"
[ -e "$POCS/.git" ] || fail source "no pocs checkout at $POCS (run: git -C $PKG submodule update --init pocs)"
git -C "$POCS" cat-file -e "$commit^{commit}" 2>/dev/null || fail source "pocs at $POCS does not hold $commit"
git -C "$POCS" ls-tree -r "$commit" "$dir/foundry.toml" "$dir/soldeer.lock" "$dir/contracts/src" \
  | awk -v s="$dir/" '{sub(s, "", $4); print $3, $4}' | LC_ALL=C sort -k2 > "$T/manifest.txt"
sed -n 's/^blob //p' PINS.txt | LC_ALL=C sort -k2 > "$T/manifest.pinned"
diff "$T/manifest.pinned" "$T/manifest.txt" > "$T/manifest.diff" || { cat "$T/manifest.diff"; fail source "blob ids at $commit differ from the blob pins in PINS.txt"; }
echo "source: pocs $commit, $(wc -l < "$T/manifest.txt") files under $dir equal the blob pins"

# --- 3. dependencies (as deployment/check.sh) ----------------------------------------------
git -C "$POCS" show "$commit:$dir/soldeer.lock" > "$T/soldeer.lock" || fail deps "cannot read soldeer.lock at $commit"
python3 - "$T/soldeer.lock" > "$T/zips.txt" <<'PY' || fail deps "cannot read the pinned soldeer.lock"
import re, sys
for blk in open(sys.argv[1]).read().split("[[dependencies]]")[1:]:
    g = lambda k: (re.search(rf'^{k} = "([^"]+)"', blk, re.M) or [None, None])[1]
    if g("url"):
        print(f'{g("name")}-{g("version")} {g("url")} {g("checksum")}')
    else:
        print(f'git {g("git")} {g("rev")}')
PY
mkdir -p "$DEPS_CACHE/zips" "$T/soldeer"
nzip=0
while read -r name url checksum; do
  if [ "$name" = git ]; then
    [ "$url" = "$(pin zkkit_repo)" ] && [ "$checksum" = "$(pin zkkit_rev)" ] || fail deps "lock names git dependency $url at $checksum, pinned $(pin zkkit_repo) at $(pin zkkit_rev)"
    continue
  fi
  want="$(sed -n "s/^zip_sha256 \([0-9a-f]*\) $name$/\1/p" PINS.txt)"
  [ -n "$want" ] || fail deps "$name is in the pinned soldeer.lock but has no zip_sha256 pin"
  [ "$want" = "$checksum" ] || fail deps "$name: lock checksum $checksum, pinned $want"
  z="$DEPS_CACHE/zips/$want.zip"
  if [ ! -f "$z" ] || [ "$(sha "$z")" != "$want" ]; then
    curl -sSfL -o "$T/dl.zip" "$url" || fail deps "cannot download $url"
    got="$(sha "$T/dl.zip")"
    [ "$got" = "$want" ] || fail deps "$url has sha256 $got, pinned $want"
    mv "$T/dl.zip" "$z"
  fi
  python3 -I -c 'import sys, zipfile; zipfile.ZipFile(sys.argv[1]).extractall(sys.argv[2])' "$z" "$T/soldeer/$name" || fail deps "cannot unpack $z"
  nzip=$((nzip + 1))
done < "$T/zips.txt"
[ "$nzip" -eq "$(grep -c '^zip_sha256 ' PINS.txt)" ] || fail deps "the lock names $nzip soldeer packages, PINS.txt pins $(grep -c '^zip_sha256 ' PINS.txt)"
python3 "$PKG/scripts/soldeer-integrity.py" "$T/soldeer.lock" "$T/soldeer" > "$T/integrity.txt" || { cat "$T/integrity.txt"; fail deps "soldeer integrity"; }
ZK="$DEPS_CACHE/zk-kit.solidity"; rev="$(pin zkkit_rev)"
if ! git -C "$ZK" cat-file -e "$rev^{commit}" 2>/dev/null; then
  rm -rf "$ZK"; git init -q "$ZK" && git -C "$ZK" fetch -q --depth 1 "$(pin zkkit_repo)" "$rev" || fail deps "cannot fetch $(pin zkkit_repo) at $rev"
fi
tree="$(git -C "$ZK" rev-parse "$rev^{tree}")"
[ "$tree" = "$(pin zkkit_tree)" ] || fail deps "zk-kit $rev has tree $tree, pinned $(pin zkkit_tree)"
echo "deps: $nzip soldeer zips by sha256 and integrity, zk-kit.solidity $rev tree $tree"

# --- 4. per suite: build, run, compare ------------------------------------------------------
mkdir -p "$WORK"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
for s in "${SUITES[@]}"; do
  P="$WORK/$s/project"; L="$WORK/$s/logs"
  rm -rf "$WORK/$s"
  POCS="$POCS" SOLDEER_DEPS="$T/soldeer" ZKKIT_GIT="$ZK" bash "$PKG/scripts/setup-suite.sh" "$s" "$P" || fail "setup:$s" "see the lines above"
  t0=$SECONDS
  python3 "$PKG/scripts/run.py" "$s" "$P" "$L" || fail "run:$s" "the runner stopped"
  echo "suite $s: $((SECONDS - t0))s"
done
python3 "$PKG/scripts/compare.py" "$PKG/EXPECTED.tsv" "$WORK" "${SUITES[@]}" | tee "$WORK/compare.txt"; rc=${PIPESTATUS[0]}
read -r _ total bad pdiff < <(grep '^SUMMARY ' "$WORK/compare.txt") || { total=0; bad=1; pdiff=0; }
echo "check.sh: ${#SUITES[@]} suites, ${SECONDS}s, work $WORK, started $STAMP${UNPINNED:+ (unpinned build:$UNPINNED)}"
if [ $rc -eq 0 ]; then
  echo "CHECK PASS: ${#SUITES[@]} suites, $total verdicts equal EXPECTED.tsv, $pdiff path counts differ from the frozen runs (PATHS lines), ${SECONDS}s${UNPINNED:+ (unpinned build:$UNPINNED)}"
else
  echo "CHECK FAIL: $bad mismatches in $total verdicts (INVENTORY FAIL, CHECK MISMATCH, CHECK DUPLICATE, CHECK EXTRA${STRICT_PATHS:+, PATHS} lines above)"
fi
exit $rc
