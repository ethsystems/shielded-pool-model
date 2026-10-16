#!/usr/bin/env bash
# Replay check for circuits-acir (see README.md). Needs bash, git, python3 (3.10 or later),
# sha256sum, elan, the pocs submodule (from the repo root: git submodule update --init
# circuits-acir/pocs) and the two pinned tools from inputs/TOOLS.txt; lake picks the toolchain
# from lean-toolchain. Run builds one at a time; set LEAN_NUM_THREADS to change the Lean thread
# count (default 2).
#   ./check.sh              rebuild the three circuits from the pinned pocs commit, then replay
#                           every theorem, control and census against expected.json
#   ./check.sh --self-test  check that each must-fail fixture fails for its intended reason
# Env: NARGO, NOIR_INSPECTOR (binaries; default: from PATH), POCS (the pocs checkout; default
# ./pocs), DEPS_CACHE (git clones of the Noir dependencies, by commit; default ./.deps),
# TOOLS_UNPINNED=1 (accept a binary whose sha256 is not the pinned Linux x86_64 build; its
# version must still match). Relative paths are taken from the caller's directory.
set -uo pipefail
export PYTHONDONTWRITEBYTECODE=1
CALLER="$(pwd)"
rel() { case "$1" in /*|"") printf '%s' "$1" ;; *) printf '%s/%s' "$CALLER" "$1" ;; esac; }
# The tools are looked up from the caller's directory, before the cd below.
NARGO="$(rel "${NARGO:-$(command -v nargo || true)}")"
NOIR_INSPECTOR="$(rel "${NOIR_INSPECTOR:-$(command -v noir-inspector || true)}")"
export NARGO NOIR_INSPECTOR
cd "$(dirname "$0")"
PKG="$(pwd)"
POCS="$(rel "${POCS:-$PKG/pocs}")"
DEPS_CACHE="$(rel "${DEPS_CACHE:-$PKG/.deps}")"
WORK="$PKG/build/rebuild"
OUT="$PKG/build/inputs"
CIRCUITS=(deposit withdraw transfer)
UNPINNED=""

pin() { sed -n "s/^$1 \(.*\)$/\1/p" "$PKG/inputs/TOOLS.txt" | head -1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }
install_hint() {
  echo "  install nargo and noir-inspector $(pin nargo_version): $(pin noir_release)"
  echo "    asset $(pin noir_asset) (unpack; nargo sha256 $(pin nargo_sha256),"
  echo "    noir-inspector sha256 $(pin noir_inspector_sha256))"
  echo "  then: NARGO=/path/to/nargo NOIR_INSPECTOR=/path/to/noir-inspector ./check.sh"
}

# --- self-test of the rebuild stages ------------------------------------------------
if [ "${1:-}" = "--self-test" ]; then
  T="$(mktemp -d "${TMPDIR:-/tmp}/circuits-acir-selftest.XXXXXX")"
  trap 'rm -rf "$T"' EXIT
  export DEPS_CACHE
  [ -e "$POCS/.git" ] || { echo "SELF-TEST FAIL: no pocs checkout at $POCS"; exit 1; }
  n=0
  # Each copy gets the package without .lake, build/, pocs/ and .deps/, and its own clone of
  # pocs at the pin. Every fixture fails before any Lean build.
  run_copy() { # name, expected-stage, setup-command...
    local name="$1" stage="$2"; shift 2
    local c="$T/$name"; mkdir -p "$c"
    tar -C "$PKG" --exclude=./.lake --exclude=./build --exclude=./pocs --exclude=./.deps -cf - . | tar -xf - -C "$c"
    { git clone -q --shared --no-checkout "$POCS" "$c/pocs" && git -C "$c/pocs" checkout -q --detach "$(pin pocs_commit)"; } \
      || { echo "SELF-TEST FAIL: could not clone pocs for $name"; exit 1; }
    (cd "$c" && "$@") || { echo "SELF-TEST FAIL: could not set up $name"; exit 1; }
    local out; out="$(cd "$c" && POCS="$c/pocs" bash ./check.sh 2>&1)"; local rc=$?
    local pat="^FAIL $stage:"; [ "$stage" = replay ] && pat='^REPLAY CHECK FAIL'
    [ $rc -ne 0 ] && grep -q "$pat" <<<"$out" \
      || { echo "SELF-TEST FAIL: $name should fail at '$stage'"; echo "$out" | tail -20; exit 1; }
    echo "SELF-TEST ok: $name fails at $stage"
    n=$((n + 1)); LAST_OUT="$out"
  }
  # because NAME PATTERN: the last copy's output must also show this exact reason.
  because() {
    grep -q -- "$2" <<<"$LAST_OUT" || { echo "SELF-TEST FAIL: $1 failed for another reason"; echo "$LAST_OUT" | tail -20; exit 1; }
    grep -m1 -- "$2" <<<"$LAST_OUT" | cut -c1-200 | sed 's/^/    /'
  }
  # 1. pocs checked out at another commit than the pin: the source gate must catch it.
  run_copy pocs-moved source git -C pocs -c user.name=self-test -c user.email=self-test@invalid commit -q --allow-empty -m moved
  because pocs-moved "^FAIL source: pocs is checked out at"
  # 2, 3. A tool binary with one byte appended: same version, another sha256. The checksum
  #    gate must stop before any build.
  for t in NARGO NOIR_INSPECTOR; do
    [ -n "${!t}" ] && [ -x "${!t}" ] || { echo "SELF-TEST FAIL: $t not found (set $t=/path)"; exit 1; }
  done
  cp "$NARGO" "$T/nargo" && printf '\0' >> "$T/nargo"
  NARGO="$T/nargo" run_copy nargo-hash tools true
  because nargo-hash "^FAIL tools: nargo binary sha256 [0-9a-f]* is not the pinned build"
  [ ! -e "$T/nargo-hash/build" ] || { echo "SELF-TEST FAIL: nargo-hash started a build"; exit 1; }
  cp "$NOIR_INSPECTOR" "$T/noir-inspector" && printf '\0' >> "$T/noir-inspector"
  NOIR_INSPECTOR="$T/noir-inspector" run_copy noir-inspector-hash tools true
  because noir-inspector-hash "^FAIL tools: noir-inspector binary sha256 [0-9a-f]* is not the pinned build"
  [ ! -e "$T/noir-inspector-hash/build" ] || { echo "SELF-TEST FAIL: noir-inspector-hash started a build"; exit 1; }
  # 4. The withdraw circuit narrowed to 127 bits, with the pocs pin, inputs/SHA256SUMS and their
  #    expected.json hashes moved to match: only the comparison of the rebuilt outputs with
  #    expected.json can catch it, and it must name withdraw and nothing else.
  run_copy circuit-127 replay python3 - "$(pin pocs_dir)" <<'PY'
import hashlib, json, subprocess, sys
d = sys.argv[1]
src = f'pocs/{d}/circuits/withdraw/src/main.nr'
t = open(src).read()
old = 'amount.assert_max_bit_size::<128>();'
assert t.count(old) == 1, 'anchor not found once'
open(src, 'w').write(t.replace(old, 'amount.assert_max_bit_size::<127>();'))
g = ['git', '-C', 'pocs', '-c', 'user.name=self-test', '-c', 'user.email=self-test@invalid']
subprocess.run(g + ['commit', '-qam', 'self-test'], check=True)
head = subprocess.run(['git', '-C', 'pocs', 'rev-parse', 'HEAD'], capture_output=True, text=True, check=True).stdout.strip()
tools = open('inputs/TOOLS.txt').read()
cur = next(l for l in tools.split('\n') if l.startswith('pocs_commit '))
open('inputs/TOOLS.txt', 'w').write(tools.replace(cur, f'pocs_commit {head}'))
sums = []
for l in open('inputs/SHA256SUMS').read().split('\n'):
    if l:
        f = l[66:]
        data = open(f'pocs/{d}/{f[len("pool/"):]}', 'rb').read()
        sums.append(f'{hashlib.sha256(data).hexdigest()}  {f}')
open('inputs/SHA256SUMS', 'w').write('\n'.join(sums) + '\n')
e = json.load(open('expected.json'))
for f in ('inputs/TOOLS.txt', 'inputs/SHA256SUMS'):
    e['source_files'][f] = hashlib.sha256(open(f, 'rb').read()).hexdigest()
json.dump(e, open('expected.json', 'w'), indent=1, ensure_ascii=False)
PY
  because circuit-127 "^MISMATCH inputs: withdraw: "
  because circuit-127 "^FATAL input artifacts differ from expected.json"
  ! grep -q "^MISMATCH inputs: \(deposit\|transfer\)\|^[A-Z]* source_files" <<<"$LAST_OUT" \
    || { echo "SELF-TEST FAIL: circuit-127 failed for another reason too"; echo "$LAST_OUT" | tail -20; exit 1; }
  echo "SELF-TEST ok: rebuild stages, $n copies, ${SECONDS}s"
  # The replay self-test below runs through exec, which skips the EXIT trap.
  rm -rf "$T"; trap - EXIT
fi
[ -z "${1:-}" ] || [ "$1" = --self-test ] || { echo "usage: ./check.sh [--self-test]" >&2; exit 2; }

# --- 1. tools --------------------------------------------------------------------
for t in NARGO NOIR_INSPECTOR; do
  [ -n "${!t}" ] && [ -x "${!t}" ] || { install_hint; fail tools "$t not found (set $t=/path or install)"; }
done
nv="$("$NARGO" --version 2>/dev/null | tr '\n' ' ')"
grep -q "nargo version = $(pin nargo_version) " <<<"$nv" && grep -q "$(pin nargo_git)" <<<"$nv" \
  || { install_hint; fail tools "nargo is '$nv', pinned $(pin nargo_version) at $(pin nargo_git)"; }
iv="$("$NOIR_INSPECTOR" --version 2>/dev/null | tr -d '\n')"
[ "$iv" = "Noir inspector version = $(pin noir_inspector_version)" ] \
  || { install_hint; fail tools "noir-inspector is '$iv', pinned $(pin noir_inspector_version)"; }
for t in nargo noir-inspector; do
  bin="$NARGO"; key=nargo_sha256
  [ "$t" = noir-inspector ] && { bin="$NOIR_INSPECTOR"; key=noir_inspector_sha256; }
  if [ "$(sha "$bin")" != "$(pin $key)" ]; then
    [ "${TOOLS_UNPINNED:-0}" = 1 ] || { install_hint; fail tools "$t binary sha256 $(sha "$bin") is not the pinned build $(pin $key) (TOOLS_UNPINNED=1 accepts another build of the same version)"; }
    UNPINNED="$UNPINNED $t"
  fi
done
echo "tools: nargo and noir-inspector $(pin nargo_version) ($NARGO, $NOIR_INSPECTOR)${UNPINNED:+; unpinned build:$UNPINNED}"

# --- 2. source -------------------------------------------------------------------
# The circuit files are read from the pinned pocs commit, as raw git blobs, never from the
# working tree, so an uncommitted edit in pocs/ cannot reach the build.
commit="$(pin pocs_commit)"; dir="$(pin pocs_dir)"
[ -e "$POCS/.git" ] || fail source "no pocs checkout at $POCS (run: git -C $PKG submodule update --init pocs)"
head="$(git -C "$POCS" rev-parse HEAD 2>/dev/null)"
[ "$head" = "$commit" ] || fail source "pocs is checked out at '$head', pinned $commit (run: git -C $PKG submodule update pocs)"
rm -rf "$WORK" "$OUT"; mkdir -p "$WORK/home" "$OUT"
nfiles=0
while read -r f; do
  mkdir -p "$WORK/$(dirname "$f")"
  git -C "$POCS" cat-file blob "$commit:$dir/${f#pool/}" > "$WORK/$f" 2>/dev/null || fail source "$dir/${f#pool/} is not in pocs at $commit"
  nfiles=$((nfiles + 1))
done < <(cut -c67- inputs/SHA256SUMS)
echo "source: $nfiles files from pocs $commit ($dir)"

# --- 3. inputs -------------------------------------------------------------------
(cd "$WORK" && sha256sum --quiet --strict -c "$PKG/inputs/SHA256SUMS") || fail inputs "a file at the pocs pin differs from inputs/SHA256SUMS"
echo "inputs: $nfiles files match inputs/SHA256SUMS"

# --- 4. Noir dependencies --------------------------------------------------------
# The same shallow clone of the tag that nargo makes, kept in DEPS_CACHE by commit, then
# unpacked where nargo looks for it (HOME/nargo/...), so nargo itself fetches nothing. The
# build below also runs nargo with GIT_ALLOW_PROTOCOL=none, so any fetch fails the build.
[ -r inputs/DEPS.txt ] || fail deps "cannot read inputs/DEPS.txt"
while read -r path head tag _; do
  head="${head#head=}"; tag="${tag#tag=}"; url="https://$(dirname "${path#nargo/}")"; repo="$DEPS_CACHE/$head"
  if ! git -C "$repo" cat-file -e "$head^{commit}" 2>/dev/null; then
    tmp="$WORK/clone"; rm -rf "$tmp"
    git -c advice.detachedHead=false clone -q --depth 1 --branch "$tag" "$url" "$tmp" 2>"$WORK/clone.log" \
      || { cat "$WORK/clone.log"; fail deps "cannot clone $url at tag $tag"; }
    got="$(git -C "$tmp" rev-parse HEAD)"
    [ "$got" = "$head" ] || fail deps "$url tag $tag is at $got, pinned $head"
    mkdir -p "$DEPS_CACHE"; rm -rf "$repo"; mv "$tmp" "$repo"
  fi
  mkdir -p "$WORK/home/$path"
  git -C "$repo" archive "$head" | tar -xf - -C "$WORK/home/$path" || fail deps "cannot unpack $url at $head"
  echo "deps: $url $tag at $head"
done < inputs/DEPS.txt
# Every git dependency that the pinned manifests name must have been placed above; otherwise
# nargo would fetch it itself, without a commit check.
wanted="$(python3 - "$WORK/pool" <<'PY'
import glob, re, sys
for p in sorted(glob.glob(sys.argv[1] + "/**/Nargo.toml", recursive=True)):
    for line in open(p):
        g = re.search(r'git\s*=\s*"https://([^"]+?)/?"', line)
        t = re.search(r'tag\s*=\s*"([^"]+)"', line)
        if g and t:
            print(f"{g.group(1)}/{t.group(1)}")
PY
)" || fail deps "cannot read the dependencies of the pinned manifests"
[ -n "$wanted" ] || fail deps "the pinned manifests name no git dependency"
for d in $(LC_ALL=C sort -u <<<"$wanted"); do
  [ -d "$WORK/home/nargo/$d" ] || fail deps "$d is named in a pinned Nargo.toml but not pinned in inputs/DEPS.txt"
done

# --- 5. rebuild ------------------------------------------------------------------
# The artifact, its print and the witness for the committed Prover.toml, written to build/inputs/.
# replay.py compares their hashes with expected.json before it uses them.
for c in "${CIRCUITS[@]}"; do
  log="$WORK/$c.log"
  (cd "$WORK/pool" && HOME="$WORK/home" GIT_ALLOW_PROTOCOL=none "$NARGO" compile --package "$c") > "$log" 2>&1 \
    || { tail -20 "$log"; fail build "nargo compile --package $c (see $log)"; }
  (cd "$WORK/pool" && HOME="$WORK/home" GIT_ALLOW_PROTOCOL=none "$NARGO" execute --package "$c" "$c-witness") >> "$log" 2>&1 \
    || { tail -20 "$log"; fail build "nargo execute --package $c (see $log)"; }
  "$NOIR_INSPECTOR" print-acir "$WORK/pool/target/$c.json" > "$OUT/$c.acir.txt" 2>> "$log" \
    || { tail -20 "$log"; fail build "noir-inspector print-acir $c (see $log)"; }
  cp "$WORK/pool/target/$c.json" "$OUT/$c.json" && cp "$WORK/pool/target/$c-witness.gz" "$OUT/$c-witness.gz" \
    || fail build "cannot copy the $c outputs to $OUT"
  echo "rebuild: $c artifact, print and witness"
done
echo "rebuild: done${UNPINNED:+ (unpinned build:$UNPINNED)}, ${SECONDS}s"

# --- 6. replay -------------------------------------------------------------------
case "${1:-}" in
  "") exec python3 scripts/replay.py check ;;
  --self-test) rm -f build/PASS; exec python3 scripts/replay.py self-test ;;
esac
