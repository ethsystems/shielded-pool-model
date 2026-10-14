#!/usr/bin/env bash
# Build reproduction check for verifier-reproduction (see README.md). Needs bash, git,
# python3, sha256sum, curl (only when no pinned CRS is on this machine), the pocs
# submodule (git submodule update --init verifier-reproduction/pocs), and the two pinned
# tools from inputs/TOOLS.txt.
#   ./check.sh              rebuild the three verifiers and compare them with the committed files
#   ./check.sh --self-test  plant seven changes, each of which must make the check fail for its
#                           reason, and run one unchanged copy, which must pass
# Env: NARGO, BB (binaries; default: from PATH), POCS (the pocs checkout; default ./pocs),
# DEPS_CACHE (git clones of the Noir dependencies, by commit; default ./.deps), CRS_DIR (an
# existing bb CRS directory to reuse; default ~/.bb-crs), CRS_FETCH=0 (never download the
# CRS), TOOLS_UNPINNED=1 (accept a binary whose sha256 is not the pinned Linux x86_64
# build; its version must still match). Relative paths are taken from the caller's directory.
set -uo pipefail
CALLER="$(pwd)"
rel() { case "$1" in /*|"") printf '%s' "$1" ;; *) printf '%s/%s' "$CALLER" "$1" ;; esac; }
# Paths, made absolute here because the build and the self-test run in other directories.
# The tools are looked up from the caller's directory too, before the cd below.
NARGO="$(rel "${NARGO:-$(command -v nargo || true)}")"
BB="$(rel "${BB:-$(command -v bb || true)}")"
export NARGO BB
cd "$(dirname "$0")"
PKG="$(pwd)"
WORK="$(rel "${WORK:-$PKG/work}")"
POCS="$(rel "${POCS:-$PKG/pocs}")"
DEPS_CACHE="$(rel "${DEPS_CACHE:-$PKG/.deps}")"
CRS_DIR="$(rel "${CRS_DIR:-$HOME/.bb-crs}")"
CIRCUITS=(deposit transfer withdraw)
UNPINNED=""

pin() { sed -n "s/^$1 \(.*\)$/\1/p" "$PKG/inputs/TOOLS.txt" | head -1; }
expected() { python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]][sys.argv[3]])' "$PKG/expected.json" "$1" "$2"; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
hex() { od -An -tx1 -v "$1" | tr -d ' \n'; }
cap() { printf '%s%s' "$(printf '%s' "${1:0:1}" | tr '[:lower:]' '[:upper:]')" "${1:1}"; }
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }
install_hint() {
  echo "  install nargo $(pin nargo_version): $(pin nargo_release)"
  echo "    asset $(pin nargo_asset) (unpack; binary sha256 $(pin nargo_sha256))"
  echo "  install bb $(pin bb_version): $(pin bb_release)"
  echo "    asset $(pin bb_asset) (unpack; binary sha256 $(pin bb_sha256))"
  echo "  then: NARGO=/path/to/nargo BB=/path/to/bb ./check.sh"
}

# --- self-test ---------------------------------------------------------------------
if [ "${1:-}" = "--self-test" ]; then
  T="$(mktemp -d "${TMPDIR:-/tmp}/verifier-selftest.XXXXXX")"
  trap 'rm -rf "$T"' EXIT
  export DEPS_CACHE
  [ -e "$POCS/.git" ] || { echo "SELF-TEST FAIL: no pocs checkout at $POCS"; exit 1; }
  n=0
  # Each copy gets check.sh, expected.json, inputs/ and its own clone of pocs at the pin.
  run_copy() { # name, expected-stage, setup-command...
    local name="$1" stage="$2"; shift 2
    local c="$T/$name"; mkdir -p "$c"
    (cd "$PKG" && tar -cf - check.sh expected.json inputs) | tar -xf - -C "$c"
    { git clone -q --shared --no-checkout "$POCS" "$c/pocs" && git -C "$c/pocs" checkout -q --detach "$(pin pocs_commit)"; } \
      || { echo "SELF-TEST FAIL: could not clone pocs for $name"; exit 1; }
    (cd "$c" && "$@") || { echo "SELF-TEST FAIL: could not set up $name"; exit 1; }
    local out; out="$(cd "$c" && WORK="$c/work" POCS="$c/pocs" bash ./check.sh 2>&1)"; local rc=$?
    if [ "$stage" = PASS ]; then
      [ $rc -eq 0 ] && grep -q '^CHECK PASS' <<<"$out" || { echo "SELF-TEST FAIL: $name should pass"; echo "$out" | tail -20; exit 1; }
      echo "SELF-TEST ok: $name passes"
    else
      [ $rc -ne 0 ] && grep -q "^FAIL $stage:" <<<"$out" || { echo "SELF-TEST FAIL: $name should fail at '$stage'"; echo "$out" | tail -20; exit 1; }
      echo "SELF-TEST ok: $name fails at $stage"
    fi
    n=$((n + 1)); LAST_OUT="$out"
  }
  # because NAME PATTERN: the last copy's output must also show this exact reason.
  because() { grep -q -- "$2" <<<"$LAST_OUT" || { echo "SELF-TEST FAIL: $1 failed for another reason"; echo "$LAST_OUT" | tail -20; exit 1; }; }
  # edit FILE OLD NEW [COUNT]: replace exactly COUNT (default 1) occurrences, portably.
  edit() { python3 - "$@" <<'PY'
import sys
p, old, new = sys.argv[1:4]; n = int(sys.argv[4]) if len(sys.argv) > 4 else 1
t = open(p).read()
assert t.count(old) == n, f"{p}: {t.count(old)} occurrences of {old!r}, expected {n}"
open(p, "w").write(t.replace(old, new))
PY
  }
  # repin: commit the edits in the copy's pocs and move the copy's pin to that commit.
  repin() {
    git -C pocs -c user.name=self-test -c user.email=self-test@invalid commit -qam "self-test" \
      && edit inputs/TOOLS.txt "pocs_commit $(sed -n 's/^pocs_commit //p' inputs/TOOLS.txt)" "pocs_commit $(git -C pocs rev-parse HEAD)"
  }
  # resum: rewrite inputs/SHA256SUMS from the copy's pocs files.
  resum() {
    local d; d="$(sed -n 's/^pocs_dir //p' inputs/TOOLS.txt)"
    cut -c67- inputs/SHA256SUMS | sed 's#^pool/##' | (cd "pocs/$d" && xargs sha256sum) | sed 's#  #  pool/#' > inputs/SHA256SUMS.new \
      && mv inputs/SHA256SUMS.new inputs/SHA256SUMS
  }
  V="$(pin pocs_dir)/contracts/src/verifiers"
  # 1. pocs checked out at another commit than the pin: the source gate must catch it.
  run_copy pocs-moved source git -C pocs -c user.name=self-test -c user.email=self-test@invalid commit -q --allow-empty -m moved
  because pocs-moved "^FAIL source: pocs is checked out at"
  # 2. A committed verifier changed and the pin moved, hashes not updated: the input gate must catch it.
  run_copy input-edit inputs bash -c "$(declare -f edit repin); edit pocs/$V/DepositVerifier.sol 'uint256 constant N = ' 'uint256 constant N  = ' && repin"
  because input-edit "^pool/contracts/src/verifiers/DepositVerifier.sol: FAILED"
  # 3. A committed VK_HASH digit flipped, pin and hashes updated: the rebuild must disagree.
  run_copy vkhash-flip verifier bash -c \
    'python3 - "pocs/'"$V"'/TransferVerifier.sol" <<"PY"
import re, sys
p = sys.argv[1]
t = open(p).read()
m = re.search(r"(uint256 constant VK_HASH = 0x[0-9a-f]*)([0-9a-f]);", t)
d = "0" if m.group(2) != "0" else "1"
open(p, "w").write(t[:m.start(2)] + d + t[m.end(2):])
PY
    '"$(declare -f edit repin resum); repin && resum"
  because vkhash-flip "^FAIL verifier: generated TransferVerifier.sol"
  # 4. The withdraw circuit narrowed to 127 bits, pin and hashes updated: the rebuild must give
  #    the recorded mutant key and verifier, which differ from the committed ones.
  run_copy circuit-127 verifier bash -c "$(declare -f edit repin resum); edit pocs/$(pin pocs_dir)/circuits/withdraw/src/main.nr 'amount.assert_max_bit_size::<128>();' 'amount.assert_max_bit_size::<127>();' && repin && resum"
  because circuit-127 "^FAIL verifier: generated WithdrawVerifier.sol"
  for k in acir_sha256 vk_hash gen_sol_sha256; do
    want="$(expected control_withdraw_127 "$k")"
    got="$(sed -n "s/^withdraw $k \(.*\)$/\1/p" "$T/circuit-127/work/results.txt")"
    [ "$want" = "$got" ] || { echo "SELF-TEST FAIL: mutant withdraw $k is $got, recorded $want"; exit 1; }
  done
  echo "SELF-TEST ok: the 127-bit mutant reproduces the recorded mutant key and verifier"
  # 5. A Noir dependency tag that moved upstream: the dependency gate must catch it. A local
  #    repository stands in for github.com, with tag v0.3.0 on another commit, and the copy
  #    gets an empty cache, so the check must clone.
  F="$T/fake-upstream/noir-lang/poseidon"
  { git init -q "$F" && git -C "$F" -c user.name=self-test -c user.email=self-test@invalid commit -q --allow-empty -m moved \
    && git -C "$F" tag v0.3.0; } || { echo "SELF-TEST FAIL: could not set up the fake upstream"; exit 1; }
  DEPS_CACHE="$T/empty-cache" GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.$T/fake-upstream/.insteadOf" \
    GIT_CONFIG_VALUE_0="https://github.com/" run_copy dep-tag-moved deps true
  because dep-tag-moved "^FAIL deps: https://github.com/noir-lang/poseidon tag v0.3.0 is at"
  # 6. A dependency that a pinned manifest names but inputs/DEPS.txt does not pin: the dependency
  #    gate must stop before nargo could fetch it without a commit check.
  run_copy dep-unpinned deps bash -c 'grep -v zk-kit inputs/DEPS.txt > inputs/DEPS.new && mv inputs/DEPS.new inputs/DEPS.txt'
  because dep-unpinned "^FAIL deps: github.com/privacy-scaling-explorations/zk-kit.noir/binary-merkle-root-v0.0.2 is named in a pinned Nargo.toml"
  # 7. A bb that reports another version: the version gate must stop before any build.
  #    TOOLS_UNPINNED=1 so the checksum gate cannot be the reason.
  printf '#!/bin/sh\necho 5.0.0\n' > "$T/fake-bb"; chmod +x "$T/fake-bb"
  BB="$T/fake-bb" TOOLS_UNPINNED=1 run_copy wrong-bb tools true
  because wrong-bb "^FAIL tools: bb is '5.0.0', pinned"
  [ ! -e "$T/wrong-bb/work" ] || { echo "SELF-TEST FAIL: wrong-bb started a build"; exit 1; }
  # 8. The unchanged copy must pass.
  run_copy unchanged PASS true
  echo "SELF-TEST PASS: $n copies, ${SECONDS}s"
  exit 0
fi
[ -z "${1:-}" ] || { echo "usage: ./check.sh [--self-test]" >&2; exit 2; }

# --- 1. tools --------------------------------------------------------------------
for t in NARGO BB; do
  [ -n "${!t}" ] && [ -x "${!t}" ] || { install_hint; fail tools "$t not found (set $t=/path or install)"; }
done
nv="$("$NARGO" --version 2>/dev/null | tr '\n' ' ')"
grep -q "nargo version = $(pin nargo_version) " <<<"$nv" && grep -q "$(pin nargo_git)" <<<"$nv" \
  || { install_hint; fail tools "nargo is '$nv', pinned $(pin nargo_version) at $(pin nargo_git)"; }
bv="$("$BB" --version 2>/dev/null | tr -d '\n')"
[ "$bv" = "$(pin bb_version)" ] || { install_hint; fail tools "bb is '$bv', pinned $(pin bb_version)"; }
for t in nargo bb; do
  bin="$NARGO"; [ "$t" = bb ] && bin="$BB"
  if [ "$(sha "$bin")" != "$(pin ${t}_sha256)" ]; then
    [ "${TOOLS_UNPINNED:-0}" = 1 ] || { install_hint; fail tools "$t binary sha256 $(sha "$bin") is not the pinned build $(pin ${t}_sha256) (TOOLS_UNPINNED=1 accepts another build of the same version)"; }
    UNPINNED="$UNPINNED $t"
  fi
done
echo "tools: nargo $(pin nargo_version) ($NARGO), bb $(pin bb_version) ($BB)${UNPINNED:+; unpinned build:$UNPINNED}"

# --- 2. source -------------------------------------------------------------------
# The pool files are read from the pinned pocs commit, as raw git blobs, never from the
# working tree, so an uncommitted edit in pocs/ cannot reach the build.
commit="$(pin pocs_commit)"; dir="$(pin pocs_dir)"
[ -e "$POCS/.git" ] || fail source "no pocs checkout at $POCS (run: git submodule update --init verifier-reproduction/pocs)"
head="$(git -C "$POCS" rev-parse HEAD 2>/dev/null)"
[ "$head" = "$commit" ] || fail source "pocs is checked out at '$head', pinned $commit (run: git submodule update verifier-reproduction/pocs)"
rm -rf "$WORK"; mkdir -p "$WORK/crs" "$WORK/home"
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
# unpacked where nargo looks for it (HOME/nargo/...), so nargo itself fetches nothing.
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

# --- 5. CRS ----------------------------------------------------------------------
crs_sha="$(pin crs_sha256)"; crs_bytes="$(pin crs_bytes)"
src="$CRS_DIR/bn254_g1.dat"
if [ -f "$src" ] && [ "$(stat -c %s "$src" 2>/dev/null || stat -f %z "$src")" -ge "$crs_bytes" ]; then
  head -c "$crs_bytes" "$src" > "$WORK/crs/bn254_g1.dat"
  crs_from="prefix of $src"
else
  [ "${CRS_FETCH:-1}" = 1 ] || fail crs "no CRS of $crs_bytes bytes at $src and CRS_FETCH=0"
  for u in "$(pin crs_url)" "$(pin crs_url_alt)"; do
    curl -sSL --fail -r "0-$((crs_bytes - 1))" -o "$WORK/crs/bn254_g1.dat" "$u" && break
  done
  crs_from="fetched from $u"
fi
[ -f "$WORK/crs/bn254_g1.dat" ] && [ "$(sha "$WORK/crs/bn254_g1.dat")" = "$crs_sha" ] \
  || fail crs "CRS ($crs_from) is not the pinned $crs_bytes-byte prefix (sha256 $crs_sha)"
echo "crs: $crs_bytes bytes, sha256 $crs_sha ($crs_from)"

# --- 6. rebuild and compare -------------------------------------------------------
: > "$WORK/results.txt"
for c in "${CIRCUITS[@]}"; do
  C="$(cap "$c")"; out="$WORK/$c"; mkdir -p "$out"
  committed="$WORK/pool/contracts/src/verifiers/${C}Verifier.sol"
  (cd "$WORK/pool" && HOME="$WORK/home" "$NARGO" compile --package "$c") > "$out/nargo.log" 2>&1 \
    || { tail -20 "$out/nargo.log"; fail build "nargo compile --package $c (see $out/nargo.log)"; }
  acir="$(python3 -c 'import base64,gzip,hashlib,json,sys; print(hashlib.sha256(gzip.decompress(base64.b64decode(json.load(open(sys.argv[1]))["bytecode"]))).hexdigest())' "$WORK/pool/target/$c.json")"
  "$BB" write_vk -b "$WORK/pool/target/$c.json" -o "$out/vk" -t evm -c "$WORK/crs" > "$out/bb.log" 2>&1 \
    || { tail -20 "$out/bb.log"; fail build "bb write_vk for $c (see $out/bb.log)"; }
  "$BB" write_solidity_verifier -k "$out/vk/vk" -o "$out/${C}Verifier.sol" >> "$out/bb.log" 2>&1 \
    || { tail -20 "$out/bb.log"; fail build "bb write_solidity_verifier for $c (see $out/bb.log)"; }
  vkh="0x$(hex "$out/vk/vk_hash")"
  committed_vkh="$(sed -n 's/^uint256 constant VK_HASH = \(0x[0-9a-fA-F]*\);$/\1/p' "$committed")"
  gen_sol="$(sha "$out/${C}Verifier.sol")"
  printf '%s acir_sha256 %s\n%s vk_sha256 %s\n%s vk_hash %s\n%s gen_sol_sha256 %s\n' \
    "$c" "$acir" "$c" "$(sha "$out/vk/vk")" "$c" "$vkh" "$c" "$gen_sol" >> "$WORK/results.txt"
  cmp -s "$out/${C}Verifier.sol" "$committed"; r=$?
  [ $r -le 1 ] || fail build "cmp could not compare $out/${C}Verifier.sol with the committed file"
  if [ $r -eq 1 ]; then
    echo "first difference ($(cmp "$out/${C}Verifier.sol" "$committed" 2>&1 | sed 's/.*differ: //')):"
    diff "$committed" "$out/${C}Verifier.sol" | head -6
    fail verifier "generated ${C}Verifier.sol is not byte-identical to the committed file"
  fi
  [ "$vkh" = "$committed_vkh" ] || fail vk_hash "$c: bb vk_hash $vkh, committed VK_HASH $committed_vkh"
  [ "$acir" = "$(expected "$c" acir_sha256)" ] || fail expected "$c ACIR sha256 $acir, expected.json has $(expected "$c" acir_sha256)"
  [ "$(sha "$out/vk/vk")" = "$(expected "$c" vk_sha256)" ] || fail expected "$c vk sha256 differs from expected.json"
  [ "$vkh" = "$(expected "$c" vk_hash)" ] || fail expected "$c vk_hash differs from expected.json"
  [ "$gen_sol" = "$(expected "$c" sol_sha256)" ] || fail expected "$c verifier sha256 differs from expected.json"
  echo "$c: ACIR ${acir:0:16}, vk_hash ${vkh:0:18} == committed VK_HASH, ${C}Verifier.sol byte-identical"
done
echo "CHECK PASS: 3 verifiers byte-identical, 3 key hashes equal VK_HASH${UNPINNED:+ (unpinned build:$UNPINNED)}, ${SECONDS}s"
