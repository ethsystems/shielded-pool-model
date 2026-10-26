#!/usr/bin/env bash
# Deployment check (see README.md): do the contracts at the claimed addresses run the code of
# ethsystems/pocs a04b8b3? Needs bash, git, python3, curl, sha256sum, tar, the pocs submodule
# (git -C deployment submodule update --init pocs), forge and cast 1.8.3, and an RPC that serves
# state and logs at the claimed block.
#   ./check.sh <rpc> <claim.json> [out-dir]   fetch and check the inputs, rebuild a04b8b3 offline,
#                                             compare the chain with the rebuild; last line VERDICT
#   ./check.sh --controls <rpc> <claim.json>  run the unchanged claim, then five planted claim
#                                             changes (six when it names logsFromBlock), each of which
#                                             must fail at exactly its checks
# Env: FORGE, CAST (default: from PATH), SOLC (solc 0.8.37; default: the svm copy, else a download
# into DEPS_CACHE), POCS (the pocs checkout; default ./pocs), DEPS_CACHE (downloads, by hash;
# default ./.deps), SOLC_FETCH=0 (never download solc), TOOLS_UNPINNED=1 (accept a forge, cast or
# solc binary whose sha256 is not the pinned Linux x86_64 build; its version must still match),
# NO_NETNS=1 (build without a network namespace where unshare -rn is not permitted), LOG_WINDOW
# (blocks per eth_getLogs query when the claim names logsFromBlock; default 10000).
# Relative paths are taken from the caller's directory.
set -uo pipefail
# The helper scripts validate with assert statements, which PYTHONOPTIMIZE would strip.
unset PYTHONOPTIMIZE
CALLER="$(pwd)"
rel() { case "$1" in /*|"") printf '%s' "$1" ;; *) printf '%s/%s' "$CALLER" "$1" ;; esac; }
FORGE="$(rel "${FORGE:-$(command -v forge || true)}")"
CAST="$(rel "${CAST:-$(command -v cast || true)}")"
[ -z "${SOLC:-}" ] || SOLC="$(rel "$SOLC")"
cd "$(dirname "$0")"
PKG="$(pwd)"
POCS="$(rel "${POCS:-$PKG/pocs}")"
DEPS_CACHE="$(rel "${DEPS_CACHE:-$PKG/.deps}")"
UNPINNED=""

pin() { sed -n "s/^$1 \(.*\)$/\1/p" "$PKG/PINS.txt" | head -1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
fail() { echo "FAIL $1: $2"; echo "VERDICT FAIL ($1) after ${SECONDS}s"; exit 1; }
usage() { echo "usage: ./check.sh <rpc> <claim.json> [out-dir] | ./check.sh --controls <rpc> <claim.json>" >&2; exit 2; }

# --- controls ----------------------------------------------------------------------
if [ "${1:-}" = "--controls" ]; then
  [ $# -eq 3 ] || usage
  RPC="$2"; CLAIM="$(rel "$3")"
  T="$PKG/work/controls"; rm -rf "$T"; mkdir -p "$T"
  # Each plant changes the claim only; the chain, the source and the build stay as they are.
  python3 - "$CLAIM" "$T" <<'PY' || { echo "CONTROLS FAIL: cannot write the planted claims"; exit 1; }
import json, sys
claim = json.load(open(sys.argv[1])); out = sys.argv[2]
dead = "0x000000000000000000000000000000000000dead"
plants = {
    "unchanged": ({}, [], []),
    "wrong-registry": ({"registry": claim["depositTranscriptLib"]}, ["CODE:registry", "METADATA:registry", "WIRING"], []),
    "swapped-verifiers": ({"depositVerifier": claim["transferVerifier"], "transferVerifier": claim["depositVerifier"]},
                          ["CODE:depositVerifier", "CODE:transferVerifier", "CODE:composite", "SLOTS",
                           "METADATA:depositVerifier", "METADATA:transferVerifier"], []),
    "wrong-owner": ({"owner": dead}, ["OWNER"], []),
    "extra-token": ({"supportedTokens": claim["supportedTokens"] + [dead]}, ["TOKENS"], []),
    "wrong-block-hash": ({"blockHash": "0x" + "00" * 32}, ["CHAIN"], None),
    # Logs read from the claimed block only, after the pool's creation: the guard sees pool code
    # before them, and the owner history loses its first log.
    **({"late-logs": ({"logsFromBlock": claim["block"]}, ["EVENTS", "OWNER"], [])} if "logsFromBlock" in claim else {}),
}
with open(f"{out}/plants.txt", "w") as f:
    for name, (change, failing, warns) in plants.items():
        json.dump({**claim, **change}, open(f"{out}/{name}.json", "w"), indent=2)
        f.write(f"{name} {','.join(sorted(failing)) or '-'} {'skipped' if warns is None else ','.join(sorted(warns)) or '-'}\n")
PY
  verdict() { python3 -c '
import re, sys
m = re.search(r"^VERDICT (PASS|FAIL) failing=\[([^\]]*)\](?: warnings=\[([^\]]*)\])?", sys.stdin.read(), re.M)
if not m:
    sys.exit("no VERDICT line")
f = lambda s: ",".join(sorted(x.strip().strip(chr(39)) for x in s.split(",") if x.strip())) or "-"
print(f(m.group(2)), "skipped" if m.group(3) is None else f(m.group(3)))'; }
  n=0; base_warn=""
  while read -r name want_fail want_warn; do
    out="$(bash "$PKG/check.sh" "$RPC" "$T/$name.json" "$T/run-$name" 2>&1)"; rc=$?
    rm -rf "$T/run-$name"
    got="$(verdict <<<"$out")" || { echo "CONTROLS FAIL: $name printed no VERDICT"; echo "$out" | tail -20; exit 1; }
    got_fail="${got% *}"; got_warn="${got#* }"
    if [ "$name" = unchanged ]; then
      [ $rc -eq 0 ] && [ "$got_fail" = - ] || { echo "CONTROLS FAIL: the unchanged claim should pass"; echo "$out" | tail -20; exit 1; }
      base_warn="$got_warn"
      echo "CONTROLS ok: unchanged passes (warnings: $got_warn)"
    else
      # Expected warnings: the plant's own, plus those the unchanged claim already has.
      [ "$want_warn" = skipped ] || want_warn="$(tr ',' '\n' <<<"$want_warn,$base_warn" | grep -v '^-\?$' | LC_ALL=C sort -u | paste -sd, -)"
      [ -n "$want_warn" ] || want_warn=-
      got_warn_s="$( [ "$got_warn" = skipped ] && echo skipped || { tr ',' '\n' <<<"$got_warn" | grep -v '^-\?$' | LC_ALL=C sort -u | paste -sd, -; } )"
      [ -n "$got_warn_s" ] || got_warn_s=-
      [ $rc -ne 0 ] && [ "$got_fail" = "$want_fail" ] && [ "$got_warn_s" = "$want_warn" ] \
        || { echo "CONTROLS FAIL: $name: failing=$got_fail warnings=$got_warn_s, expected failing=$want_fail warnings=$want_warn"; echo "$out" | grep -E '^(CHECK|VERDICT|FAIL)' | tail -40; exit 1; }
      echo "CONTROLS ok: $name fails at $want_fail (warnings: $want_warn)"
    fi
    n=$((n + 1))
  done < "$T/plants.txt"
  echo "CONTROLS PASS: $n claims, ${SECONDS}s"
  exit 0
fi
[ $# -ge 2 ] && [ $# -le 3 ] || usage
RPC="$1"; CLAIM="$(rel "$2")"
[ -r "$CLAIM" ] || fail claim "cannot read $CLAIM"
if [ -n "${3:-}" ]; then
  OUT="$(rel "$3")"; [ ! -e "$OUT" ] || fail usage "out-dir exists: $OUT"
else
  OUT="$PKG/work/$(basename "$CLAIM" .json)"; rm -rf "$OUT"
fi
mkdir -p "$(dirname "$OUT")"
T="$(mktemp -d "${TMPDIR:-/tmp}/deployment-check.XXXXXX")"
trap 'rm -rf "$T"' EXIT

# --- 1. tools ------------------------------------------------------------------------
hint() {
  echo "  install forge and cast $(pin forge_version): $(pin foundry_asset)"
  echo "    (unpack; binary sha256 forge $(pin forge_sha256), cast $(pin cast_sha256))"
  echo "    then: FORGE=/path/to/forge CAST=/path/to/cast ./check.sh ..."
  echo "  solc $(pin solc_version): $(pin solc_url) (sha256 $(pin solc_sha256)); check.sh downloads it unless SOLC_FETCH=0"
}
binpin() { # name, binary, pinned sha256
  [ "$(sha "$2")" = "$3" ] && return 0
  [ "${TOOLS_UNPINNED:-0}" = 1 ] || { hint; fail tools "$1 binary sha256 $(sha "$2") is not the pinned build $3 (TOOLS_UNPINNED=1 accepts another build of the same version)"; }
  UNPINNED="$UNPINNED $1"
}
for t in FORGE CAST; do
  [ -n "${!t}" ] && [ -x "${!t}" ] || { hint; fail tools "$t not found (set $t=/path or install)"; }
done
for t in forge cast; do
  bin="$FORGE"; [ "$t" = cast ] && bin="$CAST"
  v="$("$bin" --version 2>/dev/null | tr '\n' ' ')"
  grep -qF "Version: $(pin forge_version)" <<<"$v" && grep -qF "$(pin forge_commit)" <<<"$v" \
    || { hint; fail tools "$t is '$v', pinned $(pin forge_version) at $(pin forge_commit)"; }
done
binpin forge "$FORGE" "$(pin forge_sha256)"
binpin cast "$CAST" "$(pin cast_sha256)"
solc_ver="$(pin solc_version)"; solc_sha="$(pin solc_sha256)"
if [ -z "${SOLC:-}" ]; then
  for s in "$HOME/.svm/${solc_ver%%+*}/solc-${solc_ver%%+*}" "${XDG_DATA_HOME:-$HOME/.local/share}/svm/${solc_ver%%+*}/solc-${solc_ver%%+*}" "$DEPS_CACHE/solc-$solc_ver"; do
    [ -x "$s" ] && { SOLC="$s"; break; }
  done
fi
if [ -z "${SOLC:-}" ]; then
  [ "${SOLC_FETCH:-1}" = 1 ] || { hint; fail tools "no solc ${solc_ver%%+*} found and SOLC_FETCH=0"; }
  mkdir -p "$DEPS_CACHE"
  curl -sSfL -o "$T/solc" "$(pin solc_url)" || fail tools "cannot download $(pin solc_url)"
  [ "$(sha "$T/solc")" = "$solc_sha" ] || fail tools "downloaded solc has sha256 $(sha "$T/solc"), pinned $solc_sha"
  chmod +x "$T/solc" && mv "$T/solc" "$DEPS_CACHE/solc-$solc_ver" && SOLC="$DEPS_CACHE/solc-$solc_ver"
fi
[ -x "$SOLC" ] || fail tools "SOLC=$SOLC is not executable"
"$SOLC" --version 2>/dev/null | grep -qF "Version: $solc_ver" || fail tools "solc $SOLC is not $solc_ver"
binpin solc "$SOLC" "$solc_sha"
# recheck-deploy.sh and deploy-check.py call forge and cast by name: put these two first on PATH.
mkdir -p "$T/bin" && ln -s "$FORGE" "$T/bin/forge" && ln -s "$CAST" "$T/bin/cast"
export PATH="$T/bin:$PATH" SOLC
echo "tools: forge and cast $(pin forge_version) ($FORGE, $CAST), solc $solc_ver ($SOLC)${UNPINNED:+; unpinned build:$UNPINNED}"

# --- 2. source -----------------------------------------------------------------------
# recheck-deploy.sh exports the pinned commit with git archive; here the 16 blob ids of that
# commit must equal the pins, so a different pin or a different file set stops before any build.
commit="$(pin pocs_commit)"; dir="$(pin pocs_dir)"
[ -e "$POCS/.git" ] || fail source "no pocs checkout at $POCS (run: git -C $PKG submodule update --init pocs)"
git -C "$POCS" cat-file -e "$commit^{commit}" 2>/dev/null || fail source "pocs at $POCS does not hold $commit"
git -C "$POCS" ls-tree -r "$commit" "$dir/foundry.toml" "$dir/soldeer.lock" "$dir/contracts/src" "$dir/contracts/script" \
  | awk -v s="$dir/" '{sub(s, "", $4); print $3, $4}' | LC_ALL=C sort -k2 > "$T/manifest.txt"
sed -n 's/^blob //p' PINS.txt | LC_ALL=C sort -k2 > "$T/manifest.pinned"
diff "$T/manifest.pinned" "$T/manifest.txt" > "$T/manifest.diff" || { cat "$T/manifest.diff"; fail source "blob ids at $commit differ from the blob pins in PINS.txt"; }
echo "source: pocs $commit, $(wc -l < "$T/manifest.txt") files under $dir equal the blob pins"

# --- 3. dependencies -------------------------------------------------------------------
# The three soldeer zips, by the url and checksum of the pinned lock, kept in DEPS_CACHE by sha256;
# zk-kit.solidity at the lock rev, kept as a git repository in DEPS_CACHE.
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
  echo "deps: $name zip sha256 $want"
  nzip=$((nzip + 1))
done < "$T/zips.txt"
[ "$nzip" -eq "$(grep -c '^zip_sha256 ' PINS.txt)" ] || fail deps "the lock names $nzip soldeer packages, PINS.txt pins $(grep -c '^zip_sha256 ' PINS.txt)"
ZK="$DEPS_CACHE/zk-kit.solidity"; rev="$(pin zkkit_rev)"
if ! git -C "$ZK" cat-file -e "$rev^{commit}" 2>/dev/null; then
  rm -rf "$ZK"; git init -q "$ZK" && git -C "$ZK" fetch -q --depth 1 "$(pin zkkit_repo)" "$rev" || fail deps "cannot fetch $(pin zkkit_repo) at $rev"
fi
tree="$(git -C "$ZK" rev-parse "$rev^{tree}")"
[ "$tree" = "$(pin zkkit_tree)" ] || fail deps "zk-kit $rev has tree $tree, pinned $(pin zkkit_tree)"
echo "deps: zk-kit.solidity $rev tree $tree"

# --- 4. export, integrity, offline build, compare (scripts/recheck-deploy.sh) ----------
POCS="$POCS" SOLDEER_DEPS="$T/soldeer" ZKKIT_GIT="$ZK" bash "$PKG/scripts/recheck-deploy.sh" "$RPC" "$CLAIM" "$OUT" 2>&1 | tee "$T/recheck.log"
rc=${PIPESTATUS[0]}
# No VERDICT line: the export, integrity or build step failed, or the comparison stopped (an RPC error).
grep -q '^VERDICT ' "$T/recheck.log" || { [ $rc -ne 0 ] || rc=1; echo "VERDICT FAIL (no verdict from scripts/recheck-deploy.sh: see the lines above)"; }
echo "check.sh: exit $rc, out-dir $OUT, ${SECONDS}s${UNPINNED:+ (unpinned build:$UNPINNED)}"
exit $rc
