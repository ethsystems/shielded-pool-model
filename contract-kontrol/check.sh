#!/usr/bin/env bash
# Kontrol proofs about ShieldedPool.sol at ethsystems/pocs a04b8b3 (see README.md). Needs bash, git,
# python3, curl, sha256sum, tar, patch, docker (with the right to run containers), the pocs submodule
# (git -C contract-kontrol submodule update --init pocs), forge 1.8.3 and solc 0.8.37 on the host.
#   ./check.sh [suite[:run[,run...]]...]   for each suite (default: every suite of harness/SUITES.txt),
#       export the pin, build the Kontrol project in the pinned image, run the selected kontrol prove
#       runs of harness/<suite>/runs.tsv (default: all), run the forge replays on the host, and compare
#       every verdict and every failing node's output with EXPECTED.tsv. Prints CHECK PASS|FAIL per suite
#       and a last line CHECK PASS|FAIL.
# Env: FORGE, CAST (default: from PATH), SOLC (solc 0.8.37; default: the svm copy, else a download into
# DEPS_CACHE), POCS (default ./pocs), DEPS_CACHE (default ./.deps), WORK (default ./work), SOLC_FETCH=0
# (never download solc), TOOLS_UNPINNED=1 (accept a forge or solc binary whose sha256 is not the pinned
# Linux x86_64 build; its version must still match), PULL=0 (never pull the image), CAP (container
# memory cap, default 8g), BUILD_CPUSET and PROVE_CPUSET (docker --cpuset-cpus for kontrol build
# and kontrol prove, default 0-1 and 0-5: fewer CPUs keep the kompile below the cap), TLIM (seconds per container, default 7200), GATE_GIB (available memory
# before each container starts, default 10).
# Relative paths are taken from the caller's directory.
set -uo pipefail
CALLER="$(pwd)"
rel() { case "$1" in /*|"") printf '%s' "$1" ;; *) printf '%s/%s' "$CALLER" "$1" ;; esac; }
FORGE="$(rel "${FORGE:-$(command -v forge || true)}")"
CAST="$(rel "${CAST:-$(command -v cast || true)}")"
[ -z "${SOLC:-}" ] || SOLC="$(rel "$SOLC")"
cd "$(dirname "$0")"
PKG="$(pwd)"
POCS="$(rel "${POCS:-$PKG/pocs}")"
DEPS_CACHE="$(rel "${DEPS_CACHE:-$PKG/.deps}")"
WORK="$(rel "${WORK:-$PKG/work}")"
UNPINNED=""

pin() { sed -n "s/^$1 \([^ ]*\).*$/\1/p" "$PKG/PINS.txt" | head -1; }
sha() { sha256sum "$1" | cut -d' ' -f1; }
fail() { echo "FAIL $1: $2"; echo "CHECK FAIL ($1) after ${SECONDS}s"; exit 1; }

SUITES=(); declare -A SELECT
for a in "$@"; do
  case "$a" in
    -*) echo "usage: ./check.sh [suite[:run[,run...]]...]" >&2; exit 2 ;;
    *) s="${a%%:*}"; [ -d "$PKG/harness/$s" ] || fail usage "no suite $s"; SUITES+=("$s")
       [ "$a" = "$s" ] || SELECT[$s]="${a#*:}" ;;
  esac
done
[ ${#SUITES[@]} -gt 0 ] || mapfile -t SUITES < <(sed -n 's/^suite //p' "$PKG/harness/SUITES.txt")
T="$(mktemp -d "${TMPDIR:-/tmp}/contract-kontrol.XXXXXX")"
trap 'rm -rf "$T"' EXIT

# --- 1. tools ------------------------------------------------------------------------
binpin() { # name, binary, pinned sha256
  [ "$(sha "$2")" = "$3" ] && return 0
  [ "${TOOLS_UNPINNED:-0}" = 1 ] || fail tools "$1 binary sha256 $(sha "$2") is not the pinned build $3 (TOOLS_UNPINNED=1 accepts another build of the same version)"
  UNPINNED="$UNPINNED $1"
}
command -v python3 >/dev/null || fail tools "python3 not found"
command -v patch >/dev/null || fail tools "patch not found"
[ -n "$FORGE" ] && [ -x "$FORGE" ] || fail tools "forge not found (set FORGE=/path; $(pin foundry_asset))"
[ -n "$CAST" ] && [ -x "$CAST" ] || fail tools "cast not found (set CAST=/path; $(pin foundry_asset))"
"$CAST" --version 2>/dev/null | grep -qF "Version: $(pin forge_version)" || fail tools "cast is not $(pin forge_version)"
binpin cast "$CAST" "$(pin cast_sha256)"
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
SOLC="$(readlink -f "$SOLC")"
"$SOLC" --version 2>/dev/null | grep -qF "Version: $solc_ver" || fail tools "solc $SOLC is not $solc_ver"
binpin solc "$SOLC" "$solc_sha"
export SOLC
IMAGE="$(pin kontrol_image)@$(pin kontrol_image_digest)"
# Docker is needed only when a selected suite has a Kontrol build.
NEED_DOCKER=0
for s in "${SUITES[@]}"; do grep -q $'^build\t' "$PKG/harness/$s/runs.tsv" && NEED_DOCKER=1; done
if [ "$NEED_DOCKER" = 1 ]; then
command -v docker >/dev/null || fail tools "docker not found"
if ! docker image inspect "$IMAGE" >/dev/null 2>&1; then
  [ "${PULL:-1}" = 1 ] || fail tools "image $IMAGE not present and PULL=0"
  docker pull "$IMAGE" >/dev/null || fail tools "cannot pull $IMAGE"
fi
[ "$(docker image inspect "$IMAGE" --format '{{.Id}}')" = "$(pin kontrol_image_digest)" ] || fail tools "image id of $IMAGE is not $(pin kontrol_image_digest)"
kv="$(docker run --rm --network none "$IMAGE" kontrol version 2>/dev/null | tr -d '\r')"
[ "$kv" = "Kontrol version: $(pin kontrol_version)" ] || fail tools "the image reports '$kv', pinned Kontrol $(pin kontrol_version)"
# The KEVM abi.md: the image's file must be the pinned stock file, and kevm-patch/abi.md must be that
# file with exactly the deletion of kevm-patch/abi.md.diff.
docker run --rm --network none "$IMAGE" cat "$(pin kevm_abi_path)" > "$T/abi.stock" || fail tools "cannot read abi.md from the image"
[ "$(sha "$T/abi.stock")" = "$(pin kevm_abi_stock_sha256)" ] || fail tools "the image's abi.md has sha256 $(sha "$T/abi.stock"), pinned $(pin kevm_abi_stock_sha256)"
cp "$T/abi.stock" "$T/abi.patched" && patch -s "$T/abi.patched" "$PKG/kevm-patch/abi.md.diff" || fail tools "kevm-patch/abi.md.diff does not apply to the image's abi.md"
[ "$(sha "$T/abi.patched")" = "$(pin kevm_abi_patched_sha256)" ] && [ "$(sha "$PKG/kevm-patch/abi.md")" = "$(pin kevm_abi_patched_sha256)" ] \
  || fail tools "kevm-patch/abi.md is not the image's abi.md with the pinned deletion"
[ "$(sha "$PKG/lemmas/bytes-prefix.k")" = "$(pin lemma_sha256)" ] || fail tools "lemmas/bytes-prefix.k differs from its pin"
echo "tools: Kontrol $(pin kontrol_version) ($IMAGE), abi.md stock $(pin kevm_abi_stock_sha256 | cut -c1-8) and patched $(pin kevm_abi_patched_sha256 | cut -c1-8), forge and cast $(pin forge_version) ($FORGE), solc $solc_ver ($SOLC)${UNPINNED:+; unpinned build:$UNPINNED}"
else
echo "tools: no Kontrol run selected, Docker not used; forge and cast $(pin forge_version) ($FORGE), solc $solc_ver ($SOLC)${UNPINNED:+; unpinned build:$UNPINNED}"
fi

# --- 2. source -----------------------------------------------------------------------
commit="$(pin pocs_commit)"; dir="$(pin pocs_dir)"
[ -e "$POCS/.git" ] || fail source "no pocs checkout at $POCS (run: git -C $PKG submodule update --init pocs)"
git -C "$POCS" cat-file -e "$commit^{commit}" 2>/dev/null || fail source "pocs at $POCS does not hold $commit"
git -C "$POCS" ls-tree -r "$commit" "$dir/foundry.toml" "$dir/soldeer.lock" "$dir/contracts/src" \
  | awk -v s="$dir/" '{sub(s, "", $4); print $3, $4}' | LC_ALL=C sort -k2 > "$T/manifest.txt"
sed -n 's/^blob //p' PINS.txt | LC_ALL=C sort -k2 > "$T/manifest.pinned"
diff "$T/manifest.pinned" "$T/manifest.txt" > "$T/manifest.diff" || { cat "$T/manifest.diff"; fail source "blob ids at $commit differ from the blob pins in PINS.txt"; }
echo "source: pocs $commit, $(wc -l < "$T/manifest.txt") files under $dir equal the blob pins"

# --- 3. dependencies (as deployment/check.sh), and kontrol-cheatcodes -------------------------
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
gitdep() { # name, repo, rev, tree
  local d="$DEPS_CACHE/$1"
  if ! git -C "$d" cat-file -e "$3^{commit}" 2>/dev/null; then
    rm -rf "$d"; git init -q "$d" && git -C "$d" fetch -q --depth 1 "$2" "$3" || fail deps "cannot fetch $2 at $3"
  fi
  [ "$(git -C "$d" rev-parse "$3^{tree}")" = "$4" ] || fail deps "$1 $3 has tree $(git -C "$d" rev-parse "$3^{tree}"), pinned $4"
}
gitdep zk-kit.solidity "$(pin zkkit_repo)" "$(pin zkkit_rev)" "$(pin zkkit_tree)"
gitdep kontrol-cheatcodes "$(pin cheats_repo)" "$(pin cheats_rev)" "$(pin cheats_tree)"
echo "deps: $nzip soldeer zips by sha256 and integrity, zk-kit.solidity $(pin zkkit_rev | cut -c1-8) and kontrol-cheatcodes $(pin cheats_rev | cut -c1-8) by tree"

# --- 4. per suite: setup, build, prove, replay, compare --------------------------------------
mkdir -p "$WORK"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
for s in "${SUITES[@]}"; do
  W="$WORK/$s"; L="$W/logs"
  rm -rf "$W"
  POCS="$POCS" SOLDEER_DEPS="$T/soldeer" ZKKIT_GIT="$DEPS_CACHE/zk-kit.solidity" CHEATS_GIT="$DEPS_CACHE/kontrol-cheatcodes" \
    bash "$PKG/scripts/setup-suite.sh" "$s" "$W" || fail "setup:$s" "see the lines above"
  mkdir -p "$L"; : > "$L/results.tsv"
  [ ! -d "$PKG/lemmas" ] || cp -a "$PKG/lemmas" "$W/kontrol/lemmas"
  chmod -R a+rwX "$W/kontrol"
  built=0
  while IFS=$'\t' read -r kind run abi cmd; do
    [ "$kind" = kind ] && continue
    [ -n "$kind" ] || continue
    if [ "$kind" = prove ] && [ -n "${SELECT[$s]:-}" ] && ! grep -qx "$run" <<<"$(tr ',' '\n' <<<"${SELECT[$s]}")"; then
      echo "suite $s run $run: not selected"; continue
    fi
    t0=$SECONDS
    case "$kind" in
      build)
        CPUSET="${BUILD_CPUSET:-0-1}" bash "$PKG/scripts/kontrol-run.sh" "$L/$run.txt" "$W/kontrol" "$abi" "$cmd"
        if grep -q "^BUILD_EXIT=0$" "$L/$run.txt" || { grep -q "Kontrol project built" "$L/$run.txt" && grep -q "^COMMAND_EXIT=0$" "$L/$run.txt"; }; then built=1; fi
        want_abi="$(pin "kevm_abi_${abi}_sha256")"
        grep -q "^$want_abi " "$L/$run.txt" || { echo "suite $s: the container did not see the $abi abi.md"; built=0; }
        printf '%s\t%s\t%s\t%s\t-\t-\t%ss\n' "$s" "$run" build "$([ $built = 1 ] && echo BUILT || echo BUILD-FAILED)" "$((SECONDS - t0))" >> "$L/results.tsv"
        echo "suite $s build: $([ $built = 1 ] && echo ok || echo FAILED), $((SECONDS - t0))s"
        [ $built = 1 ] || break ;;
      prove)
        [ $built = 1 ] || { echo "suite $s run $run: no build"; continue; }
        CPUSET="${PROVE_CPUSET:-0-5}" bash "$PKG/scripts/kontrol-run.sh" "$L/$run.txt" "$W/kontrol" "$abi" "$cmd"
        python3 "$PKG/scripts/kverdicts.py" "$s" "$run" "$L/$run.txt" "$W/kontrol/contracts/out/proofs" > "$L/$run.tsv"
        [ -s "$L/$run.tsv" ] || printf '%s\t%s\t-\tNO-VERDICT\t-\t-\t-\n' "$s" "$run" > "$L/$run.tsv"
        cat "$L/$run.tsv" >> "$L/results.tsv"
        echo "suite $s run $run: $((SECONDS - t0))s"; grep -P "^$s\t$run\t" "$L/results.tsv" | cut -f3-6 | sed 's/^/  /' ;;
      forge)
        (cd "$W/replay" && FOUNDRY_OFFLINE=true FOUNDRY_SOLC="$SOLC" FOUNDRY_LINT_LINT_ON_BUILD=false \
          "$FORGE" test --match-path "contracts/test/$s/$cmd" -vv) > "$L/$run.txt" 2>&1
        python3 - "$s" "$run" "$L/$run.txt" >> "$L/results.tsv" <<'PY'
import re, sys
s, run, log = sys.argv[1:4]
suite = None
for l in open(log, errors="replace"):
    l = re.sub(r"\x1b\[[0-9;]*m", "", l)
    m = re.match(r"Ran \d+ tests? for \S+:(\S+)", l)
    if m: suite = m.group(1)
    m = re.match(r"\[(PASS|FAIL)[^\]]*\] (\w+)\(", l)
    if m and suite: print(f"{s}\t{run}\t{suite}.{m.group(2)}\t{m.group(1)}\t-\t-\t-")
PY
        echo "suite $s replays: $(grep -cP "^$s\t$run\t.*\tPASS\t" "$L/results.tsv") pass, $(grep -cP "^$s\t$run\t.*\tFAIL\t" "$L/results.tsv") fail, $((SECONDS - t0))s" ;;
      controls)
        # A plain Foundry project run on the host (no Kontrol): copy it and the K claims it reads.
        rm -rf "$W/$cmd" "$W/k" "$W/zk-kit"; cp -a "$PKG/harness/$s/$cmd" "$W/$cmd"; cp -a "$PKG/harness/$s/k" "$W/k"
        mkdir "$W/zk-kit"; git -C "$DEPS_CACHE/zk-kit.solidity" archive "$(pin zkkit_rev)" | tar -x -C "$W/zk-kit"
        mkdir -p "$T/bin"; ln -sf "$FORGE" "$T/bin/forge"; ln -sf "$CAST" "$T/bin/cast"
        (cd "$W/$cmd" && PATH="$T/bin:$PATH" FOUNDRY_SOLC="$SOLC" FOUNDRY_LINT_LINT_ON_BUILD=false python3 tools/run.py \
          && PATH="$T/bin:$PATH" ZKKIT_DIR="$W/zk-kit" POSEIDON_DIR="$T/soldeer/poseidon-solidity-0.0.5" python3 tools/check_witnesses.py) > "$L/$run.txt" 2>&1
        crc=$?
        python3 - "$s" "$run" "$W/$cmd/logs/results.json" "$crc" >> "$L/results.tsv" <<'PY'
import json, os, sys
s, run, res, crc = sys.argv[1:5]
if os.path.exists(res):
    for part, r in json.load(open(res)).items():
        for x in r["results"]:
            v = x["status"] + (":" + x["reason"].replace(" ", "_") if x["reason"] else "")
            print(f"{s}\t{run}-{part}\t{x['test']}\t{v}\t-\t-\t-")
print(f"{s}\t{run}\tall-checks\t{'PASS' if crc == '0' else 'FAIL'}\t-\t-\t-")
PY
        echo "suite $s $run: $(tail -1 "$L/$run.txt"), exit $crc, $((SECONDS - t0))s" ;;
    esac
  done < "$PKG/harness/$s/runs.tsv"
done
python3 "$PKG/scripts/compare.py" "$PKG/EXPECTED.tsv" "$WORK" "${SUITES[@]}"; rc=$?
echo "check.sh: ${#SUITES[@]} suites, ${SECONDS}s, work $WORK, started $STAMP${UNPINNED:+ (unpinned build:$UNPINNED)}"
[ $rc -eq 0 ] && echo "CHECK PASS: ${#SUITES[@]} suites, ${SECONDS}s${UNPINNED:+ (unpinned build:$UNPINNED)}" || echo "CHECK FAIL: see the CHECK lines above"
exit $rc
