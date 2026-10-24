#!/usr/bin/env bash
# Build the Kontrol project and the replay project of one suite (../check.sh calls it).
# Usage: scripts/setup-suite.sh <suite> <new-work-dir>
# Writes <work-dir>/kontrol (the project that kontrol build and kontrol prove read) and
# <work-dir>/replay (the same sources plus the replay tests, for forge test on the host).
# Env: POCS (an ethsystems/pocs clone that holds the pin, read by git only), SOLDEER_DEPS (the
# unpacked soldeer packages), ZKKIT_GIT (a zk-kit.solidity clone that holds the lock rev),
# CHEATS_GIT (a kontrol-cheatcodes clone that holds the pinned commit).
set -euo pipefail
export LC_ALL=C
SUITE=$1; W=$2
PKG=$(cd "$(dirname "$0")/.." && pwd)
pin() { sed -n "s/^$1 \([^ ]*\).*$/\1/p" "$PKG/PINS.txt" | head -1; }
PIN=$(pin pocs_commit); SUB=$(pin pocs_dir)
: "${POCS:?}" "${SOLDEER_DEPS:?}" "${ZKKIT_GIT:?}" "${CHEATS_GIT:?}"
H="$PKG/harness/$SUITE"
[ -d "$H" ] || { echo "no suite $SUITE"; exit 2; }
[ ! -e "$W" ] || { echo "work dir exists: $W"; exit 2; }
P="$W/kontrol"
mkdir -p "$P/dependencies"; W=$(cd "$W" && pwd); P="$W/kontrol"

# 1. The pool sources: git archive of the pinned commit, never the working tree; every exported
#    file must hash to its blob at the pin.
PATHS="$SUB/foundry.toml $SUB/soldeer.lock $SUB/contracts/src"
git -C "$POCS" archive "$PIN" $PATHS | tar -x --strip-components=3 -C "$P"
git -C "$POCS" ls-tree -r "$PIN" $PATHS | awk -v s="$SUB/" '{sub(s, "", $4); print $3, $4}' | sort -k2 > "$W/export-manifest.txt"
(cd "$P" && find . -type f -not -path './dependencies/*' | sed 's|^\./||' | sort \
  | while read -r f; do echo "$(git hash-object "$f") $f"; done) > "$W/export-check.txt"
cmp -s "$W/export-manifest.txt" "$W/export-check.txt" || { diff "$W/export-manifest.txt" "$W/export-check.txt"; echo "export differs from the pin"; exit 1; }
[ "$(sha256sum < "$P/contracts/src/ShieldedPool.sol" | cut -c1-64)" = "$(pin pool_sha256)" ] || { echo "ShieldedPool.sol sha256 differs"; exit 1; }

# 2. Dependencies: the three soldeer packages and zk-kit.solidity as the pinned soldeer.lock names
#    them (check.sh has checked their hashes), and kontrol-cheatcodes at its pinned commit.
for d in forge-std-1.14.0 poseidon-solidity-0.0.5 @openzeppelin-contracts-5.6.0-rc.1; do cp -a "$SOLDEER_DEPS/$d" "$P/dependencies/"; done
mkdir "$P/dependencies/zk-kit-v1"; git -C "$ZKKIT_GIT" archive "$(pin zkkit_rev)" | tar -x -C "$P/dependencies/zk-kit-v1"
mkdir "$P/dependencies/kontrol-cheatcodes"; git -C "$CHEATS_GIT" archive "$(pin cheats_rev)" | tar -x -C "$P/dependencies/kontrol-cheatcodes"

# 3. The foundry.toml patch (scripts/foundry-kontrol.txt, after optimizer_runs; one remapping after
#    forge-std's). Kontrol needs the AST and the storage layouts; ShieldedPool links the external
#    libraries LeanIMT and PoseidonT3, so the pool's bytecode carries fixed addresses and each
#    harness etches the library code there in setUp. Nothing else in the export changes.
cp "$P/foundry.toml" "$W/foundry.toml.orig"
sed -i '/^optimizer_runs = 100$/r '"$PKG/scripts/foundry-kontrol.txt" "$P/foundry.toml"
sed -i 's#^    "forge-std/=dependencies/forge-std-1.14.0",$#&\n    "kontrol-cheatcodes/=dependencies/kontrol-cheatcodes/src/",#' "$P/foundry.toml"
# A suite whose harness links more libraries (insert-loop: the mutant LeanIMT copies) lists them in
# harness/<suite>/foundry-libraries.txt; they go after the PoseidonT3 line.
EXTRA=0
if [ -f "$H/foundry-libraries.txt" ]; then
  sed -i '/PoseidonT3.sol:PoseidonT3:0x00000000000000000000000000000000000A1002",$/r '"$H/foundry-libraries.txt" "$P/foundry.toml"
  EXTRA=$(wc -l < "$H/foundry-libraries.txt")
fi
diff "$W/foundry.toml.orig" "$P/foundry.toml" > "$W/foundry.toml.diff" || true
[ "$(grep -c '^> ' "$W/foundry.toml.diff")" -eq "$(( $(wc -l < "$PKG/scripts/foundry-kontrol.txt") + 1 + EXTRA ))" ] \
  && [ "$(grep -c '^< ' "$W/foundry.toml.diff")" -eq 0 ] || { cat "$W/foundry.toml.diff"; echo "foundry.toml patch not as documented"; exit 1; }

# 4. The harness and the mutants of this suite. Files named *Replay.t.sol go to the replay project
#    only: Kontrol never builds them.
mkdir -p "$P/contracts/test/$SUITE"
shopt -s nullglob
for f in "$H"/*.sol; do case "$f" in *Replay.t.sol) ;; *) cp "$f" "$P/contracts/test/$SUITE/" ;; esac; done
[ ! -d "$PKG/mutants/$SUITE" ] || python3 "$PKG/mutants/make.py" "$SUITE" "$P"
cp -a "$P" "$W/replay"
for f in "$H"/*Replay.t.sol; do cp "$f" "$W/replay/contracts/test/$SUITE/"; done
# The container runs as another user: it must be able to write the Kontrol project.
chmod -R a+rwX "$P"
echo "setup $SUITE: $(wc -l < "$W/export-manifest.txt") files equal their blobs at ${PIN:0:7}; foundry.toml patch; $(ls "$P/contracts/test/$SUITE" | grep -c '\.sol$') harness files; $(ls "$P/contracts/test/$SUITE/mutants" 2>/dev/null | wc -l) mutants"
