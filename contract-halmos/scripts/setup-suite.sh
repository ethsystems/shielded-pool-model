#!/usr/bin/env bash
# Build the Foundry project of one suite (../check.sh calls it).
# Usage: scripts/setup-suite.sh <suite> <new-project-dir>
# Env: POCS (an ethsystems/pocs clone that holds the pin, read by git only), SOLDEER_DEPS (the
# unpacked soldeer packages), ZKKIT_GIT (a zk-kit.solidity clone that holds the lock rev), SOLC (the
# solc binary forge must use), forge 1.8.3 first on PATH.
set -euo pipefail
export LC_ALL=C
SUITE=$1; P=$2
PKG=$(cd "$(dirname "$0")/.." && pwd)
pin() { sed -n "s/^$1 \([^ ]*\).*$/\1/p" "$PKG/PINS.txt" | head -1; }
PIN=$(pin pocs_commit); SUB=$(pin pocs_dir)
: "${POCS:?}" "${SOLDEER_DEPS:?}" "${ZKKIT_GIT:?}" "${SOLC:?}"
[ -d "$PKG/harness/$SUITE" ] || { echo "no suite $SUITE"; exit 2; }
[ ! -e "$P" ] || { echo "project exists: $P"; exit 2; }
mkdir -p "$P/dependencies"; P=$(cd "$P" && pwd)

# 1. The pool sources: git archive of the pinned commit, never the working tree; every exported
#    file must hash to its blob at the pin.
PATHS="$SUB/foundry.toml $SUB/soldeer.lock $SUB/contracts/src"
git -C "$POCS" archive "$PIN" $PATHS | tar -x --strip-components=3 -C "$P"
git -C "$POCS" ls-tree -r "$PIN" $PATHS | awk -v s="$SUB/" '{sub(s, "", $4); print $3, $4}' | sort -k2 > "$P/export-manifest.txt"
(cd "$P" && find . -type f -not -path './dependencies/*' -not -name 'export-*.txt' | sed 's|^\./||' | sort \
  | while read -r f; do echo "$(git hash-object "$f") $f"; done) > "$P/export-check.txt"
cmp -s "$P/export-manifest.txt" "$P/export-check.txt" || { diff "$P/export-manifest.txt" "$P/export-check.txt"; echo "export differs from the pin"; exit 1; }
[ "$(sha256sum < "$P/contracts/src/ShieldedPool.sol" | cut -c1-64)" = "$(pin pool_sha256)" ] || { echo "ShieldedPool.sol sha256 differs"; exit 1; }

# 2. Dependencies, as the pinned soldeer.lock names them (check.sh has checked their hashes).
for d in forge-std-1.14.0 poseidon-solidity-0.0.5 @openzeppelin-contracts-5.6.0-rc.1; do cp -a "$SOLDEER_DEPS/$d" "$P/dependencies/"; done
mkdir "$P/dependencies/zk-kit-v1"; git -C "$ZKKIT_GIT" archive "$(pin zkkit_rev)" | tar -x -C "$P/dependencies/zk-kit-v1"

# 3. The library-address patch. ShieldedPool links the external libraries LeanIMT and PoseidonT3.
#    Halmos fills link placeholders only in the test contract, so the pool's bytecode must carry
#    fixed addresses: foundry.toml gets a libraries block (4 lines after optimizer_runs), and each
#    harness etches the library code at that address in setUp. Nothing else in the export changes.
cp "$P/foundry.toml" "$P/foundry.toml.orig"
sed -i '/^optimizer_runs = 100$/r '"$PKG/scripts/foundry-libraries.txt" "$P/foundry.toml"
diff "$P/foundry.toml.orig" "$P/foundry.toml" > "$P/foundry.toml.diff" || true
[ "$(grep -c '^> ' "$P/foundry.toml.diff")" -eq 4 ] && [ "$(grep -c '^< ' "$P/foundry.toml.diff")" -eq 0 ] || { echo "library patch not as documented"; exit 1; }
rm "$P/foundry.toml.orig"

# 4. The harness and the mutants of this suite.
mkdir -p "$P/contracts/test/$SUITE"
cp "$PKG/harness/$SUITE/"*.sol "$P/contracts/test/$SUITE/"
[ ! -d "$PKG/mutants/$SUITE" ] || python3 "$PKG/mutants/make.py" "$SUITE" "$P"
# Halmos and vm.getCode read the build output from out/; the pinned foundry.toml writes contracts/out.
ln -sfn contracts/out "$P/out"

# 5. Offline build with the pinned solc, the same command Halmos runs before each run.
set +e
(cd "$P" && FOUNDRY_OFFLINE=true FOUNDRY_SOLC="$SOLC" FOUNDRY_LINT_LINT_ON_BUILD=false \
  forge build --ast --extra-output storageLayout metadata) > "$P/build.log" 2>&1; rc=$?
set -e
[ "$rc" -eq 0 ] || { tail -30 "$P/build.log"; echo "build failed"; exit 1; }
grep -q "Solc $(pin solc_version | cut -d+ -f1)" "$P/build.log" || { tail -5 "$P/build.log"; echo "build did not use solc $(pin solc_version)"; exit 1; }
echo "setup $SUITE: $(wc -l < "$P/export-manifest.txt") files equal their blobs at ${PIN:0:7}; library patch; $(ls "$P/contracts/test/$SUITE" | grep -c '\.sol$') harness files; $(grep -E 'Compiling|finished' "$P/build.log" | tr '\n' ' ')"
