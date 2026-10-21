#!/usr/bin/env bash
# C1 deployment check: rebuild a04b8b3 from a fresh export, then compare a deployment with it.
# Usage: scripts/recheck-deploy.sh <rpc> <addresses.json> <new-out-dir>
# Env: POCS (an ethsystems/pocs clone that holds a04b8b3, read by git only), SOLDEER_DEPS (extracted soldeer packages),
#      ZKKIT_GIT (a zk-kit.solidity clone that holds the lock rev). forge/cast 1.8.3 and solc 0.8.37 offline.
set -euo pipefail
export LC_ALL=C
RPC=$1; CLAIM=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); OUT=$3
HERE=$(cd "$(dirname "$0")" && pwd)
PIN=a04b8b38969dfc2ee64de47edee7e396454204a8
SUB=pocs/private-payment/shielded-pool
POCS=${POCS:?set POCS to an ethsystems/pocs clone}
: "${SOLDEER_DEPS:?set SOLDEER_DEPS}" "${ZKKIT_GIT:?set ZKKIT_GIT}"
[ ! -e "$OUT" ] || { echo "output exists: $OUT"; exit 2; }
forge --version | grep -F 'Version: 1.8.3' >/dev/null || { echo 'forge 1.8.3 required'; exit 1; }
mkdir -p "$OUT/ref/dependencies"; OUT=$(cd "$OUT" && pwd); R=$OUT/ref
echo "rpc=$RPC claim=$CLAIM sha256=$(sha256sum < "$CLAIM" | cut -c1-64)"
echo "pocs=$POCS pin=$(git -C "$POCS" rev-parse "$PIN^{commit}")"

# 1. Fresh export of the pinned commit; every file must hash to its blob at the pin.
PATHS="$SUB/foundry.toml $SUB/soldeer.lock $SUB/contracts/src $SUB/contracts/script"
git -C "$POCS" archive "$PIN" $PATHS | tar -x --strip-components=3 -C "$R"
git -C "$POCS" ls-tree -r "$PIN" $PATHS | awk -v s="$SUB/" '{sub(s, "", $4); print $3, $4}' | sort -k2 > "$OUT/export-manifest.txt"
(cd "$R" && find . -type f -not -path './dependencies/*' | sed 's|^\./||' | sort | while read -r f; do echo "$(git hash-object "$f") $f"; done) > "$OUT/export-check.txt"
cmp "$OUT/export-manifest.txt" "$OUT/export-check.txt" || { echo 'export differs from the pin'; exit 1; }
echo "export: $(wc -l < "$OUT/export-manifest.txt") files, blob ids equal git ls-tree $PIN (export-manifest.txt)"

# 2. Dependencies: soldeer integrity for zips, tree id for the git dependency.
for d in forge-std-1.14.0 poseidon-solidity-0.0.5 @openzeppelin-contracts-5.6.0-rc.1; do cp -a "$SOLDEER_DEPS/$d" "$R/dependencies/"; done
ZK=$(sed -n '/name = "zk-kit"/,/^$/s/^rev = "\([0-9a-f]*\)"/\1/p' "$R/soldeer.lock")
[ "$ZK" = a171c845ec7fdc50cdd1fe96c14c27d707cdfbed ] || { echo "unexpected zk-kit rev in lock: $ZK"; exit 1; }
mkdir "$R/dependencies/zk-kit-v1"; git -C "$ZKKIT_GIT" archive "$ZK" | tar -x -C "$R/dependencies/zk-kit-v1"
echo "zk-kit: archive of $ZK, tree $(git -C "$ZKKIT_GIT" rev-parse "$ZK^{tree}")"
python3 "$HERE/soldeer-integrity.py" "$R/soldeer.lock" "$R/dependencies"

# 3. Offline build with the exported foundry.toml; no network namespace.
echo "build: (cd $R && unshare -rn forge build --offline --build-info)"
set +e; (cd "$R" && unshare -rn forge build --offline --build-info) > "$OUT/build.log" 2>&1; rc=$?; set -e
echo "build exit=$rc; $(grep -E '^Compiling|finished in' "$OUT/build.log" | tr '\n' ' ')"
[ "$rc" -eq 0 ] || exit 1

# 4. Compare the chain with the rebuild.
set +e; python3 "$HERE/deploy-check.py" "$R" "$RPC" "$CLAIM"; rc=$?; set -e
echo "deploy-check exit=$rc"
exit "$rc"
