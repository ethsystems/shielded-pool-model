#!/usr/bin/env bash
# Re-derive extracted/ from the Noir sources with the extractor of the Lampe fork, and compare.
# Optional; scripts/check.sh does not run it. It needs git, cargo (rustup), sha256sum, network
# access for the first cargo build and the two Noir dependencies, and the pocs submodule of
# circuits-acir (from the repo root: git submodule update --init circuits-acir/pocs).
#
#   scripts/extract.sh [WORK_DIR]   default WORK_DIR: build/extract
#
# Env: LAMPE_SRC (a checkout of the fork at lampe_rev; default: a fresh clone into WORK_DIR),
# POCS (default ../circuits-acir/pocs), RUST_TOOLCHAIN (default: the fork's rust-toolchain.toml).
#
# Steps: check the fork commit; build the extractor (cargo build --locked; Cargo.lock pins Noir
# at noir_git); read the three circuits from pocs at pocs_commit as git blobs and check them
# against PINS.sha256; clone the two Noir dependencies by tag, check their commits and source
# hashes, and place them where nargo looks for them (HOME/nargo/...); run the extractor on each
# circuit with that HOME and GIT_ALLOW_PROTOCOL=none, so nothing is fetched during extraction;
# compare every generated .lean file with extracted/ byte for byte.
set -euo pipefail
cd "$(dirname "$0")/.."
PKG="$(pwd)"
pin() { sed -n "s/^# $1 \(.*\)$/\1/p" PINS.sha256 | head -1; }
fail() { echo "EXTRACT FAIL: $*"; exit 1; }
W="$(realpath -m "${1:-build/extract}")"
POCS="$(realpath -m "${POCS:-$PKG/../circuits-acir/pocs}")"
rm -rf "$W/circuits" "$W/nargo-home" "$W/out"; mkdir -p "$W/circuits" "$W/nargo-home"

# 1. The fork and the extractor
rev="$(pin lampe_rev)"
if [ -z "${LAMPE_SRC:-}" ]; then
  LAMPE_SRC="$W/lampe"
  [ -d "$LAMPE_SRC/.git" ] || git clone -q "$(pin lampe_repo)" "$LAMPE_SRC"
  git -C "$LAMPE_SRC" checkout -q --detach "$rev"
fi
[ "$(git -C "$LAMPE_SRC" rev-parse HEAD)" = "$rev" ] || fail "LAMPE_SRC is not at lampe_rev $rev"
export CARGO_TARGET_DIR="$W/target"
(cd "$LAMPE_SRC" && ${RUST_TOOLCHAIN:+env RUSTUP_TOOLCHAIN=$RUST_TOOLCHAIN} cargo build --locked --release --bin lampe) \
  > "$W/cargo.log" 2>&1 || { tail -20 "$W/cargo.log"; fail "cargo build (see $W/cargo.log)"; }
LAMPE="$W/target/release/lampe"
grep -q "$(pin noir_git)" "$LAMPE_SRC/Cargo.lock" || fail "Cargo.lock does not pin Noir at $(pin noir_git)"
echo "extractor: $LAMPE (fork $rev)"

# 2. The circuit sources, as git blobs at the pocs pin
commit="$(pin pocs_commit)"; dir="$(pin pocs_dir)"
[ -e "$POCS/.git" ] || fail "no pocs checkout at $POCS"
grep '  pool/' PINS.sha256 | while read -r sum f; do
  mkdir -p "$W/circuits/$(dirname "$f")"
  git -C "$POCS" cat-file blob "$commit:$dir/${f#pool/}" > "$W/circuits/$f" || fail "$f is not in pocs at $commit"
done
(cd "$W/circuits" && grep '  pool/' "$PKG/PINS.sha256" | sha256sum --quiet --strict -c) || fail "circuit sources differ from PINS.sha256"
echo "circuits: pocs $commit, hashes match"

# 3. The Noir dependencies, by tag, with a commit check and the source hashes
sed -n 's/^# dep //p' PINS.sha256 | while read -r path head tag; do
  head="${head#head=}"; tag="${tag#tag=}"; url="https://$(dirname "${path#nargo/}")"
  dst="$W/nargo-home/$path"; rm -rf "$dst"; mkdir -p "$(dirname "$dst")"
  git -c advice.detachedHead=false clone -q --depth 1 --branch "$tag" "$url" "$dst"
  [ "$(git -C "$dst" rev-parse HEAD)" = "$head" ] || fail "$url $tag is not at $head"
done
(cd "$W/nargo-home" && grep '  nargo/' "$PKG/PINS.sha256" | sha256sum --quiet --strict -c) || fail "dependency sources differ from PINS.sha256"
echo "dependencies: commits and source hashes match"

# 4. Extract each circuit and compare
bad=0
for c in deposit withdraw transfer; do
  mkdir -p "$W/out/$c"
  cp "$W/circuits/pool/circuits/$c/Nargo.toml" "$W/out/$c/"; cp -r "$W/circuits/pool/circuits/$c/src" "$W/out/$c/"
  (HOME="$W/nargo-home" GIT_ALLOW_PROTOCOL=none "$LAMPE" --root "$W/out/$c" --overwrite) > "$W/$c.log" 2>&1 \
    || { tail -20 "$W/$c.log"; fail "extraction of $c (see $W/$c.log)"; }
  g="$W/out/$c/lampe"
  # Every generated file has a committed counterpart and the reverse: the circuit's own files
  # and each of the two shared dependency copies, with no file missing or extra.
  gen="$(cd "$g" && find . -name '*.lean' -not -path '*/.lake/*' | LC_ALL=C sort)"
  mapped="$(sed -e 's|^\./deps/\([^/]*\)/lampe/|extracted/deps/\1/|' -e "s|^\./|extracted/$c-0.0.0/|" <<<"$gen" | LC_ALL=C sort)"
  want="$(find "extracted/$c-0.0.0" extracted/deps -name '*.lean' -not -path '*/.lake/*' | LC_ALL=C sort)"
  if [ "$mapped" != "$want" ]; then
    echo "FILE SETS DIFFER for $c (< generated, > extracted/):"
    diff <(echo "$mapped") <(echo "$want") | grep '^[<>]'  || true
    bad=$((bad + 1))
  fi
  while read -r f; do
    case "$f" in
      ./deps/*) rel="extracted/deps/$(echo "$f" | sed 's|^\./deps/\([^/]*\)/lampe/|\1/|')" ;;
      *) rel="extracted/$c-0.0.0/${f#./}" ;;
    esac
    if ! cmp -s "$g/$f" "$rel"; then echo "DIFFERS: $c $f (extracted: $rel)"; bad=$((bad + 1)); fi
  done <<<"$gen"
  n=$(wc -l <<<"$gen")
  echo "extracted: $c, $n generated files compared"
done
[ "$bad" -eq 0 ] || fail "$bad differences between the generated files and extracted/"
echo "EXTRACT PASS: deposit, withdraw and transfer regenerate byte for byte"
