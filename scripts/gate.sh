#!/usr/bin/env bash
# The trusted gate. Runs in a fresh clone of the repo's committed HEAD.
set -uo pipefail
REPO="$(cd "$(dirname "$0")/.." && pwd)"
# Work dir on the repo's own filesystem, so the .lake copy below can be a
# clone or reflink, never a 7.5 GB byte copy into a RAM-backed /tmp.
GATE_WORK="${GATE_WORK:-$REPO/.gate-work}"
mkdir -p "$GATE_WORK" || { echo "GATE FAIL: work dir"; exit 1; }
WORK="$(mktemp -d "$GATE_WORK/gate.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
CLONE="$WORK/clone"
git clone --quiet "$REPO" "$CLONE" || { echo "GATE FAIL: clone"; exit 1; }
# GATE_REF: gate a candidate commit instead of the checked-out HEAD
if [ -n "${GATE_REF:-}" ]; then git -C "$CLONE" checkout --quiet "$GATE_REF" || { echo "GATE FAIL: ref"; exit 1; }; fi
# macOS clonefile, then Linux reflink, then a plain copy
copy_lake() {
  cp -Rc "$1" "$2" 2>/dev/null && return
  rm -rf "$2"; cp -R --reflink=auto "$1" "$2" 2>/dev/null && return
  rm -rf "$2"; cp -R "$1" "$2"
}
if [ -d "$REPO/.lake" ]; then copy_lake "$REPO/.lake" "$CLONE/.lake"; fi
cd "$CLONE"
export PATH="$HOME/.elan/bin:$PATH"
LOG="$WORK/build.log"
if ! lake build >"$LOG" 2>&1; then echo "GATE FAIL: build"; tail -30 "$LOG"; exit 1; fi
if grep -Eq "declaration uses .sorry.|sorryAx" "$LOG"; then echo "GATE FAIL: sorry"; exit 1; fi
# explicit denies (the census also catches these via axioms, but only for
# inventory names): native_decide, its synonyms `decide +native` and
# `(native := true)`, and the native-evaluation axioms used directly
if grep -rnE --include="*.lean" "native_decide|\+native|native[[:space:]]*:=|ofReduce(Bool|Nat)" LeanShieldedPool statements controls 2>/dev/null; then echo "GATE FAIL: native_decide"; exit 1; fi
# bare simp rots silently as Mathlib evolves; require simp only [...] in accepted files
if grep -rnE --include="*.lean" "(^|[^_[:alnum:]])simp($| [^o])" LeanShieldedPool statements 2>/dev/null | grep -v "simp only"; then echo "GATE FAIL: bare simp (use simp only [...])"; exit 1; fi
# every declared axiom must be listed in AXIOMS.md by its full name (grep belt; kernel census is the suspenders)
while read -r f line; do
  case "$f" in controls/*) echo "GATE FAIL: axiom declared in control $f"; exit 1;; esac
  axname=$(echo "$line" | sed -nE 's/^[0-9]+:[[:space:]]*((private|protected)[[:space:]]+)*axiom[[:space:]]+([^[:space:]:({]+).*/\3/p')
  [ -n "$axname" ] || { echo "GATE FAIL: axiom declaration in $f not parsed: $line"; exit 1; }
  awk -v a="$axname" '$1 == "-" && $2 == a { f = 1 } END { exit !f }' AXIOMS.md || { echo "GATE FAIL: axiom '$axname' in $f not listed in AXIOMS.md"; exit 1; }
done < <(grep -rnE "^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)*axiom([[:space:]]|$)" LeanShieldedPool statements controls 2>/dev/null | sed 's/:/ /')
python3 scripts/mk_check.py statements/INVENTORY.md > "$WORK/CheckInventory.lean"
if ! lake env lean "$WORK/CheckInventory.lean" > "$WORK/axioms.out" 2>&1; then
  echo "GATE FAIL: inventory did not elaborate"; cat "$WORK/axioms.out"; exit 1
fi
python3 scripts/check_axioms.py statements/INVENTORY.md "$WORK/axioms.out" || { echo "GATE FAIL: census"; exit 1; }
shopt -s nullglob
for f in controls/neg_*.lean; do
  wanted=$(sed -n 's/^-- EXPECT: //p' "$f" | head -1)
  if lake env lean "$f" > "$WORK/ctl.out" 2>&1; then
    echo "GATE FAIL: negative control built: $f"; exit 1
  fi
  if [ -n "$wanted" ] && ! grep -qF "$wanted" "$WORK/ctl.out"; then
    echo "GATE FAIL: $f failed for the wrong reason (wanted: $wanted)"; cat "$WORK/ctl.out"; exit 1
  fi
done
# positive and refutation controls must BUILD. A refutation control proves the
# explicit negation on its mutated model, so it cannot pass for the wrong
# reason the way an EXPECT marker can.
for f in controls/positive*.lean controls/refute_*.lean; do
  lake env lean "$f" > "$WORK/pos.out" 2>&1 || { echo "GATE FAIL: control did not build: $f"; cat "$WORK/pos.out"; exit 1; }
  if grep -Eq "declaration uses .sorry.|sorryAx" "$WORK/pos.out"; then echo "GATE FAIL: sorry in control: $f"; exit 1; fi
done
# frozen surface, last: pins and checker come from the checked-out HEAD (the
# trusted base), files from the gated tree, so a GATE_REF candidate cannot
# re-pin itself. This also freezes the statement bodies the census cannot see.
git -C "$REPO" show HEAD:statements/FROZEN.sha256 > "$WORK/FROZEN.sha256" 2>/dev/null &&
  git -C "$REPO" show HEAD:scripts/check_frozen.py > "$WORK/check_frozen.py" 2>/dev/null ||
  { echo "GATE FAIL: frozen (no pins at HEAD)"; exit 1; }
python3 "$WORK/check_frozen.py" "$WORK/FROZEN.sha256" . || { echo "GATE FAIL: frozen"; exit 1; }
echo "GATE PASS ($(git rev-parse --short HEAD))"
