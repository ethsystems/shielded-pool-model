#!/usr/bin/env bash
# Fail-closed tests: each fixture must make the gate FAIL with the right marker.
set -uo pipefail
REPO="$(cd "$(dirname "$0")/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
FAILS=0
# Same filesystem as the repo, so copy_lake is a clone or reflink (see gate.sh)
GTEST_WORK="${GATE_WORK:-$REPO/.gate-work}"
mkdir -p "$GTEST_WORK"
copy_lake() {
  cp -Rc "$1" "$2" 2>/dev/null && return
  rm -rf "$2"; cp -R --reflink=auto "$1" "$2" 2>/dev/null && return
  rm -rf "$2"; cp -R "$1" "$2"
}
fixture() {
  local name="$1" marker="$2" script="$3"
  local W; W=$(mktemp -d "$GTEST_WORK/gtest.XXXXXX")
  git clone --quiet "$REPO" "$W/r"
  copy_lake "$REPO/.lake" "$W/r/.lake"
  ( cd "$W/r" && eval "$script" && git add -A && git commit -qm "fixture $name" )
  local out
  out=$("$W/r/scripts/gate.sh" 2>&1); local rc=$?
  if [ $rc -eq 0 ]; then echo "TEST FAIL [$name]: gate passed, should fail"; FAILS=$((FAILS+1))
  elif ! echo "$out" | grep -qF "$marker"; then echo "TEST FAIL [$name]: wrong marker (wanted '$marker'); got: $(echo "$out" | tail -2)"; FAILS=$((FAILS+1))
  else echo "test OK [$name]"; fi
  rm -rf "$W"
}
fixture sorry "GATE FAIL: sorry" \
  'printf "\ntheorem fx_sorry : 2 = 2 := by sorry\n" >> LeanShieldedPool/Proofs/TierA.lean'
fixture rogue-axiom "GATE FAIL: axiom" \
  'printf "\naxiom fx_cheat : False\n" >> LeanShieldedPool/Proofs/TierA.lean'
fixture axiom-name-prefix "GATE FAIL: axiom 'prope'" \
  'printf "\naxiom prope : False\n" >> LeanShieldedPool/Proofs/TierA.lean'
fixture axiom-two-spaces "GATE FAIL: axiom 'fx_spaced'" \
  'printf "\naxiom  fx_spaced : False\n" >> LeanShieldedPool/Proofs/TierA.lean'
fixture axiom-trailing-name "GATE FAIL: axiom 'fx_trailing'" \
  'printf "\naxiom fx_trailing : False -- axiom propext\n" >> LeanShieldedPool/Proofs/TierA.lean'
fixture statement-edit "GATE FAIL: census" \
  'python3 -c "
p=open(\"statements/INVENTORY.md\").read()
open(\"statements/INVENTORY.md\",\"w\").write(p.replace(\"LeanShieldedPool.noDoubleSpend ::\",\"LeanShieldedPool.noDoubleSpend :: TAMPERED\",1))"'
fixture missing-theorem "GATE FAIL: inventory did not elaborate" \
  'printf "ghost_thm :: Nat\n" >> statements/INVENTORY.md'
fixture native-decide "GATE FAIL: native_decide" \
  'printf "\ntheorem fx_nd : (2:Nat) + 2 = 4 := by native_decide\n" >> LeanShieldedPool/Proofs/TierA.lean'
# `decide +native` is a synonym of native_decide; in a control no census sees its axiom
fixture control-decide-native "GATE FAIL: native_decide" \
  'printf -- "theorem fx_dn : (2:Nat) + 2 = 4 := by decide +native\n" > controls/refute_fixture.lean'
fixture bare-simp "GATE FAIL: bare simp" \
  'printf "\ntheorem fx_s : (3:Nat) = 3 := by simp\n" >> LeanShieldedPool/Proofs/TierA.lean'
fixture broken-neg-control "GATE FAIL: negative control built" \
  'printf -- "-- EXPECT: nothing\ntheorem fx_neg : (1:Nat) = 1 := rfl\n" > controls/neg_fixture.lean'
fixture broken-refute-control "GATE FAIL: control did not build" \
  'printf -- "theorem fx_refute : (1:Nat) = 2 := rfl\n" > controls/refute_fixture.lean'
fixture refute-control-sorry "GATE FAIL: sorry in control" \
  'printf -- "theorem fx_refute : (1:Nat) = 2 := by sorry\n" > controls/refute_fixture.lean'
fixture control-axiom "GATE FAIL: axiom declared in control" \
  'printf -- "private axiom\tprope : (1:Nat) = 2\ntheorem fx_pos : (1:Nat) = 2 := prope\n" > controls/positive_fixture.lean'
fixture frozen-comment-edit "GATE FAIL: frozen" \
  'printf "\n-- tampered after pinning\n" >> LeanShieldedPool/Statements/L3.lean'
fixture frozen-new-file "GATE FAIL: frozen" \
  'printf "def fxExtra : Nat := 1\n" > LeanShieldedPool/Statements/Extra.lean'
# The k-anonymity extension is part of the build, census and frozen surface.
fixture k-anonymity-sorry "GATE FAIL: sorry" \
  'printf "\ntheorem fx_ka_sorry : 2 = 2 := by sorry\n" >> LeanShieldedPool/Extensions/KAnonymity.lean'
fixture k-anonymity-frozen-edit "GATE FAIL: frozen" \
  'printf "\n-- tampered after pinning\n" >> LeanShieldedPool/Extensions/KAnonymity.lean'
fixture k-anonymity-census-tamper "GATE FAIL: census" \
  'python3 -c "
p=open(\"statements/INVENTORY.md\").read()
open(\"statements/INVENTORY.md\",\"w\").write(p.replace(\"LeanShieldedPool.KAnonymity.hasAnonymitySet ::\",\"LeanShieldedPool.KAnonymity.hasAnonymitySet :: TAMPERED\",1))"'
fixture extensions-new-file "GATE FAIL: frozen" \
  'printf "def fxExtensionExtra : Nat := 1\n" > LeanShieldedPool/Extensions/Extra.lean'
# re-pinning does not launder a tampered statement: the census still bites
fixture repinned-census-tamper "GATE FAIL: census" \
  'python3 -c "
p=open(\"statements/INVENTORY.md\").read()
open(\"statements/INVENTORY.md\",\"w\").write(p.replace(\"LeanShieldedPool.noDoubleSpend ::\",\"LeanShieldedPool.noDoubleSpend :: TAMPERED\",1))" && python3 scripts/check_frozen.py --write statements/FROZEN.sha256 .'
# The L5 epoch files are part of the build, census, controls and frozen surface.
fixture l5-sorry "GATE FAIL: sorry" \
  'printf "\ntheorem fx_l5_sorry : 2 = 2 := by sorry\n" >> LeanShieldedPool/Proofs/Epoch.lean'
fixture l5-rogue-axiom "GATE FAIL: axiom" \
  'printf "\naxiom fx_l5_cheat : False\n" >> LeanShieldedPool/Proofs/EpochBase.lean'
fixture l5-inventory-edit "GATE FAIL: census" \
  'python3 -c "
p=open(\"statements/INVENTORY.md\").read()
k=\"LeanShieldedPool.Epoch.crossEpochNoDoubleSpend_proof ::\"
assert p.count(k)==1
open(\"statements/INVENTORY.md\",\"w\").write(p.replace(k,k+\" TAMPERED\",1))"'
fixture l5-statement-comment "GATE FAIL: frozen" \
  'printf "\n-- tampered after pinning\n" >> LeanShieldedPool/Statements/L5.lean'
# GATE_REF: a bad candidate commit must fail even when the checked-out HEAD is clean
W=$(mktemp -d "$GTEST_WORK/gtest.XXXXXX"); git clone --quiet "$REPO" "$W/r"
copy_lake "$REPO/.lake" "$W/r/.lake"
( cd "$W/r" && git checkout -qb cand && printf "\ntheorem fx_ref : 2 = 2 := by sorry\n" >> LeanShieldedPool/Proofs/TierA.lean && git commit -qam cand && git checkout -q - )
cand=$(git -C "$W/r" rev-parse cand)
out=$(GATE_REF="$cand" "$W/r/scripts/gate.sh" 2>&1); rc=$?
if [ $rc -ne 0 ] && echo "$out" | grep -qF "GATE FAIL: sorry"; then echo "test OK [gate-ref-candidate]"; else echo "TEST FAIL [gate-ref-candidate]: rc=$rc $(echo "$out" | tail -2)"; FAILS=$((FAILS+1)); fi
rm -rf "$W"
if [ $FAILS -eq 0 ]; then echo "GATE_TEST PASS"; else echo "GATE_TEST FAIL ($FAILS)"; exit 1; fi
