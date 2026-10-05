#!/usr/bin/env bash
# Replay check for circuits-acir (see README.md). Needs python3 (3.10 or later) and elan;
# lake picks the toolchain from lean-toolchain. Run builds one at a time; set
# LEAN_NUM_THREADS to change the Lean thread count (default 2).
#   ./check.sh              replay every theorem, control and census against expected.json
#   ./check.sh --self-test  check that each must-fail fixture fails for its intended reason
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
cd "$(dirname "$0")"
case "${1:-}" in
  "") exec python3 scripts/replay.py check ;;
  --self-test) exec python3 scripts/replay.py self-test ;;
  *) echo "usage: ./check.sh [--self-test]" >&2; exit 2 ;;
esac
