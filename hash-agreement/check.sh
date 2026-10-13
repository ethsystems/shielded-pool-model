#!/usr/bin/env bash
# Replay check for hash-agreement (see README.md). Needs python3 (3.10 or later) and elan;
# lake picks the toolchain from lean-toolchain. The five modules build one at a time; set
# LEAN_NUM_THREADS to change the Lean thread count (default 2).
#   ./check.sh    rebuild from scratch and replay every theorem, control and test against expected.json
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
[ $# -eq 0 ] || { echo "usage: ./check.sh" >&2; exit 2; }
exec python3 scripts/replay.py check
