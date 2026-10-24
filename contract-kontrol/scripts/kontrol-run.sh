#!/usr/bin/env bash
# Run one command in the pinned Kontrol image (../check.sh calls it).
# Usage: scripts/kontrol-run.sh <log> <project-dir> <stock|patched> <command>
# One container at a time: waits while another Kontrol container runs and while the host has less
# than GATE_GIB (default 10) GiB available (free -g), then runs <command> in <project-dir> with a hard
# memory cap CAP (default 8g) and no swap, core dumps off, no network, the pinned solc as forge's
# compiler (FOUNDRY_SOLC), and, for "patched", kevm-patch/abi.md mounted read-only over the image's
# abi.md. Kills the container after TLIM seconds (default 7200). The log gets a RUN start line, the
# abi.md sha256 seen inside the container, the command output, COMMAND_EXIT, PEAK_BYTES (the container
# cgroup's memory.peak) and a RUN end line (wall seconds, command exit, peak, runner exit). The shell in
# the container exits with the command's status, so the runner exit equals the command exit unless the
# run was stopped (124: timeout, 137: kill, 125: docker could not run it). The runner exits with it.
# A runner that gives up at the gate writes "RUN gate: gave up" and no RUN start or end line.
# Env: IMAGE (default the pinned digest), SOLC (the checked solc 0.8.37 binary; required), ABI_PATH
# (the image's abi.md, which check.sh looks up; required), CAP,
# CPUSET (docker --cpuset-cpus, the CPUs the container sees; unset: all), TLIM, GATE_GIB, GATE_WAIT (seconds to wait for the gate before giving up, default 14400).
set -uo pipefail
LOG=$1; P=$2; ABI_MODE=$3; CMD=$4
PKG=$(cd "$(dirname "$0")/.." && pwd)
pin() { sed -n "s/^$1 \([^ ]*\).*$/\1/p" "$PKG/PINS.txt" | head -1; }
IMAGE=${IMAGE:-$(pin kontrol_image)@$(pin kontrol_image_digest)}
CAP=${CAP:-8g}; TLIM=${TLIM:-7200}; GATE_GIB=${GATE_GIB:-10}; GATE_WAIT=${GATE_WAIT:-14400}
: "${SOLC:?}"
ABI=${ABI_PATH:?set ABI_PATH (check.sh does): the path of abi.md in the image}
MOUNT_ABI=()
case "$ABI_MODE" in
  patched) MOUNT_ABI=(-v "$PKG/kevm-patch/abi.md:$ABI:ro") ;;
  stock) ;;
  *) echo "abi mode must be stock or patched"; exit 2 ;;
esac
waited=0
while :; do
  busy=$(docker ps --format '{{.Image}} {{.Names}}' | grep -ci kontrol)
  avail=$(free -g | awk '/^Mem/{print $7}')
  [ "$busy" -eq 0 ] && [ "$avail" -ge "$GATE_GIB" ] && break
  [ "$waited" -ge "$GATE_WAIT" ] && { echo "RUN gate: gave up after ${waited}s (kontrol containers $busy, available ${avail} GiB < ${GATE_GIB})" | tee -a "$LOG"; exit 4; }
  [ $((waited % 600)) -eq 0 ] && echo "gate: waiting (kontrol containers $busy, available ${avail} GiB, need ${GATE_GIB})"
  sleep 30; waited=$((waited + 30))
done
N="contract-kontrol-$$-$(date +%s)"
T0=$(date +%s)
echo "RUN start $(date -u +%FT%TZ) image $IMAGE cap $CAP abi $ABI_MODE available $(free -g | awk '/^Mem/{print $7}') GiB" >> "$LOG"
timeout --signal=TERM --kill-after=30 "$TLIM" docker run --rm --name "$N" --network none \
  --memory "$CAP" --memory-swap "$CAP" ${CPUSET:+--cpuset-cpus "$CPUSET"} --ulimit core=0 \
  -e KPROFILE_TELEMETRY_DISABLED=true -e FOUNDRY_OFFLINE=true -e FOUNDRY_SOLC=/opt/solc/solc \
  -v "$SOLC:/opt/solc/solc:ro" "${MOUNT_ABI[@]}" -v "$P:/w/proj" -w /w/proj "$IMAGE" \
  bash -c "ulimit -c 0; sha256sum $ABI; $CMD; rc=\$?; echo COMMAND_EXIT=\$rc; echo PEAK_BYTES=\$(cat /sys/fs/cgroup/memory.peak 2>/dev/null); exit \$rc" >> "$LOG" 2>&1
RC=$?
docker inspect "$N" >/dev/null 2>&1 && docker kill "$N" >/dev/null 2>&1
S=$(( $(date +%s) - T0 ))
CE=$(grep -o "COMMAND_EXIT=[0-9]*" "$LOG" | tail -1 | cut -d= -f2)
PK=$(grep -o "PEAK_BYTES=[0-9]*" "$LOG" | tail -1 | cut -d= -f2)
echo "RUN end wall ${S}s command_exit ${CE:-none} peak_bytes ${PK:-unknown} runner_rc $RC (124 = timeout, 137 = killed)" >> "$LOG"
echo "RUN end wall ${S}s command_exit ${CE:-none} peak_bytes ${PK:-unknown} runner_rc $RC"
exit $RC
