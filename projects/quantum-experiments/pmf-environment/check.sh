#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
source env.sh
mkdir -p logs
run() {
  local name="$1"; shift
  local rc=0
  "$@" > "logs/$name.log" 2>&1 || rc=$?
  printf '%s\n' "$rc" > "logs/$name.exit"
  cat "logs/$name.log"
  return "$rc"
}
[[ $(git -C .lake/packages/Physlib rev-parse HEAD) == c5a908ba7a1ee474063626bdf0470af006f9812e ]]
[[ $(git -C .lake/packages/mathlib rev-parse HEAD) == 56a005855ea17e0b0958f73ec801ae140b0a1679 ]]
run lean-version lean --version
run module-build lake build QuantumInfo.ClassicalInfo.Channel Mathlib.Probability.Independence.Basic Mathlib.Probability.Moments.Variance
run smoke lake env lean Smoke.lean
