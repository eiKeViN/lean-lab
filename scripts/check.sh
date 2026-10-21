#!/usr/bin/env bash
# One maintained project; legacy build/audit mode names remain useful aliases.
set -euo pipefail
source "$(dirname "$0")/env.sh"
project="$LAB_ROOT/experiments/kl-for-mathlib"
mode="${1:-all}"
if [[ $# -gt 0 ]]; then shift; fi
case "$mode" in
  all|kl|build) exec bash "$project/check.sh" "$@" ;;
  warm|audit) exec bash "$project/check.sh" --checks-only "$@" ;;
  static|baseline) exec bash "$project/check.sh" --static "$@" ;;
  smoke)
    label="${1:-smoke}"
    if [[ $# -gt 1 || "$label" == */* || "$label" == .* ]]; then
      echo 'Usage: scripts/check.sh smoke [simple-result-label]' >&2; exit 2
    fi
    python3 "$LAB_ROOT/scripts/verify.py"
    cd "$project"
    exec python3 "$LAB_ROOT/scripts/measure.py" "$LAB_ROOT/results/$label.log" lake build Smoke
    ;;
  *) echo 'Usage: scripts/check.sh {all|warm|static|baseline|smoke|kl|build|audit} [validator options]' >&2; exit 2 ;;
esac
