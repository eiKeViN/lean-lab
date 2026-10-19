#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$LAB_ROOT/experiments/kl"
python3 "$LAB_ROOT/scripts/verify.py"
mode="${1:-smoke}"
label="${2:-$mode}"
case "$mode" in
  smoke) args=(lake build Smoke) ;;
  kl)
    # A full Mathlib import is in the preserved sources. Require cache readiness;
    # do not accidentally compile all of Mathlib on a small cloud worker.
    lake --no-build build Mathlib
    args=(lake build OAI) ;;
  audit) args=(lake env lean Audit.lean) ;;
  *) echo 'Usage: scripts/check.sh {smoke|kl|audit} [result-label]' >&2; exit 2 ;;
esac
python3 "$LAB_ROOT/scripts/measure.py" "$LAB_ROOT/results/$label.log" "${args[@]}"
if [[ "$mode" == audit ]]; then
  python3 - "$LAB_ROOT/results/$label.log" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
m=re.search(r"depends on axioms:\s*\[([^]]*)\]", text)
assert m, 'No axiom output found'
actual={a.strip() for a in m[1].split(',') if a.strip()}
assert actual <= {'propext', 'Quot.sound', 'Classical.choice'}, actual
print('Axiom allowlist passed:', sorted(actual))
PY
fi
