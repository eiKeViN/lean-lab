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
matches=re.findall(r"'OAI\.KLInvariance\.combinatorial_invariance' depends on axioms:\s*\[([^]]*)\]", text)
if len(matches) != 1:
    sys.exit('Expected exactly one axiom closure for the main theorem')
actual={a.strip() for a in matches[0].split(',') if a.strip()}
unexpected=actual - {'propext', 'Quot.sound', 'Classical.choice'}
if unexpected:
    sys.exit('Disallowed axioms: '+', '.join(sorted(unexpected)))
print('Axiom allowlist passed:', sorted(actual))
PY
fi
