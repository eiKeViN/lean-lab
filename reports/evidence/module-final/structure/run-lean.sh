set -euo pipefail
source scripts/env.sh
cd experiments/kl-for-mathlib
# --input paths are explicit read-only identities for recorded_run.py.
if [[ ${2:-} == --types-out ]]; then export LEAN_TYPES_OUT="$3"; fi
exec lake env lean "$1"
