#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
source env.sh
export PMF_RESTORED_ROOT="$PMF_ENV_ROOT/../physlib-pmf-bridge"
# Enter the pinned Lake environment, then run from the byte-preserved experiment.
# Draft imports need separately compiled oleans; this runner does not accept proofs.
exec lake env bash -c 'cd "$PMF_RESTORED_ROOT"; export LEAN_PATH="$PWD/UNVERIFIED_DRAFT:${LEAN_PATH:-}"; exec "$@"' pmf-restored "$@"
