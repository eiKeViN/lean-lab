#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -n "${FQC_TOOLCHAIN_DIR:-}" ]]; then
  export PATH="$FQC_TOOLCHAIN_DIR/bin:$PATH"
fi
if [[ $# -eq 0 ]]; then set -- check; fi
if [[ "$1" == full ]]; then
  shift
  if [[ $# -eq 0 ]]; then set -- all; fi
  python3 scripts/full.py "$@"
else
  python3 scripts/run.py "$@"
fi
