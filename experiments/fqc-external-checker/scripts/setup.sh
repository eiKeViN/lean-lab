#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -n "${FQC_TOOLCHAIN_DIR:-}" ]]; then
  export PATH="$FQC_TOOLCHAIN_DIR/bin:$PATH"
fi
python3 scripts/run.py setup
