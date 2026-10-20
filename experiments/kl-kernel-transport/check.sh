#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../scripts/env.sh"
python3 "$LAB_ROOT/experiments/kl-kernel-transport/validate.py" "$@"
