#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/pmf-environment"
source env.sh
python3 Frontend/verify.py
