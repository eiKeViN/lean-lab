#!/usr/bin/env bash
MEASUREMENT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PATH="$MEASUREMENT_ROOT/toolchain/lean-4.35.0-linux/bin:$PATH"
export XDG_CACHE_HOME="$MEASUREMENT_ROOT/.cache"
export LAKE_CACHE_DIR="$MEASUREMENT_ROOT/.cache/lake"
export MATHLIB_CACHE_DIR="$MEASUREMENT_ROOT/.cache/mathlib"
export LEAN_NUM_THREADS=2
