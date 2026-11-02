#!/usr/bin/env bash
PMF_ENV_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PATH="$PMF_ENV_ROOT/toolchain/lean-4.35.0-linux/bin:$PATH"
export XDG_CACHE_HOME="$PMF_ENV_ROOT/.cache"
export LAKE_CACHE_DIR="$PMF_ENV_ROOT/.cache/lake"
