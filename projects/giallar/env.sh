#!/usr/bin/env bash
GIAL_PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PATH="$GIAL_PROJECT_DIR/../../.cache/toolchains/lean-4.35.0-linux/bin:$PATH"
