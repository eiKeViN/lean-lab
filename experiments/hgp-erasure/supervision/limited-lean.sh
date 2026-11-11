#!/bin/bash
# One top-level Lean or Lake process per assigned lane. Its own children
# inherit the lock and can invoke the actual toolchain directly.
set -eu
if [[ -z "${HGP_COMPILE_LANE_HELD:-}" ]]; then
    exec 9</tools/compile.lock
    flock -x 9
    export HGP_COMPILE_LANE_HELD=1
fi
exec "/opt/lean/bin/${0##*/}" "$@"
