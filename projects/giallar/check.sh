#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
source env.sh
export GIAL_CHECK_STARTED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
mkdir -p logs evidence
[[ $(lean --version) == *"version 4.35.0,"* ]]
[[ $(git -C .lake/packages/mathlib rev-parse HEAD) == 56a005855ea17e0b0958f73ec801ae140b0a1679 ]]
[[ $(git -C .lake/packages/Physlib rev-parse HEAD) == c5a908ba7a1ee474063626bdf0470af006f9812e ]]
lake build Giallar 2>&1 | tee logs/build.log
for source in tests/*.lean; do
  lake env lean -DwarningAsError=true "$source"
done 2>&1 | tee logs/tests.log
lake exe lint-style Giallar 2>&1 | tee logs/style.log
for source in Giallar.lean Giallar/*.lean; do
  lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true \
    -DwarningAsError=true "$source"
done 2>&1 | tee logs/elaboration-style.log
python3 scripts/audit.py 2>&1 | tee logs/axioms.log
python3 scripts/source_check.py
python3 scripts/record_acceptance.py
