#!/usr/bin/env bash
# Called by setup.sh from the locked experiment, with env.sh already loaded.
set -euo pipefail
if lake --no-build build Mathlib > /dev/null 2>&1; then
  echo 'Mathlib artifacts ready; skipping network cache access.'
  exit 0
fi
echo 'Mathlib artifacts missing; restoring the official binary cache.'
# Optional diagnostic GET to an explicitly chosen artifact, respecting the user's
# endpoint choice. Never substitute an alternate route after a policy denial.
if [[ -n "${CACHE_PROBE_URL:-}" ]]; then
  curl --fail --silent --show-error --location --max-time 20 "$CACHE_PROBE_URL" -o /dev/null
fi
if lake exe cache get Mathlib; then
  :
else
  status=$?
  echo 'Mathlib cache download failed; refusing a full source build.' >&2
  exit "$status"
fi
if ! lake --no-build build Mathlib; then
  echo 'Mathlib cache is incomplete; refusing a full source build.' >&2
  exit 1
fi
