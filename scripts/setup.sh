#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
project="${1:-experiments/kl}"
cd "$LAB_ROOT/$project"
[[ $(uname -sm) == 'Linux x86_64' ]] || { echo 'Bootstrap supports Linux x86_64; install elan manually on other platforms.' >&2; exit 1; }
mkdir -p "$LAB_ROOT/.cache"
fetch() {
  local url="$1" dest="$2" hash="$3"
  if [[ ! -f "$dest" ]]; then
    curl --fail --location --silent --show-error --retry 2 "$url" -o "$dest.part"
    mv "$dest.part" "$dest"
  fi
  echo "$hash  $dest" | sha256sum --check --status
}
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  fetch https://github.com/leanprover/elan/releases/download/v4.2.0/elan-x86_64-unknown-linux-gnu.tar.gz "$LAB_ROOT/.cache/elan.tar.gz" 620db834935d0da55ac9cda207b2e370e8034061cbb0228af5eb6c14b02f0c0c
  tar -xzf "$LAB_ROOT/.cache/elan.tar.gz" -C "$LAB_ROOT/.cache" elan-init
  "$LAB_ROOT/.cache/elan-init" -y --no-modify-path --default-toolchain none
fi
pin=$(tr -d '\r\n' < lean-toolchain)
if ! elan run "$pin" lean --version >/dev/null 2>&1; then
  if [[ "$pin" == leanprover/lean4:v4.34.1 ]]; then
    # Official release asset: avoids the releases.lean-lang.org redirect blocked here.
    fetch https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst "$LAB_ROOT/.cache/lean.tar.zst" 47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4
    if [[ ! -x "$LAB_ROOT/.cache/lean-4.34.1-linux/bin/lean" ]]; then
      tar --zstd -xf "$LAB_ROOT/.cache/lean.tar.zst" -C "$LAB_ROOT/.cache"
    fi
    elan toolchain link "$pin" "$LAB_ROOT/.cache/lean-4.34.1-linux"
  else
    elan toolchain install "$pin"
  fi
fi
lean --version
lake --version
# Resolves missing checkouts from the committed manifest; never runs `lake update`.
lake env lean --version
if [[ "$project" == experiments/kl ]]; then python3 "$LAB_ROOT/scripts/verify.py"; fi
if [[ "${SKIP_CACHE:-0}" != 1 ]]; then
  bash "$LAB_ROOT/scripts/cache.sh"
fi
