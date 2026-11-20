#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
source env.sh
mkdir -p ../../.cache/toolchains downloads
archive=downloads/lean-4.35.0-linux.tar.zst
if ! command -v lean >/dev/null || [[ $(lean --version) != *"version 4.35.0,"* ]]; then
  if [[ ! -f "$archive" ]]; then
    curl -fL --retry 2 https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst -o "$archive.part"
    mv "$archive.part" "$archive"
  fi
  echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  $archive" | sha256sum -c -
  tar --zstd -xf "$archive" -C ../../.cache/toolchains
fi
lake env lean --version
python3 scripts/cache_inputs.py > .cache-inputs
xargs lake exe cache get < .cache-inputs
bash check.sh
