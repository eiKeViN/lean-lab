#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
source env.sh
mkdir -p downloads toolchain logs
archive=downloads/lean-4.35.0-linux.tar.zst
if [[ ! -f "$archive" ]]; then
  curl -fL --retry 2 https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst -o "$archive.part"
  mv "$archive.part" "$archive"
fi
echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  $archive" | sha256sum -c -
if [[ ! -x toolchain/lean-4.35.0-linux/bin/lean ]]; then
  tar --zstd -xf "$archive" -C toolchain
fi
lake env lean --version
lake exe cache get Mathlib.Probability.ProbabilityMassFunction.Constructions Mathlib.Probability.ProbabilityMassFunction.Integrals Mathlib.Probability.Independence.Basic Mathlib.Probability.Moments.Variance Mathlib.Analysis.Convex.Combination Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog Mathlib.Basic.NNReal.Basic Mathlib.Data.EReal.Basic Mathlib.Tactic.Finiteness Mathlib.Topology.UnitInterval Mathlib.Analysis.Convex.Basic
bash check.sh
