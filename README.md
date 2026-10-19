# Lean lab

Small, pinned Lean experiments with repository-owned setup and checks. The first
experiment is an unchanged 34-module Kazhdan–Lusztig (KL) source baseline.

**Current status:** all 34 unchanged KL modules compile, and the main theorem's
axiom audit passes with exactly `propext`, `Quot.sound`, and `Classical.choice`.
Warm KL build: 3.40 s. Warm setup: 4.40 s, skipping network cache access.
See [measured results](reports/fresh-task.md).

## Run in a fresh task

From `/workspace/lean-lab` (or the root of your clone):

```bash
bash scripts/setup.sh
bash scripts/check.sh smoke
bash scripts/check.sh kl
bash scripts/check.sh audit
```

Setup requires bash, git, curl, Python 3, tar, zstd, and Linux x86_64. It installs
pinned official release binaries only when absent, restores dependencies from the
committed manifest, then downloads mathlib's matching binary cache. No global
Lean default or shell profile is changed. Run `source scripts/env.sh` before
interactive `cd experiments/kl; lake ...` commands. There is intentionally no
root `lean-toolchain`: each experiment owns its own version and manifest.

Warm setup checks whether the full Mathlib artifacts are already usable and skips
network cache access when they are. `SKIP_CACHE=1` retains the small smoke-only
setup path for restricted workers. For a diagnostic preflight on missing caches,
set `CACHE_PROBE_URL` to an explicitly chosen artifact URL; see the measured GET
in [the report](reports/baseline.md). Setup otherwise lets the official cache tool
honor its endpoint configuration, then checks readiness without source builds.
The KL check refuses to compile all of mathlib automatically if its cache is
missing. The audit prints the exact theorem type and its recursive kernel axiom
closure and fails if anything outside `propext`, `Quot.sound`, `Classical.choice`
occurs. It is meaningful only after a successful KL build.

## Saved cloud environment

No saved environment setting was changed by this task. Suggested settings:

| Setting | Value / meaning |
| --- | --- |
| Repository | `eiKeViN/lean-lab`; other mounts are read-only references for this task |
| Setup command | `cd /workspace/lean-lab && bash scripts/setup.sh && bash scripts/check.sh smoke` |
| Maintenance command | Same as setup; reuses installed tools and ready Mathlib artifacts |
| Networking | Setup needs GitHub source/releases, redirected release assets, and `cache.mathlib.org`; documented cache fallback is `lakecache.blob.core.windows.net` |
| Secrets | None needed for public dependency downloads; use the platform Git credential for repository publication |
| Parallelism | `LEAN_NUM_THREADS=4` by default; override for a differently sized worker |

Eight repository directories were mounted at startup. Associating only this lab
could reduce checkout work and clutter; that potential saving was not measured
and the association setting was not changed. The runtime was Debian 13, with a
4-CPU cgroup quota, 16 GiB RAM limit and approximately 30 GiB initially free disk.
Saved setup UI values, startup scripts, and persistence across future workers
cannot be inspected through the available shell; the commands above are the
reproducibility contract, not a claim that platform settings were saved.

## Cache and maintenance costs

- `.cache/elan` shares per-version Lean installations across experiments.
  The verified 4.34.1 release fallback is linked to `.cache/lean-4.34.1-linux`.
- `.cache/mathlib` holds content-addressed mathlib downloads across experiments.
- Each experiment's `.lake` holds its exact dependency checkout and compiled
  artifacts. Repeated checks reuse these; do not run `lake clean` routinely.
- All generated caches and `results/` logs are ignored by Git. Selected baseline
  evidence is committed under `reports/`. Current local footprint is about
  4.0 GiB for `.cache` and 8.0 GiB for the KL `.lake`, including full mathlib
  and KL artifacts.
- This fresh task had no retained caches from the previous worker. Setup is
  idempotent when files persist and downloads again if the platform discards them.
- Do not run `lake update` during normal setup. To intentionally upgrade, create
  a separate experiment or review both `lean-toolchain` and `lake-manifest.json`
  changes together. Reuse a compatible installed toolchain; never substitute a
  different version merely because it is already installed.

Cheap script regressions: `python3 scripts/test_checks.py` (no Lean build or network).

No CI, containers, background services or speculative refactoring were added.
Source provenance and licenses are in [provenance/README.md](provenance/README.md).
