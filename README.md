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
  evidence is committed under `reports/`. The baseline measurement recorded about
  4.0 GiB for `.cache` and 8.0 GiB for the KL `.lake`, including full mathlib
  and KL artifacts.
- The original baseline measurement used a fresh worker without retained caches.
  Later experiments reuse the validated toolchain and dependency artifacts. Setup
  is idempotent when files persist and downloads again if they are discarded.
- Do not run `lake update` during normal setup. To intentionally upgrade, create
  a separate experiment or review both `lean-toolchain` and `lake-manifest.json`
  changes together. Reuse a compatible installed toolchain; never substitute a
  different version merely because it is already installed.

Cheap script regressions: `python3 scripts/test_checks.py` (no Lean build or network).

The baseline setup adds no CI, containers or background services.
Source provenance and licenses are in [provenance/README.md](provenance/README.md).

## Lean experiments and library layout

Each experiment is a separate Lake project with its own pinned toolchain and
manifest. Source is under its `OAI/` tree; the current staging experiment also
has `ForMathlib/`. Run commands from the lab root after `scripts/setup.sh`.

| Experiment | Purpose |
| --- | --- |
| `experiments/kl` | Pristine 34-module upstream baseline |
| `experiments/kl-signed-ranks` | Paired signed-rank API experiment |
| `experiments/kl-kernel-transport` | General kernel transport and compatibility |
| `experiments/kl-architecture` | Frozen, reviewed semantic file migration |
| [`experiments/kl-for-mathlib`](experiments/kl-for-mathlib/README.md) | Current candidate/application layout, preserving all earlier experiments |

The current candidate layer includes specialized Coxeter, Hecke, KL polynomial
and Tits word mathematics as well as general algebra. `OAI/KL` retains the
present application/model interfaces; future interface extraction is separate.
ForMathlib has no project-layer imports. Candidate status is distinct from
Mathlib PR readiness. See [the assessment](reports/for-mathlib-layout.md) for
current evidence, limitations and the complete per-module inventory.

```bash
bash experiments/kl-for-mathlib/check.sh
```
