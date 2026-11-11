# Frozen HGP Lean environment

Host sources and binaries are shared across rooms. Each room sees:

| Room path | Host directory |
| --- | --- |
| `/opt/lean` | `runtime/lean-4.33.1-linux` |
| `/opt/qecert` | `qecert` including `.lake/packages` and build artifacts |
| `/work` | The individual participant's writable room |

The dependency mounts are read-only and the room denies network socket creation.
Copy `lean-project` into each participant room. Its Lake requirements and manifest
use local paths only, overriding every inherited Git dependency. Run the same
commands in every room:

```sh
cd lean-project
lake env lean HGPExperiment.lean
lake build HGPExperiment
```

The first command only elaborates the file; the second builds the participant's
local library. All shared dependencies must be prepared before making their
mounts read-only. Do not run `lake update` inside a participant room.

## Source pins

- Lean: `4.33.1`, official Linux release, commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- QECert: `c0ff74952c65b48e2ba5430fc4dfa4459d120440`.
- Mathlib: tag `v4.33.1`, commit
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- All additional dependency revisions: `qecert/lake-manifest.json`.

`prepare-dependencies.sh` verifies these source pins, resumes official binary
cache downloads, and builds only the HGP QEC dependency target. Set
`HGP_RUNTIME_ROOT` to the host directory containing `runtime` and `qecert` when
invoking it outside the workspace layout. The source checkouts and official Lean
binary installation must already exist; the script does not change source pins.

QEC's HGP import closure includes a bare `import Mathlib`, so the full Mathlib
binary cache is required. This is a cache download, not a whole-Mathlib source
build. The official cache CLI uses parallel curl; the preparation script wraps
curl to use serial transfers at eight starts per second because curl ignores
`--rate` in parallel mode. If the cache service returns 429, rerun later; existing
archives are retained and reused. No participant should perform cache downloads.

## Recreating source checkouts

Use official source URLs, the pinned QEC snapshot, and the dependency manifest:

```sh
mkdir -p runtime
curl -fL --retry 5 -o /tmp/lean-4.33.1-linux.tar.zst \
  https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst
tar --zstd -xf /tmp/lean-4.33.1-linux.tar.zst -C runtime
git clone https://github.com/QudeLeap/Lean-QECert.git qecert
git -C qecert checkout --detach c0ff74952c65b48e2ba5430fc4dfa4459d120440
export PATH="$PWD/runtime/lean-4.33.1-linux/bin:$PATH"
```

For each entry in `qecert/lake-manifest.json`, clone its `url` into
`qecert/.lake/packages/<name>` and check out its exact `rev` detached. Preserve
that manifest; do not resolve dependency branches with `lake update`. Then run
`supervision/prepare-dependencies.sh` from the experiment directory, or pass its
full path and set `HGP_RUNTIME_ROOT` explicitly.
