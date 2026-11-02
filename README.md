# Lean lab

A workspace for isolated Lean formalization and proof-engineering experiments.
There is **no root Lean project or repository-wide toolchain**. Each active
project owns its Lean pin, Lake manifest, dependencies, and verification entrypoint.

## Projects

| Project | Scope and entrypoint | Pinned environment | Recorded status |
|---|---|---|---|
| [KL formalization](experiments/kl-for-mathlib/README.md) | KL/application proofs, reusable `ForMathlib` layer, module/API experiments; main import `OAI.KL` | Lean **4.34.1**, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` | [261/261 modules migrated and accepted](reports/module-completion.md); exact interface exceptions and historical evidence remain documented |
| [Quantum probability experiments](projects/quantum-experiments/README.md) | Finite-friendly APIs backed by mathlib bridges, actual Physlib channel specializations, finite-sum comparison; active Lake workspace `pmf-environment` | Lean **4.35.0**, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e` | [47 new declarations and 63 historical declarations checked](projects/quantum-experiments/pmf-environment/Frontend/README.md); [corrected costs and controlled timings](projects/quantum-experiments/pmf-environment/CostStudy20261102/README.md) |

The new quantum environment does not upgrade or replace the KL environment.
The status links describe the actual recorded runs; navigation updates do not
constitute new KL builds or independent whole-dependency kernel verification.

## Run the intended project

For KL, from the repository root:

```bash
bash scripts/setup.sh
bash scripts/check.sh          # KL source, build, import, type and axiom checks
```

Shorter KL checks remain `warm`, `static`, and `smoke`; see the
[KL project guide](experiments/kl-for-mathlib/README.md) and
[module index](experiments/kl-for-mathlib/MODULES.md).
The root `scripts/` commands target KL only.

For quantum probability, first prepare its separate environment:

```bash
cd projects/quantum-experiments/pmf-environment
bash setup.sh
source env.sh
python3 Frontend/verify.py
```

With that environment already prepared, `bash projects/quantum-experiments/check.sh`
from the repository root repeats the combined quantum validation.
[Reproduction details](projects/quantum-experiments/pmf-environment/README.md)
cover official cache requirements and public source-identity checks.

## Evidence and navigation

- [Verification report index](reports/README.md): latest KL acceptance and prior research rounds, plus the quantum report entrypoints.
- [KL provenance](provenance/README.md): exact upstream snapshots, licenses and frozen type/source baselines; this folder's 4.34.1 pin is KL-specific.
- [Quantum source layout](projects/quantum-experiments/README.md): active `Verified`, `Comparison` and `Frontend` libraries versus frozen `UNVERIFIED_DRAFT` history.
- [Quantum publication evidence](projects/quantum-experiments/pmf-environment/history/README.md): source hashes, repair diff, necessary failure records and final accepted logs.

Historical `NOT_RUN`, incomplete-draft and proxy-blocked records describe the
older attempts in which they were written. They remain preserved and do not
supersede the later quantum acceptance. Conversely, compilation of the concrete
fixed-input theorems does not establish random-input independence or general
proof/maintenance savings. The comparison is a bounded consumer-extension test,
not a long-term maintenance or cross-version benchmark.

Keep experiments isolated, preserve source and API evidence, and avoid routine
`lake update` or cache deletion. `ForMathlib` staging in the KL project denotes
candidates, not upstream acceptance. No Alioth code is hosted or migrated here.
