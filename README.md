# Lean lab

A workspace for isolated Lean formalization and proof-engineering experiments.
There is **no root Lean project or repository-wide toolchain**. Each active
project owns its Lean pin, Lake manifest, dependencies, and verification entrypoint.

## Projects

| Project | Scope and entrypoint | Pinned environment | Recorded status |
|---|---|---|---|
| [KL formalization](experiments/kl-for-mathlib/README.md) | KL/application proofs, reusable `ForMathlib` layer, module/API experiments; main import `OAI.KL` | Lean **4.34.1**, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` | [261/261 modules migrated and accepted](reports/module-completion.md); exact interface exceptions and historical evidence remain documented |
| [Quantum probability experiments](projects/quantum-experiments/README.md) | Finite-friendly APIs backed by mathlib bridges, actual Physlib channel specializations, finite-sum comparison; active Lake workspace `pmf-environment` | Lean **4.35.0**, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e` | [47 new declarations and 63 historical declarations checked](projects/quantum-experiments/pmf-environment/Frontend/README.md); [corrected costs and controlled timings](projects/quantum-experiments/pmf-environment/CostStudy20261102/README.md) |
| [Stabilizer API experiment](experiments/stabilizer-api/README.md) | Lean-QEC typed stabilizers, general coefficient maps, composable transport and source-isolated comparisons; `scripts/check.py` | Lean **4.30.0-rc2**, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, Lean-QEC `8d115519b471b71a21fbdddf5341d8203b841cc9` | [Recorded targeted verification](experiments/stabilizer-api/evidence/acceptance.json); compatibility and trust scope are grouped in the project guide |
| [Measurement API experiment](experiments/measurement-api/README.md) | Physlib POVM transport, coarsegraining, binary testing, PMF bridge and Kraus/statistics separation; `scripts/check.sh` | Lean **4.35.0**, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e` | [Actual compilation, public types and axiom checks](experiments/measurement-api/evidence/acceptance.json); full hypothesis-testing client before/after comparison |

Each project keeps its own environment. Status links describe recorded runs,
not fresh builds or independent whole-dependency kernel verification.

## Run the intended project

Use the project guides above for setup, verification commands, and prerequisites.
There is no repository-wide build command.

## Evidence and navigation

The [verification report index](reports/README.md) links current project evidence
and retained research history. Project guides own their detailed source,
compatibility, and reproduction notes.

Keep experiments isolated, preserve source and API evidence, and avoid routine
`lake update` or cache deletion. No Alioth code is hosted or migrated here.
