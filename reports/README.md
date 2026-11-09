# Verification records

Return to the [multi-project workspace index](../README.md).

## Current project entrypoints

- **KL / Lean 4.34.1:** [complete module migration acceptance](module-completion.md),
  [project guide](../experiments/kl-for-mathlib/README.md), and
  [module index](../experiments/kl-for-mathlib/MODULES.md). The latest recorded
  acceptance covers 261/261 modern modules, with its explicit interface exceptions.
  The later six-round API work culminates in [API saturation](api-saturation.md),
  with [API discovery](../experiments/kl-for-mathlib/API-GUIDE.md) in the project.
  Those reports retain their original branch-stage status and verification scope.
- **Quantum / Lean 4.35.0:** [experiment index](../projects/quantum-experiments/README.md),
  [PMF bridge verification](../projects/quantum-experiments/pmf-environment/Verified/VALIDATION.md),
  [finite-sum comparison](../projects/quantum-experiments/pmf-environment/Comparison/README.md),
  [corrected cost/timing study](../projects/quantum-experiments/pmf-environment/CostStudy20261102/README.md),
  [finite-friendly interfaces and clients](../projects/quantum-experiments/pmf-environment/Frontend/README.md), and
  [publication acceptance](../projects/quantum-experiments/pmf-environment/history/publication/README.md).
  These are separate projects and dependency pins; the quantum scripts do not check KL.
- **Stabilizer / Lean 4.30.0-rc2:** [project guide](../experiments/stabilizer-api/README.md),
  [review and compatibility scope](../experiments/stabilizer-api/REVIEW.md), and
  [targeted acceptance](../experiments/stabilizer-api/evidence/acceptance.json).
- **Measurement / Lean 4.35.0:** [project guide](../experiments/measurement-api/README.md),
  [compilation, public types and axiom evidence](../experiments/measurement-api/evidence/acceptance.json),
  and [independent exercises and same-task follow-up](../experiments/measurement-api/Usability/RESULTS.md).

## Earlier KL rounds and retained evidence

The [module-boundary archive](boundary-archive.md) preserves pinned diagnostic
reproducers and rejected AttachBottom trials, with their historical status.

The [three-file production integration](module-integration.md) connects the module
pilot to exact source transforms, split audits and real downstream validation.

The bounded [import/module pilot](module-import-pilot.md) records four-grid,
visibility compatibility, and incremental-build experiments on the pinned baseline.

The earlier library extraction round is in
[lemma-granularity-library.md](lemma-granularity-library.md), with a separate
[coverage register](lemma-granularity-library-coverage.md), following the
[comparison pilot](lemma-granularity-comparison.md), the
[expanded pilot](lemma-granularity-expansion.md) and [first pilot](lemma-granularity.md). The prior whole-library refinement is in
[whole-library-layout.md](whole-library-layout.md); the previous local refinement
is in [responsibility-boundaries.md](responsibility-boundaries.md). The preceding
consolidation results are in [project-consolidation.md](project-consolidation.md).

Earlier reports and evidence are retained as historical records. Their commands,
cache paths and experiment directories describe the commit where they ran; they
are not instructions to recreate parallel maintained projects. Source links and
line ranges can be resolved at these immutable commits:

- [7ddc53b](https://github.com/eiKeViN/lean-lab/tree/7ddc53ba8a09ed902fefff86e67a87217518c1d4): pristine, signed-rank and kernel-transport stages.
- [2b52879](https://github.com/eiKeViN/lean-lab/tree/2b5287954bd3c16015d9aab10dc3331d61065926): reviewed semantic architecture stage.
- [85b3d1a](https://github.com/eiKeViN/lean-lab/tree/85b3d1a4fa9c4f08beb718d8925d2d0ec9c50060): published ForMathlib/application classification and validated type export.

`provenance/baselines.json` and the checksum-bound reference export preserve the
source and comparison anchors used by today's checks. Historical records are
not relabelled as fresh builds or GitHub CI results.
