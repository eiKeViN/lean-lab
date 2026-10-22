# Verification records

The [three-file production integration](module-integration.md) connects the module
pilot to exact source transforms, split audits and real downstream validation.

The bounded [import/module pilot](module-import-pilot.md) records four-grid,
visibility compatibility, and incremental-build experiments on the pinned baseline.

Current entrypoints are in the root README and the maintained
`experiments/kl-for-mathlib/README.md`. The current library extraction round is in
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
