# File responsibility refinement — 2026-10-21

Base: merged `main` at `c2a9bd42fe4ce719af0dc1c1fd020fcb80ae2e04`.
Work branch: `codex/kl-responsibility-boundaries`. The one maintained project stays
at `experiments/kl-for-mathlib`; no experiment copy or mathematical API is added.

## Mathematical placement

Paths below are relative to the maintained project. Declaration namespaces,
statements and proof bodies are preserved, including existing character/matrix
names. Compatibility imports keep the three published paths usable.

| Previous implementation | Current implementation and reason | Preserved compatibility |
| --- | --- | --- |
| `ForMathlib/Algebra/BigOperators/FiniteCharacterCancellation.lean`, plus the two weighted-difference lemmas in polynomial `ScaledReciprocity.lean` | `ForMathlib/Algebra/BigOperators/SingleCoordinate.lean`: `OAI.KLInvariance.finite_character_cancellation` and `OAI.KLInvariance.Comparison.matrix_difference_single` / `matrix_difference_le` all eliminate the other coordinates of a finite weighted sum. Their statements do not require characters, matrices, or polynomials. The first theorem uses an arbitrary commutative ring; the two inequalities/differences retain their real-valued interfaces. | Old cancellation entry forwards to this implementation; old polynomial entry forwards to both precise implementations. |
| Polynomial `ScaledReciprocity.lean` | `ForMathlib/Algebra/Polynomial/ScaledEvaluation.lean`: `OAI.KLInvariance.Comparison.scaledPolynomial` and `eq_of_scaled_difference_reciprocal` concern scaled integer-polynomial evaluation over the reals and reciprocal-difference rigidity. The only owned dependency is `Polynomial.Reciprocal`. | `ForMathlib.Algebra.Polynomial.ScaledReciprocity` remains an import-only umbrella. |
| `ForMathlib/Algebra/Module/Localization/Products.lean` | `ForMathlib/Algebra/Module/Submodule/ProductScaling.lean`: principal scalar-image submodules and finite associated products under an arbitrary algebra extension; there is no `IsLocalization` assumption. The associated-product lemmas support `product_image_scale`, so the cohesive original unit stays together. | `ForMathlib.Algebra.Module.Localization.Products` forwards to the new implementation. |

Actual consumers now import the needed implementation directly:

- `OAI/KL/Sheaves/StalkReciprocity.lean`: single-coordinate cancellation.
- `OAI/KL/Comparison/SuffixFreeness.lean`: weighted-difference inequalities;
  it no longer imports owned polynomial support for these lemmas.
- `OAI/KL/Invariance/Finite.lean`: explicitly imports both scaled evaluation and
  single-coordinate weighted sums, because it uses both responsibilities.
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/IntervalTransport.lean`:
  scaled polynomial evaluation, without the weighted-sum file.
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/ScaledImages.lean`:
  product scaling of scalar-image submodules.

The three implementation families are potential supplements to existing Mathlib
objects. This is a mathematical/dependency classification, not evidence of
novelty or submission readiness. Existing namespaces, broad `import Mathlib`,
assumption/naming review, duplicate searches and maintainer acceptance remain
future preparation. No Mathlib submission is made. The official
[scope](https://leanprover-community.github.io/contribute/index.html),
[review criteria](https://leanprover-community.github.io/contribute/pr-review.html)
and [naming guide](https://leanprover-community.github.io/contribute/naming.html)
remain the classification references; ForMathlib's one-way dependency rule is
our project rule, not an official mandated directory layout.

The three application consumers above stay application-side: suffix freeness
uses the current boundary sheaves, finite invariance assembles the comparison
pipeline, and stalk reciprocity connects the present boundary/Bott character
models. Separating scalar support does not extract a general sheaf/model API.
Their mathematical subject is not a reason to exclude possible future upstream
work. `responsibility-review.json` records these reasons and deferred cases.

`LinearAlgebra.Dual.BalancedCut` remains together because its statements concern
the same cut-balancing object; `Module.Projective.Transport` remains together
because its responsibility is projectivity under equivalences. No split or merge
is justified by line count. A possible future submodule-oriented name for
`Module.Cover.Product` is deferred rather than migrating an additional broad
foundational dependency chain in this bounded round.

## Source preservation and compatibility

All 525 original source-unit records, fixed sources, original blob hashes and
76 inherited instance-name annotations still equal the immutable architecture
policy. The historical source is read from pinned Git objects, not a retired
checkout. The reference export and its checksums are unchanged.

One mixed parent, `SimultaneousInvariance:5`, is now allocated as two pieces.
In pinned transport source
`OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean`, original
lines 321–349 contain the polynomial declarations and lines 350–375 contain the
weighted-difference declarations. The original parent hash remains
`8739585162c079084774bfda6575826afd4db0ab256bca6cd3c645d66e2f6ece`.
The split is at the complete `matrix_difference_single` declaration boundary;
no declaration or proof is split or rewritten.

`source_partitions.py` checks the parent and each raw-piece hash, exact adjacent
coverage of the parent, unique parent-qualified IDs and a declaration-start cut.
Extra metadata cannot override a piece's source/context. Only the parent's
existing opening/end scope frames may be copied; declaration-bearing or other
unsupported frames fail closed. The original lexical full-source coverage
algorithm is unchanged. `migrate.py --check` verifies every generated product,
and allocation must use all expanded pieces exactly once. Partitioning an
instance-annotated unit is rejected without an explicit future design review.
The scope guard is a small lexical whitelist, not a general Lean parser; the
actual boundary is also visible in the pinned source, and Lean/type checks
independently validate the rendered modules.

There remain 192 implementation modules: 168 ForMathlib candidates and 24 project
modules including the kernel compatibility implementation. Compatibility imports
increase from 36 to 39, so generated Lean products increase from 230 to 233.
Original source units remain 525; allocated pieces are 526. Core direct imports
increase from 326 to 327 because the finite-invariance consumer now names both
responsibilities explicitly. Fewer edges or files is not the success criterion:
the important change is independent importability and accurate object ownership.
ForMathlib → OAI implementation imports remain zero. No global simp attributes,
tactics, new mathematical declarations or changed theorem hypotheses are added.

## Reproduction and executed results

From the repository root:

```bash
bash scripts/check.sh
python3 scripts/test_checks.py
PYTHONOPTIMIZE=1 python3 scripts/test_checks.py
(cd experiments/kl-for-mathlib && python3 test_source_partitions.py)
(cd experiments/kl-for-mathlib && PYTHONOPTIMIZE=1 python3 test_source_partitions.py)
```

Environment: Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`),
Lake 5.0.0-src+5045d00, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Linux x86_64.
Pins, manifest, exporter, comparator, original coverage checker, existing Lean
behavior checks and the sixteen-closure audit are unchanged from the base.

| Executed action | Result |
| --- | --- |
| Initial `bash scripts/check.sh`: history/export/source checks and Mathlib `--no-build` readiness | Passed. Cache reused; no Mathlib source build. |
| Same run: `lake build ForMathlib OAI` | Passed, 108.554 s wall; affected modules and compatibility imports genuinely re-elaborated. The 9158-job Lake graph includes cached jobs; it is not a claim of 9158 fresh compilations. |
| Same run: new weighted import test / scaled-evaluation import test | Weighted passed; the latter stopped on test-command syntax (`if … do`, expected `then`). No library/proof failure. The command was corrected to `if … then`. Initial failure evidence is retained. |
| Final `bash scripts/check.sh warm` | All 24 stages passed; 76.893 s summed recorded stage wall time. This includes fresh Lean harness execution and current type export. |
| Final warm `lake --no-build build ForMathlib OAI` | Passed, 4.640 s; requires all maintained artifacts ready. |
| Three new Lean import/compatibility checks | Passed, 4.381 / 4.168 / 4.306 s. Exact owned-module sets exclude the unrelated support family. |
| Seven inherited Lean behavior/import/audit files | All passed, including all sixteen named axiom closures. |
| Current public-type export and comparison | 3902 old / 3902 new, no added, missing or changed type. The comparator's `relocated: 3902` is relative to the older transport baseline, not the number moved in this round. |
| Historical reference export replay | 3902 / 3902, no differences; frozen evidence replay, not historical re-elaboration. |
| Original source coverage | All 35871 non-comment lines across 34 pinned reference files covered. |
| Comparator regression suite | All 31 adversarial tests passed; inherited policy is byte-identical. |
| Partition regression suite | All 14 tests passed, also with `PYTHONOPTIMIZE=1`. Includes gaps, overlaps, missing tails, hash changes, invalid frames/cuts/IDs/parents and source/context overrides. |
| Root failure-path suite | All 18 tests passed both normally and with `PYTHONOPTIMIZE=1`. |
| Final warm `lake build ForMathlib OAI` | Passed, 4.640 s. This is a warm rebuild, not direct elaboration timing or evidence of a speedup. |

Main theorem `OAI.KLInvariance.combinatorial_invariance` has exactly
`propext`, `Classical.choice`, `Quot.sound`. Every audited closure is a subset of
that allowlist; no `sorry`, added axiom or unsafe proof bypass is introduced.

[Recorded stages and logs](evidence/responsibility-boundaries/) distinguish the
successful incremental build, initial harness syntax failure and complete final
warm validation. Raw type DAGs and compiler caches stay outside Git. This checks
preservation and Lean acceptance under the pinned environment; it does not
independently certify the original mathematical arguments, check Mathlib HEAD,
resolve novelty, or establish upstream acceptance. This round has not yet had an
independent review. GitHub CI is reported separately at publication; local cloud
validation is not a GitHub CI result.
