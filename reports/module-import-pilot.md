# Bounded import/module pilot

Baseline: `999bdb033bf54abf48ff2bf9d5c12a514fdc9576` (verified against the fetched
`codex/kl-lemma-granularity` head). Branch: `codex/module-import-pilot`; no main merge.
Lean 4.34.1 at `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The single maintained project remains
`experiments/kl-for-mathlib`.

## Scope and reproducibility

This is an in-place, reversible experiment, not a whole-library migration. The
scripts require the three selected files to match the exact baseline and restore
them in `finally`. There is no alternate maintained project. Do not run the scripts
concurrently with editors/builds touching those files. Interrupted processes should
be allowed to finish restoration; a hard kill requires restoring from the recorded
baseline before continuing.

```bash
bash scripts/setup.sh
source scripts/env.sh
python3 scripts/module_pilot.py
python3 scripts/module_pilot_incremental.py
bash scripts/check.sh static
```

Logs and generated consumers go to ignored `results/module-pilot*`; compiled
artifacts remain in the existing project's `.lake`. The evidence directory contains
selected measurements and audit output, not a replacement cache.

Allowed transformations are exact, scoped operations: replace the first import
with the documented candidate imports; optionally prepend `module`, mark those
imports `public`, and insert `public section`; add `@[expose]` to the six kernel
transport definitions. All namespaces, public names, signatures, and mathematical
proof text otherwise remain unchanged. The incremental probes temporarily edit one
docstring, wrap a theorem proof using `apply id`, or wrap one compatibility definition
body with `id`. These are measured probes and are restored, not delivered proofs.
No private-name prefix stripping, global kind normalization, axiom relaxation,
manifest rewriting, or change to the full implementation audit is made.

The narrow SingleCoordinate candidate uses
`Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Basic.Real.Basic`,
`Mathlib.Algebra.Polynomial.Basic`, and `Mathlib.Tactic.Ring`.
The polynomial import preserves the existing `open Polynomial`, even though the
mathematics itself is about finite sums. This is a conservative candidate, not a
claim of minimality. Tactic/syntax availability is checked by real elaboration.

Modern consumers check original declaration kinds independently from the visible
`ConstantInfo` representation. Public type comparisons erase only binder display
names and expression metadata; constant names, universe levels, binder information,
applications, projections and let structure remain. Axiom collection uses Lean's
producer-exported closures and rejects anything outside `propext`, `Quot.sound`,
`Classical.choice`. The original CompatChecks examples exercise all three old names,
`rfl` alias equality, `.val`, and inverse maps, in both consumer modes.

## Environment and accounting

Fresh environment: 4 CPU quota, 16 GiB memory; `LEAN_NUM_THREADS=4`. Official cache
restoration is separate from target measurements. Setup took 149.221 s, with
997384 KiB maximum child RSS. It restored 8908 cache entries; no full Mathlib source
build was performed. GNU time was unavailable; the repository's `scripts/measure.py`
was used. Its maximum child RSS is a peak for an individual measured command, not
summed parallel process memory. Measurements include Lake startup, import processing
and OS page-cache effects; no cold filesystem-cache claim is made.

Initial static validation raced the dependency clone and failed because its HEAD
was not yet available; after setup it passed. Initial consumer instrumentation used
an unqualified `logInfo` and failed; it was corrected to `Lean.logInfo`. A first
raw-type log parser retained only the first line of multiline expressions; those
runs cannot establish type equality and are retained as integration cost only.

## Compatibility boundaries already observed

A modern module cannot import a legacy producer: both legacy-wide and legacy-narrow
negative controls fail at the import boundary. Adding `public section` is necessary
to preserve the selected public names; theorem-body exposure is a separate choice.
The modern theorem view is `axiomInfo` while `getOriginalConstKind?` reports theorem;
legacy and explicit `import all` views retain theorem implementation data. This is
not evidence of a new logical axiom.

For KernelTransport, both the producer and compatibility wrapper must migrate.
Exposing only one layer is insufficient for the old definitional commitments.
With all six definitions exposed, the unchanged nine compatibility examples pass
in ordinary modern and legacy consumers. With bodies hidden, all nine fail in the
ordinary modern consumer but pass in legacy. Importing **only the wrapper** with
`import all` recovers the three alias equalities but still fails the six `.val` and
inverse tests: the underlying producer is another boundary. `import all` is an
explicit implementation-view escape hatch, not a confidentiality mechanism.

The header-aware harness is separate from the existing source reconstruction,
manifest/DAG, full PublicTypes and SemanticCorpus policies. Those tools still
assume legacy headers and implementation records. A permanent integration must
add an exact allowlist for the selected header/attribute changes and retain both
implementation and public-view audits. This pilot does not broadly exempt
`axiomInfo`, alter the three-axiom policy, or strip `_private.ForMathlib` prefixes.

At the original source graph, SingleCoordinate has 9 direct and 20 transitive local
consumers; the kernel producer has 3 direct and 37 transitive consumers, and its
compatibility wrapper has 4 direct and 35 transitive consumers (including aggregate
and compatibility entrypoints; excluding root `ForMathlib.lean`). These are graph
reachability counts, not measured rebuild counts. The experiment compiles real
bounded consumers, not every reachable application module.

Narrowing changes the imported/re-exported environment even when every owned type
and proof remains identical. Code that used SingleCoordinate as an accidental
Mathlib umbrella can lose unrelated names, instances or syntax. This experiment
only guarantees the tested owned interface and consumer contracts, not arbitrary
previous transitive imports. The four narrowed imports are conservatively public;
future work may split proof-only tactics into non-public or `meta import` phases,
but no such split is assumed correct here. Deleting a transitively redundant local
edge alone would not establish a smaller import closure.

## SingleCoordinate measurements (three repetitions)

| Variant | Direct elaboration wall s | Peak RSS GiB | No-change Lake build s | Legacy consumer s | Modern consumer s |
|---|---:|---:|---:|---:|---:|
| legacy-wide | 4.64–5.07 | 6.97–6.97 | 3.69–4.01 | 4.62–4.67 | rejected |
| legacy-narrow | 1.90–1.95 | 1.91–1.91 | 1.00–1.09 | 1.87–2.00 | rejected |
| module-wide | 3.76–3.85 | 5.02–5.02 | 3.54–3.72 | 4.39–4.63 | 3.71–3.88 |
| module-narrow | 1.63–1.80 | 1.19–1.19 | 1.08–1.13 | 1.94–2.04 | 1.78–1.83 |

Direct elaboration is `lake env lean <source>` without output serialization; it is
not a clean library compilation benchmark. Warm builds validate dependency traces.
Variants ran in the listed order, not randomized; these are observed ranges on one
machine with a warm filesystem cache, not confidence intervals. Each producer was
built before consumer timing. The initial three-target build cost 11.98 s (see
`attempt1` measurements); repeat target readiness checks then required no rebuild.

In the ordinary modern view, narrow-consumer RSS was 1.18 GiB versus 4.99 GiB for
wide imports; legacy views were 1.91 GiB versus 6.97 GiB. The observed header module
counts were 10745 (legacy-wide), 2677 (legacy-narrow), 10744 (modern-wide), and 2573
(modern-narrow). These include Lean/tooling modules and are not the same unit as
Mathlib cache entries or Lake job counts.

SingleCoordinate legacy `.olean` sizes were 111240/111192 bytes (wide/narrow).
Modern public `.olean` sizes were 29968/30288 bytes, with separate private
79912/79544-byte and server 3016-byte artifacts. This is interface partitioning,
not a demonstrated reduction in total compiled disk footprint.

## Incremental edits (three edit/restore cycles)

| Probe | Rebuilt bounded modules | Wall s | Peak child RSS GiB |
|---|---|---:|---:|
| SingleCoordinate module doc | producer, legacy, import-all | 3.04–3.21 | 1.91 |
| SingleCoordinate proof term (`apply id`) | producer, legacy, import-all | 2.91–3.12 | 1.91 |
| Kernel wrapper module doc | wrapper, legacy, import-all | 10.65–10.88 | 6.99 |
| Kernel wrapper exposed body (`id <| …`) | wrapper, modern, legacy, import-all | 10.68–10.71 | 6.99 |

The ordinary modern consumer was reused in the first three cases. Public `.olean`
hashes stayed identical for these doc/proof probes; private and server hashes
changed. The exposed definition-body probe changed the wrapper's public `.olean`
and rebuilt all three consumers. Their final interface artifacts were identical,
but their build traces changed: a rebuild does not necessarily change output bytes.
The underlying kernel producer did not rebuild for wrapper-only changes.
These are precise observed cases, not a claim that every proof or documentation
edit avoids modern downstream rebuilds. Restore cycles are also retained in the
measurements. No-op probe-library builds took 1.05 s (single) and 3.61 s (kernel).
The imported kernel cluster remains broad, so these timings cannot isolate only
Lean elaboration work or predict full-library speedup.

A default-private SingleCoordinate control compiled but the modern consumer could
not resolve its original theorem name. This distinguishes declaration publicity
from definition-body exposure. The source reconstruction control rejected the
module-narrow file with `Unrecorded active proof change`; this was an expected
integration failure, not fixed by relaxing its guard. `lake shake --keep-public
ForMathlib.Algebra.BigOperators.SingleCoordinate` failed its no-build preflight
because the package's default targets include unbuilt unrelated modules. Thus no
shake minimization result is claimed, and neither `--force` nor `--fix` was used.

## Validation, cost and decision

The final four-grid/kernel run used 227.62 s of measured commands; incremental and
boundary probes used 214.63 s. Earlier integration runs cost 23.85 and 209.93 s,
including useful initial builds, a logging qualification error, the multiline
parser correction, and discovery that import-all on the wrapper does not open the
producer. These sums include repeated consumer compilation and restoration, not
just mathematical elaboration. Setup's 149.22 s is separate. No reliable token
telemetry is available. No whole-Mathlib or whole-project rebuild was run for the
microbenchmarks.

All three product files and the Lake configuration are restored byte-for-byte.
The fresh readiness claim is scoped to these targets and their upstream closure;
this environment has not freshly built all 261 product modules. Final validation
reruns the original static/source checks, no-build readiness for all three targets,
and the original CompatChecks and WeightedSumImportChecks. The 18 existing offline
failure-path regressions also pass. The retained 3902-type historical comparison
is static evidence; the fresh public-view type/axiom checks cover the five selected
theorems and six kernel definitions, not a new 3902-declaration kernel audit.

**Continue with a bounded integration stage, not a library-wide rollout.** Import
narrowing shows the larger measured loading benefit here. First add an exact
three-file header/expose transformation manifest and adapt source reconstruction,
head-span/DAG parsing, and the split implementation/public audits. Preserve all
unselected bytes and require the original interface/axiom checks. Then test actual
local downstream consumers and decide explicitly which umbrella re-export promises
must remain. Keep the six kernel bodies exposed while the old reduction contracts
are supported. A further proof-only `meta import` split or smaller candidate import
set should be a separate measured experiment. Do not select Hilbert.Basic or apply
global expose based on these results.

No permanent production migration is delivered in this branch: the deliverables
are the two runnable bounded experiments and this evidence-backed decision. This
keeps the existing acceptance checks green while making the remaining integration
cost concrete. The trial is complete; broader production adoption remains a next
stage, rather than an unreported failed migration.

Evidence: [measurements and audit records](evidence/module-import-pilot/).
To repeat, archive existing `results/module-pilot` and
`results/module-pilot-incremental` directories first; scripts refuse to overwrite
an existing measured run. Generated consumers are temporary and no extra project
or dependency lock is introduced.
