# Dependency-closed module rollout

**Completed: 125 of 261 product modules now use the module system, including
122 new migrations; 12 additional headers have conservative narrow imports.**
The remaining 136 products retain their exact starting sources. All 43 final
acceptance stages passed after a real complete ForMathlib/OAI build. No
mathematical proof, statement or definition body was rewritten, and no historical
type/kind/private-name exception was added.

The starting commit is `45cc0cfcf699b7acd17a48d867c5f28bdb30bc5d`, descended from the
requested `999bdb033bf54abf48ff2bf9d5c12a514fdc9576`, on
`codex/module-import-pilot`. The accepted code execution is captured at checkpoint
`0f5c3a741d6096b070dabc8dce660944761ae295`; subsequent delivery changes only reports,
evidence and regenerated lemma-index navigation. No main merge or PR was made.
The maintained project remains `experiments/kl-for-mathlib`.

Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain fixed. The upstream Git tree was
checked clean. The already-ready fixed cache was reused; setup took 4.86 s.
Fresh-environment initialization was not measured. Mathlib no-build readiness
was required; no full Mathlib source build, clean, upgrade, force or shake fix
was used.

## Delivered scope and compatibility

The selected region is dependency-closed: 113 ForMathlib and 12 OAI products.
`module-rollout.json` binds 122 new source transformations to the starting Git
objects with exact character offsets and before/after hashes. It adds module /
public-section headers, public re-exports, and 252 explicit data-definition or
instance exposure annotations. Abbreviations and automatic exposure rules remain
Lean's own; redundant exposure warnings are retained. Private declarations are
not mechanically made public. The earlier three-file rules remain independently
bound and their production sources are unchanged in this round.

`module-rollout-imports.json` separately binds the 12 narrowed headers.
Their exact inverse runs before inherited source/proof transport checks. All
122 inverses recover the exact starting mathematical text; all 136 held product
files and 14 protected audit/snapshot/configuration files match their starting
hashes. DAG edges record public/meta/all flags. Production contains no import-all
or private-in-public escape. The 363 local implementation edges are preserved;
removing a redundant edge alone is not presented as a closure improvement.

Complete implementation and ordinary modern consumers have separate audit roots.
`ImplementationImports` is deliberately legacy, with explicit ordinary imports
of the selected producers plus the aggregate, obtaining full implementation data.
The original PublicTypes serializer, thmInfo/proof-value controls, 3902-type
snapshot, 45 additions and comparator remain unchanged. Modern kind handling is
bounded to the selected 1196 records and checks `getOriginalConstKind?`.

Final evidence establishes:

- Original 3902 types and all 45 added types pass their unchanged comparisons.
- All 3947 normalized records also equal the starting producer export in every
  field: name, universe parameters, mathematical type, kind and module owner.
  There are zero missing, added, changed or relocated records. Raw TSV hashes
  differ; the inherited serializer's complete record dictionaries are identical.
- All 1196 ordinary modern records match strictly. Their visible representations
  are 778 theorem-as-axiomInfo, 86 theorem, 306 definition, 10 constructor,
  8 inductive and 8 recursor. Original kinds are independently checked;
  theorem-as-axiomInfo is not a new logical axiom.
- Every selected modern axiom closure is limited to propext, Quot.sound and
  Classical.choice. Existing root and extracted-lemma axiom audits, proof-reuse
  checks, old names, `.val`, inverse maps, rfl and regression controls pass.
- Compiler proof aliases use a finite hash-bound baseline list and full
  proposition serialization. Both views reject private rewriting; no new
  `_private.ForMathlib` prefix stripping or global kind relaxation was introduced.

`ModernCoordinateChecks` imports only the narrowed coordinate producer plus Lean.
Its projection `.val` and restriction equalities still close by rfl. It also
asserts that unrelated `MeasureTheory.integral_const` is unavailable.
`ModernCoordinateMathlibChecks` demonstrates the explicit consumer repair with
`Mathlib.MeasureTheory.Integral.Bochner.Basic`. No production consumer repair
was needed. This preserves owned API contracts while documenting the reduction
of incidental Mathlib re-exports; arbitrary external import-only uses are not
promised compatible. Aggregate entrypoints retain their re-export roles and
remain legacy, so modern consumers must use selected focused module paths.

## Actual closure observations

For the 12 delivered focused targets, setup.json importArts fall from 8908 each
to 579–1309, with Mathlib entries falling from 8530 to 328–1052. Full before/after
module lists and setup hashes are retained. The two further tested narrow
candidates later held legacy are excluded from these delivered ranges.

This does not shrink the default aggregate Mathlib closure: final ForMathlib has
9089 importArts and OAI.Architecture 9115, each still including 8530 Mathlib entries.
No controlled whole-library before/after time or memory comparison was run.
No clean-build speedup, aggregate memory improvement or universal proof/doc-only
incremental rebuild claim follows from this batch. Many consumers remain legacy
and still load implementations.

Read-only shake was run without fix/force on the initial 14 ready targets and
again on the final 12. Its bounded diagnostic temporarily scopes Lake
`defaultTargets` to exactly those targets, first checks no-build readiness, then
restores lakefile bytes in a finally block. Final raw shake status is 1 with
suggestions, not an automatically applied patch. Broad tactic-registration
suggestions were not blindly applied; conservative data and source-used tactic
imports were selected and actually compiled. Missing imports discovered during
editing are preserved as failed attempts.

## Failed scopes and why 136 products remain legacy

1. Initial checkpoint `b505bfa` selected 226 nodes (223 new). Structure and its
   consumers were held after inspecting private quotientLinear in the public
   structureSheaf implementation. AttachBottom then failed with its original
   attachStalkMap body exposed. Controlled implementation-import variants for
   ModuleData.Basic, GradedSheaf.Defs, Generators and Mathlib did not fix it;
   withdrawing exposure did. Exposure was not withdrawn in delivery: the
   producer and consumer closure were held legacy. The broader attempt also
   required combining expose inside an existing instance_reducible attribute
   group; that module is now held as well.
2. The revised 181-node region compiled, including 14 narrow candidates, but
   strict auditing rejected six missing / one added compiler matcher names,
   seven implementation type-expression changes and ten modern changes. No
   snapshot, kind rule, private rewrite or finite matcher waiver was accepted.
   The affected owner/consumer closure was restored. Its downstream build was
   interrupted after 233.16 s; orphan compiler children were explicitly stopped.
3. Checkpoint `2d68b405d20ddea232710bac58792303590aa97d` retained 131 nodes.
   Its regional 1336-record audits and complete build passed, but full acceptance
   failed on Sheaf.stalkMap.eq_1, first realized in held legacy
   GradedSheaf.Properties. The selected producer Sheaf.Basic.stalkMap caused a
   historical type-expression difference. All 45 added types matched. Restoring
   Basic and five selected consumers to their exact original legacy sources
   fixed the focused real Properties rebuild/export. The entire 125-node
   result was then rebuilt and fully accepted; this is a required consequence
   of six source changes, not a repeated no-change build.

These differences are strict compiler/interface-expression findings, not claims
that the propositions are logically inequivalent. No definitional-equivalence
exception was used to override the inherited comparisons. Exact rejected scope
plans, type exports/diffs, failure logs and execution identities are retained.

## Cost and execution identity

The fixed allocation is four CPU and 16 GiB, LEAN_NUM_THREADS=4, with the inherited
serial compiler gate. Lake per-job times include queue/lock waits and must not be
summed as isolated elaboration times. RSS below is the largest child process, not
summed concurrent-process RSS. Command timings exclude pre-launch input hashing,
editor/operator/review/report time. Reliable token telemetry is unavailable.

| Recorded operation | Wall seconds | Result |
|---|---:|---|
| Existing-cache setup | 4.86 | ready |
| Initial 40-node topological prefix | 161.13 | pass |
| Rejected 131-node full library build | 1639.09 | build pass; later type audit failed |
| Its first full acceptance | 123.06 | fail on one old equation type |
| Restored Properties target / fresh export | 30.80 / 8.61 | exact old record restored |
| Accepted 125-node full library build | 1500.67 | all targets pass |
| Final 43-stage acceptance | 152.83 | all pass |
| Final no-change full-library build (inside acceptance) | 3.65 | no recompilation |
| Fresh semantic corpus | 8.44 | unchanged records/docs |

The accepted full build's peak child RSS is 7622572 KiB (about 7.27 GiB), and final
acceptance's 7781036 KiB (about 7.42 GiB). These are actual integration costs, not
clean-build comparisons. Earlier overlapping import-edit trials and interrupted
runs are retained but are not controlled timing comparisons or a manufactured
total-cost sum.

`scripts/recorded_run.py` captures actual command, Git/diff identity and tracked /
untracked file hashes before each run. Final acceptance used checkpoint 0f5c3a7;
all 346 captured project/script inputs still match, except the subsequently
regenerated LEMMA_INDEX navigation. No Lean source, checker, manifest, pin or
harness changed afterwards. Index rendering/checking have their own execution
identities. Intermediate tool revisions are not described as the final harness:
the initial 14-target shake script is retained and hash-matched to its actual
execution; the final diagnostic derives 12 targets from the final plan.

Some early ignored `.lake` scratch inputs were not separately hashed by the
wrapper; their retained copies are explicitly marked as captured after execution,
with no invented old hash. The repaired Properties probe instead uses an absolute
input path, whose pre-execution hash and retained source match. Final acceptance
uses tracked audit roots, whose execution hashes are complete.

Fresh full-view semantic extraction matches all 2627 prior records, including
338 documented theorems. All 45 indexed lemmas match their compiled source
docstrings; only navigation line numbers change. Original, expansion, comparison
and library retrieval groups run successfully. This is a complete legacy/server
corpus check, not evidence of ordinary public-view documentation availability.

At checkpoint 0f5c3a7, the connected GitHub reader reports zero check runs and
zero workflow runs. Direct API access was blocked by the network proxy (403),
then the supported connected GitHub GET route succeeded. Final delivery head and
CI state are rechecked after push; absence of CI records is not a passing CI run.

## Reproduction and next workflow

Use fresh output labels; the recorder refuses to overwrite execution identities.
From the repository root:

```bash
bash scripts/setup.sh
source scripts/env.sh
python3 scripts/recorded_run.py results/recheck/full.log bash scripts/check.sh
# Once the complete product closure is ready:
python3 scripts/recorded_run.py results/recheck/warm.log bash scripts/check.sh warm
python3 scripts/recorded_run.py results/recheck/shake.log python3 scripts/diagnose_rollout_imports.py
python3 experiments/kl-for-mathlib/module_rollout.py --write-checks
```

The full validation builds the controlled implementation audit import first.
For fresh documentation afterwards, run ImplementationSemanticCorpus.lean with
SEMANTIC_CORPUS_OUT, then render_lemma_index.py / semantic_search.py as recorded in
the retained commands. Gzip exports and unchanged comparators also permit offline
rechecking of captured evidence; that is not a fresh Lean elaboration.

The compatible 125-node region is worth retaining: it provides ordinary modern
interfaces and demonstrably smaller focused closures without altering mathematics.
Do not automatically migrate the remaining boundary. First obtain small pinned
reproducers for private implementation exposure, AttachBottom elaboration and
compiler-generated names/types, and review any proposed compatibility policy.
Further conservative import narrowing can be considered independently.

For future batches, run strict regional implementation and modern audits before
expensive full builds, and include known historical legacy realizers, especially
simp/unfold consumers. Compiler realization ownership can differ from the defining
producer: stalkMap is in Basic while its historical eq_1 is realized in Properties.
An owner-filtered regional audit missed that boundary. Keep the unchanged complete
3947-record audit as final authority; neither a regional pass nor a whole build
alone is sufficient. Preserve compatibility/aggregate re-exports and distinguish
declaration visibility, body exposure, public import and meta execution phase.
These visibility controls are not a confidentiality mechanism.

[Retained evidence](evidence/module-rollout/) includes final stages, full/public
exports, source scope, closure lists, actual execution identities and failed scopes.
