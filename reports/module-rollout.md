# Dependency-closed module rollout — strict batch acceptance in progress

The starting commit is `45cc0cfcf699b7acd17a48d867c5f28bdb30bc5d` on
`codex/module-import-pilot`. Local/remote identity and a clean worktree were checked.
The fixed Lean 4.34.1 / Mathlib pins are unchanged; this round reused the already
ready upstream cache. It did not measure fresh-environment initialization.

The initial checkpoint `b505bfa` selected 226/261 product modules (223 new).
Compilation exposed a second boundary: `GradedSheaf.AttachBottom.attachStalkMap`
failed elaboration with its original definition body exposed. Controlled variants
adding implementation imports of ModuleData.Basic, GradedSheaf.Defs, Generators,
and even Mathlib did not fix it; withdrawing exposure did. We retained the
original reduction contract by leaving this module and its consumers legacy,
rather than editing its proof/body or hiding the definition. Separately,
`Sheaf.Structure` and its upward closure remain legacy because private
`quotientLinear` occurs in the implementation of public `structureSheaf`.

The 181-module intermediate build passed, including 14 narrow import candidates.
Strict auditing then rejected that scope: six historical compiler matcher names
were absent, one was added, seven full implementation type expression hashes
changed, and ten modern type expressions differed. These checks were left failed;
no baseline was updated, no private prefixes stripped, and no finite matcher
exemption is delivered. The rejected scope, exporter and diffs are retained as
experimental evidence. Its full library build was interrupted and orphan compiler
children explicitly terminated; it is not a completed library acceptance.

The 131-node checkpoint compiled the entire library successfully (1639.09 s),
but its first full acceptance failed after 123.06 s: the historical
`Sheaf.stalkMap.eq_1` type expression changed even though its first-realizing
legacy consumer `GradedSheaf.Properties` was held unchanged. The selected producer
`Sheaf.Basic.stalkMap` caused this downstream compiler realization boundary.
All 45 added lemma types matched. We restored that producer and its five selected
consumers to their exact starting legacy sources; no mathematical or comparison
change was used. A focused real rebuild of Properties and a fresh full-view export
now reproduce the exact historical stalkMap.eq_1 record. This is why region-only
type checks cannot replace full downstream acceptance.

The **delivered candidate is 125/261 modules, 122 new**, with **1196/3947** historical
declaration records in the modern audit and **12 narrowed import headers**.
The 136 held modules are the exact upward closure of the two earlier boundaries
plus finite owners rejected by strict implementation/modern comparison. Their
sources remain byte-identical to the starting commit. This remains a large,
dependency-closed rollout; it deliberately stops at demonstrable compatibility
boundaries. Mathematical names/statements/proofs/definition bodies are preserved
by exact inverse source comparison. Production uses no implementation imports or
private-in-public escape. All 1196 modern records now match the original snapshot
strictly, with no missing-name or changed-type exemption.

`module-rollout.json` binds the immutable starting tree and each exact header/
attribute edit by offset and before/after hash. There are 252 explicit exposure
annotations. The broader rejected candidate also revealed that an existing
`@[instance_reducible]` attribute needed `expose` inside its group; stacking a
second group failed parsing. That module is now held legacy. Source/DAG
rules preserve public/meta/all flags. The previous three-file rules remain
independently bound. `module-rollout-imports.json` separately binds 12 manually
reviewed narrow headers; missing dependencies found by compilation are recorded
as failed experiments and repaired only by imports.

Read-only shake was run without `--fix` or `--force` on 14 ready focused targets.
Its exact executed script is retained and hash-matched to the execution identity.
The delivered diagnostic now derives its 12 targets from the final bounded
import plan; that final tool revision is distinct from the historic 14-target run.
The diagnostic script temporarily scopes Lake defaultTargets to exactly these
same targets, first checks their no-build readiness, and restores lakefile bytes
in a finally block. It does not claim the held aggregate closure was ready.
Broad tactic-registration suggestions were not automatically applied; data
imports and explicitly used tactic modules were selected and compiled.
Actual setup.json transitive importArts fell from 8908 to 579–1309 for the
12 delivered focused targets (Mathlib entries: 8530 to 328–1052). Both full
module lists and setup hashes are retained; the two additionally tested but held
modules are excluded from this delivered range. Aggregates still import Mathlib,
so these focused reductions do not establish a smaller aggregate closure.
The 363 original local implementation edges are preserved; this round does not
pretend removal of transitively redundant edges alone shrinks a closure.
No controlled whole-library before/after timing exists, so no whole-library
speedup is claimed. Narrowing these focused headers intentionally does not
promise re-export of arbitrary unrelated Mathlib declarations.

Complete implementation and modern public views have independent audit roots.
`ImplementationImports` is a legacy audit root with explicit ordinary imports of
the selected modules, which obtain full implementation data; `import all` requires
a modern root and is not used here. A failed legacy `import all` probe is retained.
The inherited full serializer and 3902+45 snapshots/comparator remain unchanged.
Modern theorem axiomInfo representations are accepted only when their original
kind is theorem; every selected positive record retains its original kind/type
and has its axiom closure restricted to propext, Quot.sound and Classical.choice.
The modern audit observes 827 theorem-as-axiomInfo records, 92 ordinary theorem
records, 379 definitions, 14 constructors, 12 inductives and 12 recursors. Original
kinds are checked separately; theorem-as-axiomInfo is not a new logical axiom.
Compiler proof aliases use a finite, hash-bound baseline list and full proposition
serialization; no new private-prefix rewrite is allowed.

`ModernCoordinateChecks` independently imports only the narrowed coordinate
producer plus Lean. Its `.val` projection and restriction equalities still close
by `rfl`; it asserts that unrelated `MeasureTheory.integral_const` is absent.
`ModernCoordinateMathlibChecks` shows the explicit consumer repair by importing
`Mathlib.MeasureTheory.Integral.Bochner.Basic`. Neither test changes production
consumers. This demonstrates the incidental Mathlib re-export boundary; it does
not claim arbitrary external import-only usages remain compatible.

The six matcher names from the rejected intermediate scope remain entirely
outside the selected dependency closure. Their original legacy modules and
consumers are retained. Complete 3947-record acceptance is still required; a
modern-only pass cannot substitute for it.

Every measured command uses `scripts/recorded_run.py`, capturing execution-time
tracked/untracked source hashes and Git/diff identity before execution. Some
early scratch Lean inputs under ignored `.lake` paths were not separately hashed
by that wrapper: their retained copies are explicitly marked as captured after
execution, with no invented pre-execution hash. Final acceptance uses tracked
audit roots and captures their actual execution identities. Intermediate executions may
use different verifier versions; their individual input identities are retained.
Early 40-node compilation took 161.13 s; the revised region initially passed in
92.86 s with many artifacts already warm. These are integration-cost observations,
not clean-build comparisons. Failed builds/probes and interrupted duplicate
integration runs are preserved, not presented as successful measurements.

Pending: final narrowed region, full real downstream build, strict implementation
and modern audits, semantic/documentation extraction, final acceptance, evidence
packaging, push and remote/CI verification. Checkpoints are not completion.

The rollout supports continued use of the compatible 125-node region. Further
module expansion should stop at the held boundary until a small pinned-version
reproducer explains the generated-name/type-expression changes and an explicit
compatibility policy is reviewed; do not simply update snapshots. Independently,
more import narrowing can be considered in dependency-closed regions. Run strict
region implementation and modern audits before the expensive whole-library build:
the rejected 181-node attempt spent 233 s in an interrupted downstream build,
including orphan child cleanup. Test early; batch the eventual full build once.
Preserve re-export responsibilities at compatibility/aggregate entrypoints and
avoid treating ordinary declaration visibility, exposed definition bodies,
public import re-export and meta execution phase as interchangeable controls.
