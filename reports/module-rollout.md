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

The **delivered candidate is 131/261 modules, 128 new**, with **1336/3947** historical
declaration records in the modern audit and **12 narrowed import headers**.
The 130 held modules are the exact upward closure of the two earlier boundaries
plus finite owners rejected by strict implementation/modern comparison. Their
sources remain byte-identical to the starting commit. This remains a large,
dependency-closed rollout; it deliberately stops at demonstrable compatibility
boundaries. Mathematical names/statements/proofs/definition bodies are preserved
by exact inverse source comparison. Production uses no implementation imports or
private-in-public escape. All 1336 modern records now match the original snapshot
strictly, with no missing-name or changed-type exemption.

`module-rollout.json` binds the immutable starting tree and each exact header/
attribute edit by offset and before/after hash. There are 287 explicit exposure
annotations. One existing `@[instance_reducible]` attribute needed `expose` added
inside its group; stacking a second attribute group failed parsing. Source/DAG
rules preserve public/meta/all flags. The previous three-file rules remain
independently bound. `module-rollout-imports.json` separately binds 12 manually
reviewed narrow headers; missing dependencies found by compilation are recorded
as failed experiments and repaired only by imports.

Read-only shake was run without `--fix` or `--force` on 14 ready focused targets.
The diagnostic script temporarily scopes Lake defaultTargets to exactly these
same targets, first checks their no-build readiness, and restores lakefile bytes
in a finally block. It does not claim the held aggregate closure was ready.
Broad tactic-registration suggestions were not automatically applied; data
imports and explicitly used tactic modules were selected and compiled.
Actual setup.json transitive importArts before/after counts will be retained.
No controlled whole-library before/after timing exists, so no whole-library
speedup is claimed. Narrowing these focused headers intentionally does not
promise re-export of arbitrary unrelated Mathlib declarations.

Complete implementation and modern public views have independent audit roots.
`ImplementationImports` confines explicit implementation imports to auditing;
the inherited full serializer and 3902+45 snapshots/comparator remain unchanged.
Modern theorem axiomInfo representations are accepted only when their original
kind is theorem; every selected positive record retains its original kind/type
and has its axiom closure restricted to propext, Quot.sound and Classical.choice.
Compiler proof aliases use a finite, hash-bound baseline list and full proposition
serialization; no new private-prefix rewrite is allowed.

The six matcher names from the rejected intermediate scope remain entirely
outside the selected dependency closure. Their original legacy modules and
consumers are retained. Complete 3947-record acceptance is still required; a
modern-only pass cannot substitute for it.

Every measured command uses `scripts/recorded_run.py`, capturing execution-time
file hashes and Git/diff identity before execution. Intermediate executions may
use different verifier versions; their individual input identities are retained.
Early 40-node compilation took 161.13 s; the revised region initially passed in
92.86 s with many artifacts already warm. These are integration-cost observations,
not clean-build comparisons. Failed builds/probes and interrupted duplicate
integration runs are preserved, not presented as successful measurements.

Pending: final narrowed region, full real downstream build, strict implementation
and modern audits, semantic/documentation extraction, final acceptance, evidence
packaging, push and remote/CI verification. Checkpoints are not completion.
