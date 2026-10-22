# Dependency-closed module rollout — in progress

Starting commit: `45cc0cfcf699b7acd17a48d867c5f28bdb30bc5d` on
`codex/module-import-pilot`; local/remote identity and a clean worktree were checked.
Fixed Lean/Mathlib pins are unchanged.

The selected maximal dependency-closed region contains 226 of 261 product modules,
including the previous three modules: 223 new module migrations, 3706 of 3947
published declarations. The 35-module upward closure of
`ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure` remains legacy because its
private `quotientLinear` occurs in the exposed `structureSheaf` implementation.
No private name is made public, no private-in-public escape is enabled, and no
mathematical statement/proof/body is changed. This conservative boundary also
retains the original public aggregate entrypoints rather than breaking re-export.

`module-rollout.json` is a hash-bound exact edit/offset allowlist over the starting
Git tree. It adds public module headers/re-exports and 849 explicit data-definition
or instance exposure annotations to preserve legacy reductions. Redundant instance
expose warnings are retained, not suppressed. It does not expose theorem proof
bodies or private helpers. Its exact inverse runs before the existing proof/source
checks, and the old three-file layer remains independently bound.

The first 40 nodes of the stored topological order compiled in 161.13 seconds.
This is a checkpoint, not completed acceptance: the remaining region, modern
3706-name audit, selective import narrowing, real downstream validation and final
full acceptance still need to finish. The original 3902+45 snapshots and inherited
serializer/comparator remain unchanged. `ImplementationImports.lean` confines
explicit implementation imports to an independently generated audit root; the
production modules use ordinary public imports. Further progress/evidence will be
recorded before final delivery.
