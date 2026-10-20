# Kernel transport responsibility migration

**Current acceptance:** passed under `kl-kernel-anonymous-owner-v1`: exact except
explicitly permitted anonymous-instance owner relocation markers. The original
strict failure below is retained as historical evidence. No mathematical source
or client changed after built commit `a9568d548f48febeb2aa99b4ede8130e4eabba68`.

Work branch: `codex/kl-kernel-transport`. Frozen implementation reference:
`7225842219ed3844b2fbd9cf3d95f9b65bec862c` (`experiments/kl-signed-ranks`).
The local architecture report at `4030418f6b98ff1d5c6f4a513b8ca1d67b790555`
precedes this implementation. No publication or merge is part of this round.

## Change and limits

The isolated `experiments/kl-kernel-transport` package moves the three original
kernel equivalence implementation bodies from `BottSamelson.lean` to
`OAI/LinearAlgebra/KernelTransport.lean`, under `OAI.LinearEquiv`. The new path is
our local classification; Mathlib's nearby APIs are in
`Algebra/Module/Submodule/{Ker,Equiv}` and `Algebra/Module/Equiv/Basic`.

`KernelTransportCompat.lean` retains all three original `OAI.KLInvariance` names
as `def` wrappers with explicit original types and fully qualified RHSs.
The two actual Bott clients and their eval/homogeneous proofs are untouched.
`kernelTargetEquiv` still has no production client; it is not counted as a reuse
gain. Mixed transport is only k-linear, and Q still has no A-module assumption.
No implementation proof rewrite, weakened assumption, new class or simp rule.

The validation runner checks each implementation body byte-for-byte, and checks
that Bott differs only by exact removal of those sections and one compat import.
Pristine, signed-ranks, scripts and provenance are checked against the frozen Git
reference both before and after validation. The other 33 inherited KL modules
and all three package configuration files are byte-identical to signed-ranks.

This is API discoverability and separation of local import responsibilities.
It does not establish proof shortening, a new representation-independent
mathematical abstraction, tactic stability improvements or a speedup.

## Reproduce

From the repository root, with the existing signed-ranks reference cache ready:

```bash
bash experiments/kl-kernel-transport/check.sh
```

The runner refuses missing reference/Mathlib artifacts, shares dependency
checkouts, and copies/reflinks an independent build directory. No source-only
Mathlib fallback, dependency update or upstream lakefile is run. All Lean checks
are sequential, using the repository environment (`LEAN_NUM_THREADS=4`).

Toolchain: Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`),
Lake `5.0.0-src+5045d00`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

An initial version query at the repository root reported no global default
toolchain. Querying inside the pinned experiment returned the versions above;
no default or saved environment setting was changed.

## Validation record

The full library compiled, but strict API acceptance **failed** for the three
moved compatibility declarations. This is a tested experiment with a precisely
identified validation/design blocker, not an accepted migration.

Run: `results/kernel-transport/20261020T120849004389Z`.
The runner exited 1 with:

```
Existing public type/kind changed: ['OAI.KLInvariance.kernelMixedEquiv', 'OAI.KLInvariance.kernelTargetEquiv', 'OAI.KLInvariance.kernelSourceEquiv']
```

Initial new-module builds passed (Lake per-job times 5.5 s generic, 3.7 s compat).
The measured runner reused these artifacts: its generic/compat times below are
warm checks, not direct elaboration measurements.

| Executed stage | Wall seconds | Result |
| --- | ---: | --- |
| Reference Mathlib readiness | 2.907 | passed |
| Reference OAI readiness | 3.334 | passed |
| Experiment Mathlib readiness | 2.958 | passed |
| Generic module (warm) | 3.245 | passed |
| Compatibility module (warm) | 3.240 | passed |
| Independent API/import checks | 5.114 | passed |
| Compatibility checks | 4.859 | passed |
| Changed Bott and real clients | 146.507 | passed |
| Inherited signed boundary checks | 5.220 | passed |
| Full downstream OAI build | 917.592 | passed |
| Sixteen axiom closures | 4.367 | passed |
| Reference type export | 8.913 | passed |
| Experiment type export | 8.853 | passed |
| Final import/API/name-resolution checks | 5.428 | passed |
| Final warm OAI build | 3.450 | passed |

The source build reached all 36 local modules / 8960 Lake jobs. Bott's
146.507 s and the 917.592 s downstream stage are separate costs. The latter
included IntegralPairings (Lake job time 724 s), the historical longest module
(721 s in the pristine run). These historical values are context, not controlled
performance comparisons. No Mathlib source build was started.

Independent checks contain eleven generic examples and nine compatibility
examples: all three forward/inverse payloads by `rfl`, all old/new equivalences
definitionally equal, mixed k-scalar compatibility, full/zero kernels, a
nontrivial coordinate swap and the distinct-scalar complex/real case. Exact local
imports are one generic module or generic plus compat. The final 5.428 s harness
run also verified that `LinearEquiv.coe_coe`, `symm_apply_apply` and
`apply_symm_apply` resolve to the root Mathlib names inside `OAI.LinearEquiv`.
No production Lean source changed after its successful compilation.

The inherited BoundaryChecks file is byte-identical: four symbolic examples,
22 concrete pair cases and eight count cases. It passed unchanged.

All sixteen printed closures were present exactly once and passed the allowed
axiom set. The three new definitions and three wrappers use only `propext` and
`Quot.sound`. The two Bott kernels, seven signed/geometric targets and main
use `propext`, `Classical.choice`, `Quot.sound`. Full output is committed in
`reports/evidence/kernel-transport-audit.log`.

One manually launched warm measurement inherited earlier shell child CPU/RSS
accounting due to the shell's final exec. Its wall value remains recorded as
`warm-shell`; the table uses the clean fresh-subprocess repeat, 3.450 s, CPU
4.054/1.833 s, peak RSS 990664 KiB. This is artifact readiness, not a speedup.
Unsupported CLI options were separately checked to fail before builds.

## Exact API blocker and diagnostic evidence

The strict export preserves every binder name/info, universe, expression
constructor, constant name and declaration kind; it only removes metadata.
No comparison rule was weakened. Counts and module ownership match the plan:
34 reference modules, 36 experiment modules, 3899 to 3902 public declarations,
exactly the three new definitions, and exactly three old owners moved from
BottSamelson to KernelTransportCompat. The other 3896 old declarations are
structurally identical, including binder names and kinds.

The three moved types differ only in Lean-generated anonymous instance binder
names. There are seven differing binder-name fields in source transport, seven
in target transport and seventeen in mixed transport. For example, the first
source instance binder is represented as:

```
Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».OAI.RepresentationTheory.KazhdanLusztig.BottSamelson 3079144783) "_hygCtx") "_hyg") 3
```

After relocation, only `BottSamelson` becomes `KernelTransportCompat` in this
name. Numeric hygiene components remain identical. The diagnostic exhaustively
checked every differing expression field: all are `forall` binder-name fields;
all constants, universes, binder information, user-written binder names and
other expression fields match. The same owner-marker effect occurs between old
implementations and the new generic definitions. Diagnostic evidence does not
turn the failed strict check into a pass.

Per-module exclusions use the unchanged Lean `isPrivateName` / `Name.isInternal`
predicates, without per-name exceptions:

| Module | Private before/after | Internal before/after |
| --- | --- | --- |
| BottSamelson | 3 / 3 | 217 / 182 |
| Generic module | absent / 0 | absent / 38 |
| Compat module | absent / 0 | absent / 3 |

The public total is exactly the planned 3902; it was not adjusted to hide these
compiler-generated declarations. Every module's excluded counts are preserved
in `kernel-transport-api-diagnostics.json`. Focused raw DAG data for the three
old types and six relocated/wrapper types is in
`kernel-transport-focused-types.json`. Full raw exports remain ignored; their
SHA-256 values are in `kernel-transport-results.json`.

## Original design decision (resolved by the rule below)

The approved plan required exact binder names as well as independent old imports
and three owner relocations. Lean's generated binder names encode their source
module, so these requirements conflict under the current representation-level
predicate. I have not introduced metaprogramming to forge the old compiler names,
changed wrapper ownership back, or silently normalized names to obtain green.

Recommended next decision: permit only the declared owner-module substitution
inside generated anonymous `inst.«_@».…._hygCtx._hyg` binder names for the three
explicitly mapped moved declarations (and their three new-definition matches),
while requiring all numeric hygiene components, base names, user-written names,
binder info, constants, universes, kinds and all other expression fields to match.
This must be independently assessed as an explicit amendment to the strict
comparison contract; it is not implemented in the acceptance runner.

Keeping wrappers in Bott would instead retain its generated names but fail the
planned lightweight compatibility import and owner map. Reconstructing old
compiler hygiene names through custom elaboration would add fragile maintenance
machinery. Neither alternative was applied.

## Final state and limits

The final protected-file check confirmed 100 source/tooling/provenance files
byte-identical to the frozen reference; pristine blob/pin verification passed
again. No build remains running, no operation was denied or left uncertain, and
no mathematical source failure was found. The remaining failure is the executed
strict API check (exit 1), pending the design decision above.

The local report and experiment are preserved for review. No push, PR, merge,
saved configuration or permission change; no GitHub CI claim. The experiment
README now warns that the default reproduction command intentionally still
reports this strict acceptance failure. No independent final source audit of
this new implementation is claimed.

## Final acceptance under the reviewed bounded rule

This supersedes the earlier pending status, not its raw evidence. Rule version:
`kl-kernel-anonymous-owner-v1`. Only six explicit declaration pairs are eligible:
three old names B→C, plus their three new implementation correspondences B→G.
Each pair has fixed outer forall slots, fixed context IDs and numeric scopes.
Both Names must exactly match the structured N(owner,h,s) shape, the raw repr
must agree with that expected shape, and binderInfo must be instImplicit.
All other fields remain exact. No lambda/let, nested domain or other declaration
receives an exception. No global stripping, alpha normalization, const rewrite
or interning mutation. The exception comparator uses no memo at all.

`PublicTypes.lean` adds NAME records while leaving NODE/TYPE and the other raw
records unchanged. After removing only NAME records, both exports' SHA-256
values exactly equal those saved in the original built-commit evidence. Existing
saved exports were also hashed and matched. All 36 mathematical sources, pinned
configuration and original focused harnesses were checked byte-for-byte against
`a9568d5…` before and after this run; original strict-failure evidence is frozen.
Workflow file hashes separately identify the new exporter, comparator and tests.

Run: `results/kernel-transport/20261020T125532453057Z`.
`bash experiments/kl-kernel-transport/check.sh` exited 0. The source readiness
checks passed before all build targets, which remained warm. No long source
rebuild or installation occurred in this acceptance round.

| Final aggregate stage | Wall seconds | Result |
| --- | ---: | --- |
| Reference OAI readiness | 3.436 | passed |
| Experiment OAI readiness | 3.245 | passed |
| Generic warm target | 3.354 | passed |
| Compat warm target | 3.406 | passed |
| Independent API/name/import checks | 6.361 | passed |
| Wrapper checks | 5.073 | passed |
| Bott warm target | 3.557 | passed |
| Inherited signed boundaries | 5.170 | passed |
| Full OAI warm target | 3.420 | passed |
| Sixteen axiom closures | 4.357 | passed |
| Structured reference export | 9.367 | passed |
| Structured experiment export | 9.036 | passed |
| Mutation/shared-DAG/actual-export tests | 13.254 | passed |
| Final warm OAI | 3.310 | passed |

All 14 test groups passed with no skips in the aggregate, including real exports.
The tests reject altered constants, constant universes and declaration universe
parameters, user binder names, numeric context/scope components (124 individual
mutations across the six pairs), binderInfo, owner tokens, unlisted slots,
nested forall/lambda/let contexts, parameter domains/results/bvars, declaration
kind/set/count/ownership and raw Name/supplement disagreement. Shared raw node
pairs are tested across permitted/unmapped declarations in both orders, and
across outer-slot/nested-domain contexts; inputs and global interning stay
unchanged. Unit fixtures run without Lean; real exported data is also checked.

Final counts: 3899→3902 public declarations; 34→36 modules; exactly three owner
moves and three new API names. The other 3896 old declarations are fully exact.
There are 31 accepted fields in the three old moved types and 31 in the three
new implementation correspondences. Every accepted difference, Name tree,
context ID, scope, slot and rule version is recorded in
`reports/evidence/kernel-transport-accepted-differences.jsonl`.

The final aggregate audit again passed exactly sixteen targets. The six kernel
API/wrapper closures use propext and Quot.sound; main and relevant downstream
closures use only propext, Classical.choice and Quot.sound. This is local Lean
validation under the stated comparison contract, not an independent final audit
or GitHub CI result. There is no unverified cold-elaboration speed claim.

Final machine evidence is `kernel-transport-acceptance-results.json`; test output
is `kernel-transport-comparator-tests.log`. The original blocked results,
focused raw DAG and 31-field diagnostic files were not overwritten. No current
acceptance blocker remains. No push, PR, merge, access or environment-setting
change is part of this round.
