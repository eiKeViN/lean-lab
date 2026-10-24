# Remaining interface decisions (pinned diagnostics, not production changes)

The 25-module batch is accepted at code checkpoint 491f409adfcdd91e50ca1842311dbaa35e7dc017; see module-final-batch.md for its completed build and 59-stage audit. These remaining-boundary controls changed only ignored fixtures. No PR/main action occurred.

## Matcher boundary

Six producer modules: ForMathlib.Algebra.Module.CoefficientChange.Basic,
ForMathlib.Algebra.Module.Cover.Local,
ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis,
ForMathlib.Algebra.Module.ReflectionPair.Twist,
ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties,
ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder.

Their dependency closure is 105 legacy modules; it contains all 35 in the
Structure closure, so these counts must not be added. Outside Structure this
blocks 70. The retained batch is the other 25 of the original 130 legacy files.

Eight old names (all prefixed OAI.KLInvariance.):
- CoefficientChange.ext.match_1
- LocalCover.splitEquiv.match_3
- MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_1
- MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_3
- ReflectionFrobenius.wallCoordinate_injective.match_1_2
- ReflectionFrobenius.wallMatrix_mulVec.match_1_1
- ReflectionPairTranslation.Twist.ext.match_1
- TitsSpace.exists_common_transverse.match_1_1

The 95-module trial's ordinary modern resolver cannot access any of them; all
are available in a legacy consumer after restoring their producers. The trial
adds LocalCover.splitEquiv.match_6. No production ForMathlib/OAI Lean source
contains a direct .match_N reference (rg search); public parent declarations
remain used, so absence of direct consumers is not permission to delete names.

A real extracted CoefficientChange.Basic modern producer confirms both modern
AND legacy downstream imports lose ext.match_1, while public ext still resolves.
The small core Matcher fixture additionally demonstrates actual old-helper
application fails in a legacy consumer of the modern producer. Thus this is
more than a serializer fingerprint finding. It is not a claim of changed
mathematical propositions. The exact pin's MutualDef.lean lines 1382-1392
elaborate theorem bodies without exporting and explicitly suppress private-in-
public export; latest-version documentation was not used as pin evidence.

Compatibility feasibility: a SMALL Option-based proof-matcher fixture has an
explicit public compatibility definition under the historical qualified name,
using Option.rec. It succeeds in ordinary modern and legacy consumers, including
actual helper application and rfl. A simple exposed reference to the hidden
matcher in its producer fails, so this is not solved merely by adding expose
at the call site. These are feasibility controls, NOT validation of all eight
actual helpers or a production fix. In particular, automatically generated ext
helpers require care about collision/realization, imported private dependencies,
legacy duplicate serialization and ownership. A separate shim may change old
owner metadata and the LocalCover variant may add the new match_6 record; both
must remain explicit raw differences and need a specific policy decision.

Recommended choice: authorize a bounded old-name compatibility experiment,
using actual old helper type/value data, kernel checks, ordinary old/new name
and exact historical-type use, actual application/reduction and axiom controls.
Prefer source compatibility over allowing names to disappear. If a shim is
used, explicitly review the finite owner relocation/new auxiliary additions;
do not waive all matchers or owners. This increases modern auxiliary exposure
and maintenance but need not break old source usage. In contrast, accepting
missing names directly breaks old #check/term references even though the current
project has no such direct references. A fully in-producer preservation method
may avoid relocation but has not been established; do not claim it solved.

## Structure boundary

The closure is 35 modules, all already in the matcher closure. Current production
Structure is unchanged. The real extracted private quotientLinear and exposed
structureSheaf definitions fail as expected when the exposed body references the
private helper. Inlining ONLY its two computational expressions in structureSheaf
passes. Ordinary modern consumer vertex/upper/lower projection rfl controls pass;
private quotientLinear remains unresolvable. The unchanged legacy extracted
source passes the same three rfl controls. Full Structure proofs, exact equation
export, historical-type witness and closure regression are NOT yet run.

Recommended choice: first authorize/continue the bounded inline implementation
trial, preserving private encapsulation and all tested computation. It is not
necessary to start by publishing quotientLinear. Keep the unused original private
helper until the source/provenance strategy is reviewed. Expect an equation
representation delta from the inlined expression; validate actual old/new types
and computational old-helper definitions under fresh names before any finite
acceptance. Do not infer full compatibility merely from these three projections.

Alternatives: publishing quotientLinear adds a previously unavailable public API
name/implementation promise; withholding expose loses ordinary definition-body
and potentially rfl access. Neither was done. Inlining adds no helper public name
and is the least interface-expanding candidate, but changes two production body
expressions and therefore requires explicit source accounting and full audit.

## Controls and limitations

bounded-structure-results.json records five success/failure controls and sources.
The initial extracted Structure fixture had incorrect unnamed end commands; its
failure is retained and the labelled scope correction was tested separately.
legacy-coefficient-consumer.log and modern-coefficient-consumer.log retain actual
unknown-name failures. public-matcher-compat.log and legacy-public-matcher.log
record the generic compatibility successes; reference-matcher.log the failed
simple reference. legacy-modern-matcher-v2.log is the core actual-use failure.
The first direct binary command went through elan without a root default
configuration and failed before execution; the rerun used the exact cached binary,
without installing/upgrading anything. No public production helper was added.

The complete Structure prerequisite chain has only four remaining legacy modules:
Cover.Local, Sheaf.Iso, Sheaf.BaseChange, Sheaf.Structure. LocalCover is the sole
matcher producer on that chain. A controlled full-module inline trial is next;
its result is not included in the completed 25-module acceptance.
