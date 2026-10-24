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

The closure is 35 modules, all already in the matcher closure. The real modern
prerequisite chain has only four currently legacy producers: Cover.Local,
Sheaf.Iso, Sheaf.BaseChange and Structure; LocalCover is the only matcher producer
on that chain. Production files remain unchanged after the experiment.

A controlled four-producer trial compiled the full real Structure module and all
its proofs, with only the two quotient calls in structureSheaf inlined and the
usual module/public/expose transport. The private quotientLinear declaration was
retained. No public helper compatibility definition or ownership exception was
introduced. Ordinary modern historical use succeeded for 135 of 136 names/types,
including exact levels/attributes, kernel/defeq and three-axiom checks, with 20
actual old helper type/value pairs reconstructed under fresh names. Those include
the private quotient and old LocalCover matcher; both old computational definitions
are well-formed in the new ordinary environment, which is useful feasibility
evidence but not restoration of the missing historical matcher name.

Vertex/upper/lower rfl and structure/base-change vertex rw/simp controls pass.
The same regional exporter reports 198 records before/after, zero type/kind/level/
owner differences, only missing LocalCover.splitEquiv.match_3 and added match_6.
That raw comparison remains failed. Full candidate downstream regression was not
run after this known name failure; the four-module candidate is not delivered.

All source bytes and four original olean hashes were restored, and full project
no-build readiness passes. The complete 25-module accepted audit inputs remain
unchanged. The delivered branch still has 156 modern and 105 legacy modules.
See module-final-batch.md and evidence/module-final/structure/ for all controls,
raw differences, restoration identities, failures and measured costs.

Recommendation: retain the inline implementation as the next compatible candidate;
there is no demonstrated need to publish quotientLinear or withdraw expose. The
remaining delivery gate is the old LocalCover matcher API, plus subsequent full
integration acceptance once that gate is addressed. Publishing quotientLinear
would add a previously unavailable public name/implementation promise; withholding
expose would lose definition-body access. Neither was done. The safe inline trial
changes two implementation expressions but leaves the private interface and all
tested computation intact; it is not a global fingerprint waiver.

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
matcher producer on that chain. The completed controlled trial is described above; it remains outside the delivered
25-module acceptance because the matcher name failure is not waived.
