# Supported sections and split-operation API experiment

Base: `d655bbdf5d09ddc26324f997e4f9a1987309a6a7` (round 4).
Branch: `experiment/support-sections-api-20261024`. Main and earlier branches are
preserved; no PR or merge. Lean and mathlib pins are unchanged. Definitions retain
`expose`; this is an interface experiment, not a transparency migration.

## Scope and actual use

The initial scan checked the three remaining round-4 boundaries. General tensor
naturality already covers the inspected production endomorphism wrappers; no new
cross-object production use was found. Sections need the image-range inclusion
formula. Projector consumers outside `Summand` already mostly use the existing
projector laws; the worthwhile local gap is split corner compression, not another
projector coordinate alias. Adjacent single-support/costalk/duality code has two
independent production realizations with the same coordinate and degree arguments.

This yields **four coherent families**, not five artificially separated groups:

| Family | New / completion | Semantic boundary and real consumers |
| --- | --- | --- |
| Single support and costalk coordinates | New | A single-stalk vector gives a single-supported section; evaluation is its inverse; the costalk lift multiplies by incoming labels. Boundary `Support` and `FreeModel` use these instead of expanding `Pi.single`. |
| Supported duality and degree transport | New | Evaluation on a global section characterizes the stalk functional, and the inverse preserves the complementary degree. `Propagation.costalkEquivDual_pairing` and both inverse-homogeneity proofs use these APIs. |
| Image-section range | Completion | The range equivalence has the canonical image-inclusion map. `AdjointSheaf.bottImageSectionWordEquiv_coordinates` names this fact instead of relying on the equivalence constructor. |
| Split corner algebra | Completion | Compression retracts corner extension; identity extends to the projector. `Summand` injectivity, composition and primitive-projector transfer use these laws. |

There are 12 new mathematical theorems, no new production definitions or
instances. The complete names and source/consumer map are in
[API-GUIDE](../experiments/kl-for-mathlib/API-GUIDE.md). Existing mathlib
`LinearEquiv.apply_symm_apply`, extensionality and linear-map laws are reused.
Point evaluations and the identity corner law simplify toward the underlying
vector operations. Pairing, compression and homogeneity remain explicit; no new
extensionality attributes or instance search rules are introduced.

## Representative actual source

These are verbatim source excerpts, with surrounding sections omitted.

```lean
@[simp] theorem singleStalkEquivSupport_apply_self (x : V) (v : B.singleStalk x) :
    (B.singleStalkEquivSupport x v).val.val x = v.val := by
  rw [B.singleStalkEquivSupport_val]
  exact Pi.single_eq_same _ _
```

The two costalk clients previously used `change (Pi.single x …) x = _` and
`Pi.single_eq_same`. Their new proof supplies the same local finite/free basis
instances as the costalk construction, then composes the support coordinate and
incoming-label multiplication APIs; those instances are not new global instances.

```lean
theorem SplitIn.compress_liftEnd (s : SplitIn B C) (f : Hom B B) :
    s.projection.comp ((s.liftEnd f).comp s.inclusion) = f := by
  apply Hom.eq_of_maps
  · intro x v
    simp only [Hom.comp_vertex_apply, s.liftEnd_vertex_apply, s.vertex_split]
  · intro e v
    simp only [Hom.comp_edge_apply, s.liftEnd_edge_apply, s.edge_split]

theorem SplitIn.liftEnd_injective (s : SplitIn B C) : Function.Injective s.liftEnd := by
  intro f g h
  exact (s.compress_liftEnd f).symm.trans
    ((congrArg (fun q : Hom C C => s.projection.comp (q.comp s.inclusion)) h).trans
      (s.compress_liftEnd g))
```

Previously injectivity expanded both vertex and edge nested record maps. Now
it applies the same compression law to an equality of corner extensions.
Composition likewise uses the two evaluation APIs and the split identities.
The inverse-degree theorem is phrased through the pairing characterization and
proves the needed identity of functionals by `LinearMap.ext`, instead of exposing
the `dualToSupport` constructor in the two production homogeneity arguments.

## Implementation changes with frozen clients

Run `source scripts/env.sh`, then from the maintained project run
`python support_sections_trial.py` with no concurrent build. The script uses
ordinary module artifact setups, never `import all`, and restores source bytes and
normal `.olean*` hashes in `finally`. Scratch artifacts live under `results`.

1. **Inverse-first supported equivalence.** Replace `singleStalkEquivSupport`'s
   bijective single-section map by the inverse of the bijective evaluation map.
   This is the same linear equivalence, with a different computational route.
   The old API proof fails. Reprove **only `singleStalkEquivSupport_val`**, using
   the inverse identity and the support condition away from the vertex. The
   remaining API statements/proofs and all four adapted downstream files remain
   byte-identical. Graded duality, boundary support, free support and propagation
   all compile. Old boundary/free support fail exactly at `change Pi.single …`;
   old graded duality and propagation pass. The latter already used an adequate
   boundary or were not sensitive to this change; no benefit is claimed for them.
2. **Corner reassociation control.** Replace `i.comp (f.comp p)` by
   `(i.comp f).comp p`. Existing API proofs and both old/new frozen `Models` and
   `AdjointSheaf` compile without repair. This perturbation is definitionally
   indistinguishable at the relevant uses and **does not demonstrate maintenance
   savings**. It is a negative control, not a second successful pressure test.

Six whole client files are hash-bound across the two trials (one, `Models`, has no
production edits this round). The support-coordinate family has discriminating
pressure-test evidence. Pairing/degree, image-section and corner APIs have actual
production coverage, but this batch does not establish their stability under
arbitrary representation changes. In particular, it does not claim a separate
projector or general-tensor implementation pressure test.

The failed inverse prototype (dependent `Pi.single` elaboration) is retained
separately, with successful restoration. Development logs also retain a reversed
equality-composition error, required local finite-basis instances, and a direct
large-equivalence expansion that exceeded 200,000 heartbeats. Equality composition
replaced that expansion and compiled at the existing heartbeat limit. No compiler
research or unrelated changes were needed.

## Validation and exact policy

The complete 9,186-target incremental build passed (85.782 s after local
compilation). The raw full interface grew from 3,989 to 4,001 records: exactly
12 theorem additions, zero generated additions, and no missing, changed or
relocated old declarations. Full checks are still pending. Local production compilation and ordinary
imports already pass; 18 new/consumer axiom closures use only `propext`,
`Classical.choice`, `Quot.sound`.

`api-support-source.json` records the exact seven-file source delta; its inverse
feeds the immutable earlier checks. `api-support-types.json` records exactly
the 12 added theorem full records, not a prefix exemption. Earlier export and
migration baselines remain unchanged. The inherited proof-evolution fixture needs
one exact pre-module `Propagation` input, bound to its immutable Git blob/hash;
this is separate from accepting the final seven-file overlay. Regression checks
reject extra bytes, altered/missing records and applying the overlay to that
historical fixture. The round-4 source roundtrip test compares its exact view
through the new bounded inverse; registry isolation mocks only the newer layer.

## Costs and reproduction

PENDING measured build/check costs. Mathematical source delta: seven production
files, +143/-49 lines. The batch is evaluated by the mathematical boundary and
actual consumers, not declaration count or line reduction. Token telemetry is
unavailable; no token estimate is supplied.

Commands: `scripts/check.sh` for the full build/check workflow, or after a recorded
successful complete build `scripts/check.sh warm`; `python support_sections_trial.py`
for the isolated changes. Trial patches, frozen hashes, outcomes, restoration,
ordinary-import logs, development failures, build/check metrics and accepted
input bindings will be linked here after final archival. Earlier reports remain
unchanged.
