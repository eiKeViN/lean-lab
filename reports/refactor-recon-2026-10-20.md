# KL refactoring: first-slice decision packet

## Readiness and scope

- Local starting HEAD and freshly fetched remote main both equal
  `dc7adaa35047517a600a2b80ff5aefcf28eb905a`; the starting tree was clean.
  No intervening work was overwritten. Work is now on the local-only branch
  `codex/kl-refactor-recon-20261020`; no push, PR, or main mutation.
- Read AGENTS.md and the repository check scripts. `bash scripts/check.sh kl
  recon-warm` passed: 34/34 source blobs match upstream provenance, dependency
  revisions match, Mathlib has 8923 ready targets, and OAI is up to date.
  Warm command time: **3.165 s**, peak child RSS 998036 KiB; no KL modules rebuilt.
  Metrics/log: [evidence/recon-warm.json](evidence/recon-warm.json),
  [evidence/recon-warm.log](evidence/recon-warm.log).
- Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), Lake
  5.0.0-src+5045d00, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
  Retained caches: 4.0 GiB `.cache`, 8.0 GiB KL `.lake`; OAI build directory
  328 MiB. No setup/download was necessary. No saved settings changed.
- The existing unchanged-baseline audit records exactly `propext`,
  `Classical.choice`, `Quot.sound`. It was **not rerun** in this reconnaissance.
  Compilation/axiom closure does not independently certify mathematical scope,
  comparator equivalence, or agreement with the informal argument.

All declaration references below refer to this exact baseline. Let D denote
`experiments/kl/OAI/RepresentationTheory/KazhdanLusztig/DihedralIntervals.lean`;
C, G, and T denote `CharacterReciprocity.lean`, `GradedSheaves.lean`, and
`TerminalKernels.lean` in the same directory.

## Two candidate slices

### A. Signed-dihedral endpoint pairs into rank contributions — recommended

**Evidence.** `SignedDihedral.arrowAfter_pos` (D:1468) and `arrowAfter_neg`
(D:1488) already translate endpoint coordinates into arithmetic tests. Three
later proofs each recombine that pair themselves:

| Genuine consumer | Actual repeated work |
| --- | --- |
| `SignedDihedral.countAfter_base` (D:1537; pair use 1547) | Both endpoint rewrites; restrict to ranks below the upper endpoint; convert an indicator sum to a filtered cardinality. |
| `SignedDihedral.countAfter_pos_formula` (D:1688; pair use 1702) | Both endpoint rewrites; nested-condition arithmetic identifies the 1-or-2 contribution used by `positiveCount`. |
| `SignedDihedral.countAfter_neg_formula` (D:1718; pair use 1733) | Both endpoint rewrites; prove every rank at/above the upper endpoint contributes zero before truncating a sum. |

The coordinate-normalization layer also repeats parity analysis:
`arrowAfter_next` (D:1510) locally proves the same general natAbs parity fact
later named `odd_add_abs` (D:1610). Specializations are `odd_add_natAbs`
(D:1455) and `odd_sub_natAbs` (D:1464). The pinned Mathlib already supplies
`Int.natAbs_odd` (`Mathlib/Algebra/Ring/Int/Parity.lean:94`) and `Int.odd_add`
(:75); no new parity typeclass or tactic is warranted.

**Boundary.** Separate coordinate/order normalization from finite-rank counting.
Keep `Before` and single-endpoint comparisons below the boundary; summation
clients consume a paired-rank contribution and do not reopen its sign/order
case split. Retain the existing `eligible_ranks_card` (D:1027),
`total_outgoing_count` (D:1563), and `positiveCount_formula` (D:1650);
their different counting problems do not justify a new generic summation engine.

**Risks.** r=0 double representation, r=|j|, negative j, natural truncated
subtraction, top c=j versus |j|<|c|, and the singleton top term. Finite-period
GoodIndex/canonical-top hypotheses belong to the geometric bridge, not this
arithmetic helper. Do not replace c=j with merely |c|=|j|. Do not touch
`finite_before_same`/`finite_before_next` (D:975/1001) in the first slice.

### B. Scaled-image transport and model-sum interface consolidation — defer

**Evidence.** A real generic API already exists: `Sheaf.ScaledImages` and
`scaledImages_iff` (C:443/450), product/pi/zero closure (C:508/526/542), and
`ModelSum.scaledImages` (C:548). The pi result already allows arbitrary index
types over a commutative ring; the common scalar is essential. A replacement
"generic model sum" abstraction would duplicate established capabilities.

The actual mismatch is witness-level reconstruction in `Sheaf.Iso.scaledImages`
(T:19), despite existing same-edge image transport `Iso.map_lowerImage` and
`Iso.map_upperImage` (G:631/639), plus `EmbeddedModule.map_scaled` and
`map_eq_scaled_iff` (G:657/665). It could use a single submodule-equality proof
through `scaledImages_iff`, after checking the equivalence between the current
pointwise submodule scalar and `EmbeddedModule.scaled` (map by lsmul).

**Consumers, without inflation.** Product, pi and zero closure feed one
`ModelSum.scaledImages` induction (C:548). That theorem and `Iso.scaledImages`
have **one direct application site**, `localized_boundary_scaledImages`
(T:245, calls at 258–261). Other genuine boundary clients are
`structure_scaledImages` (T:62, uses equality conversion at 73) and
`scaledImages_denominator` (T:946, unpacks witnesses). These are different
operations, not three independent clients of a new transport helper.
`ambient_boundary_scaledImages` (T:418) and `boundary_plane_scaledImages`
(T:462) are downstream consequences, not evidence of repeated generic proofs.

**Risks/cost.** Universe parameters differ across sheaves; the same edge map must
transport both images and preserve the same scalar. The generic API is split
across large files in a linear import chain (G → ... → C → ... → T); extracting
it into an earlier module can cause broad recompilation or cycles. A future
transport-only improvement is plausible, but would primarily shorten one proof;
product/model-sum reuse and representation independence already exist.

## Proposed first interface (design only; not implemented or Lean-checked)

Inside `SignedDihedral`, add one explicit paired-rank theorem and, only if useful,
a below-upper-rank corollary. For integers i,j with |i|<|j| and natural r, set
L=i.natAbs, M=j.natAbs and E(r)=(L<r ∧ Odd (L+r)). The proposed equality is:

```text
arrowAfter i (i+j) r + arrowAfter i (i+j) (-r)
  = if E(r) then
      if 0<j then 1 + (if M<r then 1 else 0)
      else (if r<M then 1 else 0)
    else 0
```

For r<M this reduces to `if E(r) then 1 else 0`, for either sign of j.
No extra parity assumption on i+j is needed for this local equality.
A finite sanity check passed 1664 cases (i,j in [-8,8], r in [0,12], |i|<|j|);
this is **not a Lean proof**. The formula still requires formal proof.

Move/reuse the existing general parity bridge before its first consumer;
preserve all old public names/statements. Existing single-endpoint lemmas may
prove the pair theorem, but the three counting clients should use the pair API.
Do not add global simp rules for the nested formula; use named rewrites and
local `simp only`/arithmetic closure. No custom tactic is proposed.

**Three direct API consumers:** D:1537, 1688, 1718 above. Two real indirect
regression clients: `countAfter_difference` (D:1765) and the actual plane-root
`PlaneBasis.laterCount_difference` (D:1974, invokes it at 2003).
`countAfter_next_formula` (D:1741) remains a regression case, not a claimed
consumer of this same-source endpoint-pair interface.

## Falsifiable acceptance criteria

1. The three counting proofs use the paired-rank API; none repeats the joint
   `arrowAfter_pos`/`arrowAfter_neg` expansion. Their public types, including top
   and parity hypotheses, stay unchanged. The singleton-top summand stays intact.
2. Parity normalization has one general implementation; `arrowAfter_next` no
   longer duplicates its four-sign proof. Prefer existing Mathlib parity facts.
3. The interface mentions only integer coordinates/natural ranks/parity, not a
   CoxeterSystem, PlaneBasis, root realization, or finite period. This reduces
   coupling of counting proofs to endpoint sign arithmetic; it is **not** a
   coordinate-free reformulation of dihedral geometry.
4. Existing arithmetic and geometric downstream clients compile; audit the new
   helper and main theorem with only the existing allowed axiom set. No sorry,
   added axiom, unsafe bypass, removed tests, or weakened assumptions.
5. Record helper+client proof sizes separately. API reuse succeeds only with all
   three consumers; total proof shortening is a separately measured outcome,
   not promised. Report target compile time and warm repeat against this baseline;
   investigate >20% regression on a repeated comparison, not on one noisy sample.
   Automation stability means explicit rewrites/local closure with no new global
   tactic behavior, not a claim of stability across untested Lean versions.

## Small implementation/validation plan for independent review

1. Review this interface and its boundary cases before implementation. Keep this
   local branch; preserve baseline commit dc7adaa and all provenance manifests.
   Do not edit `experiments/kl` to evade its strict source-identity verifier.
2. Create a separate `experiments/kl-signed-ranks` experiment from the pinned
   baseline, changing only D initially. Keep baseline source and checks intact.
   Reuse the exact toolchain and content-addressed mathlib cache; reuse pinned
   dependency checkouts without mutating them. Copy/reflink OAI build artifacts
   separately (do not share a writable build directory). First test artifact
   reuse with `lake --no-build build OAI`; path/trace reuse is **not yet tested**.
   If reuse fails, inspect the planned rebuild before accepting cold-build cost.
3. Prove the pair formula; consolidate parity normalization; migrate only the
   three named clients. Use a small experiment-owned runner that verifies the
   pristine baseline, dependency pins, and an explicit changed-file allowlist,
   then builds the experiment. Do not disable baseline verification globally.
4. Compile D first, then its experiment's downstream targets and theorem audit;
   compare public types and axiom closures with the pristine experiment. Include
   r=0, r=M, signs, empty eligible range, and c=j in focused proof/examples.
   Measure like-for-like direct elaboration of pristine D and changed D, plus
   affected-target and warm timings; the 3.165-second readiness check is not a
   cold elaboration comparator. Preserve failure logs before any mathematical redesign. No push/PR/main update without the next authorization.

## Reading aids and limitations

Read the [signed-count guide at 8004f18](https://github.com/jiajunma/combkl/blob/8004f18a6cab3bb1f113b48abb5d2ea4c37bcaaf/docs/knowledge/nodes/kl.reflection_combinatorics/signed_count_difference.md)
and [model-sum guide at 12aba06](https://github.com/jiajunma/combkl/blob/12aba06b1cd4a12344a1dd86e710fe48a250af52/docs/knowledge/nodes/kl.localization/model_sum_scaled_images.md).
They helped locate declarations; the evidence and consumer counts above come
from the pinned local Lean source. No upstream code/docs were synced.

The web tool's raw-link fetch for the second guide failed with "restricted URL";
it was not retried. The normal GitHub page had already loaded successfully and
provided the guide text. Initial shell startup briefly reported no usable
execution environment; it succeeded after the ready environment context arrived.
No approval-review denial occurred. There is no current reconnaissance blocker;
the proposed helper proof and new-experiment artifact reuse remain untested.
