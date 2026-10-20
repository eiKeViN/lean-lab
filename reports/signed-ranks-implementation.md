# Signed-dihedral paired-rank implementation — 2026-10-20

## Outcome and reproduction

All acceptance checks passed on local branch `codex/kl-signed-ranks`, based on
the reconnaissance commit and pristine baseline `dc7adaa35047517a600a2b80ff5aefcf28eb905a`.
No push, PR, merge, main mutation, permission change, or unrelated-repository write.
`experiments/kl`, root validation scripts, pins and provenance are unchanged.
The new experiment copies all 34 baseline modules; 33 remain byte-identical.
Only its `DihedralIntervals.lean` differs. No mathematical source failure occurred.

```bash
bash experiments/kl-signed-ranks/check.sh
bash experiments/kl-signed-ranks/check.sh --measure  # optional sequential timings
```

The runner requires the validated baseline cache, verifies all 34 pristine blobs,
pins/configuration and a one-file changed-source allowlist, then checks Mathlib
readiness without source building. Dependencies are shared; experiment OAI build
artifacts are separately copied/reflinked. Initial `lake --no-build build OAI`
passed immediately after copying: no cold baseline or Mathlib rebuild was needed.
Lean 4.34.1, Lake 5.0.0-src+5045d00 and mathlib d13f23b remain unchanged.

## Mathematical change

`SignedDihedral.arrowAfter_pair` proves the reviewed formula under |i|<|j|:
with L=i.natAbs, M=j.natAbs, E=(L<r ∧ Odd (L+r)), the pair contribution equals
`if E then (if 0<j then 1+(if M<r then 1 else 0) else (if r<M then 1 else 0)) else 0`.
`arrowAfter_pair_below` supplies the below-upper-rank corollary.
Exactly `countAfter_base`, `countAfter_pos_formula`, `countAfter_neg_formula`
use this shared API; none reopens both endpoint comparison lemmas.
The literal `c=j` hypotheses and separate singleton-top summand are unchanged.
The existing general parity bridge is moved before its first use, proved using
`Int.odd_add`, `Nat.odd_add`, `Int.natAbs_odd`, `Int.natAbs_even`, and reused.
No global simp registration, custom tactic, sorry, axiom, or proof bypass.

## Verification and measurements

Final runner: `results/signed-ranks/20261020T093534722065Z`.
Selected results and exact executed commands are committed in
[evidence/signed-ranks-results.json](evidence/signed-ranks-results.json).
The complete small source delta is [evidence/signed-ranks-source.patch](evidence/signed-ranks-source.patch).

| Stage | Actual result |
| --- | --- |
| Baseline identity/pins | Passed before and after; strict original verifier unchanged |
| Changed module | First actual build 13.821 s; final cached check 3.336 s |
| Boundary checks | Passed, 5.475 s: symbolic zero/source-rank/top-rank checks; 22 concrete pair cases and 8 count cases, both signs and parities, ranks immediately below/at/above the upper rank, empty eligible ranges, literal c=j and higher tops |
| Downstream library | Sequential recovery build passed in 57.655 s; PlaneLocalization was already built during the interrupted attempt, so this is not a clean all-affected-modules timing. Final cached downstream check passed in 3.599 s |
| Axiom audits | All eight passed in 4.036 s; every closure exactly propext, Classical.choice, Quot.sound |
| Public types | All 3897 original non-private, non-internal declaration types preserved across all 34 modules; exactly two new public helper declarations |
| Type export cost | Before 8.768 s / 7293424 KiB peak RSS; after 8.887 s / 7294492 KiB |
| Final warm OAI build | Passed, 3.216 s, 980640 KiB peak child RSS |
| Existing script regressions / shell syntax / whitespace | Passed |

The eight audited declarations are the two new helpers, three migrated consumers,
`countAfter_difference`, `PlaneBasis.laterCount_difference`, and
`combinatorial_invariance`; exact output is in [evidence/signed-ranks-audit.log](evidence/signed-ranks-audit.log).
Public-type comparison uses exact shared-expression constructor interning, not
hash-only equality. Binder names/information and universes are retained; metadata
annotations are stripped. Lean's `Name.isInternal` excludes generated `_proof_`
and `_simp_` auxiliaries, whose types are implementation details; no named public
theorem is exempted. Declaration bodies are intentionally not compared.

Two comparable, sequential direct-elaboration pairs for unchanged versus changed D:

| Pair | Before | After | Change |
| --- | --- | --- | --- |
| 1 | 8.814 s | 8.894 s | +0.91% |
| 2 | 9.275 s | 8.850 s | -4.58% |

No material regression observed in two sequential timing pairs; no statistical
significance test or speedup claim.
The earlier simultaneous exploratory pair is excluded. Direct elaboration is
not compared to the reconnaissance warm-readiness timing. RSS is maximum child
process RSS, not aggregate parallel memory; no cross-worker benchmark is claimed.

Nonblank physical proof-body lines (after `:= by`, excluding statement/blank lines):

| Scope | Before | After |
| --- | --- | --- |
| Three consumers | 63 (20/25/18) | 57 (18/20/19) |
| Two new helpers | 0 | 11 (8/3) |
| Pair API + consumers | 63 | 68 |
| Four parity-related proofs | 48 | 10 |
| Combined selected proofs | 111 | 78 |

The pair abstraction adds five lines overall while removing three copies of
endpoint recombination. Parity consolidation accounts for the net shortening.
Whole module: 2274 → 2254 physical lines. These are source-size measurements,
not kernel proof-term sizes. Representation independence is bounded: counting
clients stop unpacking endpoint sign/order arithmetic, but integer coordinates
remain. Automation stability means explicit local rewriting, not a cross-version
claim. Original mathematical scope/comparator equivalence is not independently
certified by compilation or this refactoring.

## Failures and limits retained honestly

- Two initial zero-rank harness rewrites failed on numeral/coercion matching;
  a `simpa only` specialization fixed the check. The source helper had compiled.
- I mistakenly overlapped a metadata preflight with a downstream build. Cgroup
  memory exhaustion killed both checks; an owned orphan child was terminated.
  This was not a permission denial or a mathematical failure. Sequential builds
  then passed, reusing completed artifacts.
- A text-tree metadata exporter also exhausted memory alone. Compact DAG output
  and direct file writes replaced it. Intermediate exporter elaboration errors
  were corrected without `#eval!` or accepting Lean's error placeholders.
- Initial comparison included compiler-generated auxiliaries and correctly
  refused their differences; public/internal classification was corrected using
  Lean's general predicate, not per-theorem exceptions. Final comparison passed.
- Raw failed attempts and 28-MB-class type DAGs remain ignored under `results/`;
  successful metrics, audit, type-dump SHA-256 values and source hashes are in
  the committed compact evidence JSON. No failed stage is represented as passed.

No build remains running and no implementation blocker remains. Independent final
read-only review approved the supplied mathematical diff, validation runner, type
exporter and boundary checks, with no blocking defect. That review did not rerun
builds or inspect the live checkout; the execution evidence above is from this
workspace. Permission to push and create a draft PR remains pending. No push, PR
or merge has been performed; this work remains local-only.
