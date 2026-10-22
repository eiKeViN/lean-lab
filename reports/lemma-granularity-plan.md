# Lemma granularity pilot plan — 2026-10-21

Architecture PR #6 is merged at `a234ae5be6f77763e2014aad2cddd69e6aa50755`;
its tree equals verified `6b02eeb`. New branch: `codex/kl-lemma-granularity`.
Maintain the same project; do not merge this pilot into main.

Four proof samples in three existing modules:

- S1 finite-character cancellation: finite weighted-sum exchange and elimination.
- S2 single-coordinate difference: a second actual production use of elimination.
- S3 scaled polynomial reciprocity: real square-root witness and clearing scaling.
- S4 bottom polynomial equality: inverse interval transport, with substantial KL context.

Ten candidate steps, fixed before edits:

| ID | Step | Initial disposition |
| --- | --- | --- |
| C1 | Exchange the two weighted finite sums (S1) | Adopt if the explicit signature elaborates cleanly. |
| C2 | Evaluate a weighted sum supported at one normalized coordinate (S1/S2) | Adopt; two actual parent clients. |
| C3 | Rewrite an equality to zero after subtracting (S1) | Reject: existing simp facts already express it. |
| C4 | Package `sub_eq_zero.mp` (S1) | Reject: standard one-step fact, no new responsibility. |
| C5 | Positive square-root witness in the open unit interval (S3) | Adopt as a small analytic boundary. |
| C6 | Clear the reciprocal scaled-polynomial difference (S3) | Adopt as a separate algebraic step. |
| C7 | Nonvanishing of a natural power (S3) | Reject: existing `pow_ne_zero`. |
| C8 | Equality away from bottom transported through the inverse interval iso (S4) | Adopt as the context-heavy sample. |
| C9 | Distinct target endpoints via rank difference (S4) | Decline this pilot: endpoint/order facts already provide the object-level API; avoid another contextual wrapper. |
| C10 | Derive equality from the opposite scalar inequalities (S4) | Reject: `linarith` already closes the two-line combination. |

Expected additions: five lemmas, with unchanged old statements and API. Exact
signatures and feasibility are decided by Lean; failures/changes are recorded.
A source allowlist, immutable pristine reconstruction and hash-bound evolution
diffs will explicitly authorize only the three files and four old proof edits.
The old 3902-type reference is not overwritten: compare every old type and
separately check the exact added-name/type set. Keep the inherited type reader,
serialization/collision checks, baseline audit and regression suite intact.
Audit each addition and changed client as well as the original named closures.

Semantic scheme: 1–3 sentence Lean docstrings are the mathematical explanation.
A small index stores declaration names, source parents, keywords and decisions;
it links to Lean rather than duplicating signatures or maintaining one Markdown
specification per source file. Test search with the six frozen natural-language
queries in `evidence/lemma-granularity/plan.json`, without declaration names.
Use the same lexical ranking before/after; also ablate new docstrings from the
final corpus to separate documentation from the addition of named lemmas.
This is a small, non-blind feasibility pilot, not a statistical benchmark.

Reuse evidence separates original-site calls, the real second production client
for C2, focused applicability tests, and future potential. Include at least two
additional applicability checks; do not call test examples production reuse.

Record wall-clock intervals and executed-command timings, including failed
iterations. Separate one-time validation/search infrastructure from extraction
edits and incremental validation. Selection and initial design were interleaved
14:47:53–14:52:29 UTC and cannot honestly be split after the fact. Later phases
are timestamped explicitly. Preserve cache reuse evidence. No model token-usage
telemetry is exposed; report it unavailable, never infer tokens from characters
or command-output token counts. Report per-attempt/per-retained-lemma costs with
that limitation, without a speedup or general-quality claim.
