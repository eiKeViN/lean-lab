# Expanded lemma extraction plan — 2026-10-22

Continue `codex/kl-lemma-granularity` from `0fb4b2e`; do not merge main.
Five proofs across four files, eight preselected extraction points, four declined
candidates: see the exact names, source hashes and reasons in
[evidence/lemma-granularity-expansion/plan.json](evidence/lemma-granularity-expansion/plan.json).

Choose independent mathematical responsibilities. A second use is evidence, not
a requirement. Judge whether the original proof now delegates a meaningful
mathematical step, not just whether lines shrink. Preserve the old 3902 types
and the first five added types; list/audit all new declarations. Keep the old
plan and evidence unchanged. Extend the bounded source guard explicitly, retaining
its negative tests, exact source diff, pristine reconstruction and all existing
checks. No global simp attributes, custom tactics or general API redesign.

Reuse short source docstrings and the generated semantic index. Record before/after
proof structure, kept/declined candidates, all failed attempts, actual calls, new
incremental command costs and limits. The fixed queries above are not a blind
benchmark. One controlled direct pair per changed file suffices for this expansion;
repeat only to diagnose a material concern. Token telemetry is unavailable.
