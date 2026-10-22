# Module rollout evidence

Final accepted scope:125 products(122 new),12 narrow headers,1196 modern records.
Execution code checkpoint:0f5c3a741d6096b070dabc8dce660944761ae295.
Start:45cc0cfcf699b7acd17a48d867c5f28bdb30bc5d. See ../../module-rollout.md.

Primary final evidence:

- whole-125.log/json/inputs.json.gz:actual complete product build.
- final-acceptance.log/json/inputs.json.gz and final-validation/stages.json:
  all43 final stages, each actual stage log, full3947/modern1196 exports.
- full-vs-starting-export.json:all3947 normalized records match every field.
- scope-and-identity.json:exact122 inverses,136 untouched products,old3/protected14.
- final-input-identity.json.gz:346 actual code/source inputs; only derived index
  navigation changes after acceptance. index-change.json binds that limitation.
- closure-before.json.gz / closure-after-final.json.gz / delivered-closure-summary.json:
  real setup importArts. aggregate-after.json.gz records broad aggregate limits.
- semantic-corpus.json.gz / corpus-comparison.json:2627 records,338 docs unchanged.
  lemma-index logs verify all45 source docstrings; four retrieval groups run.
- public-representations.json and rollout-public-types stage log distinguish visible
  representation from original kind and three-axiom closures.

Historical failures are not final acceptance:

- closure/expose-syntax/attach-* preserve the initial226-node failure/probes.
- rejected-181 retains scope/exporter and exact full/public comparison failures.
  region-full-ready/public-ready TSV exports substantiate those differences.
- whole-strict is the131-node successful build whose final-validation failed.
  rejected-131 retains that failed33-stage run and its full export/type difference.
- properties-restored/restored-properties-types/restored-stalkMap-comparison show
  the exact historical record restored by holding Basic and its consumer closure.
- Early narrow import trials, premature public-loader failure, interrupted runs
  and overlapping edit trials are retained, not performance comparisons.

Each inputs.json records its own actual execution version. Do not equate an older
run with the final harness. diagnostic-sources/capture-provenance.json explicitly
marks early ignored scratch files captured only afterwards; no old hash is invented.
The repaired Properties absolute input and executed initial shake script are
hash-matched to actual pre-execution identities. Final fixtures are tracked.

The original baseline TSV is not duplicated here: its producer export is retained
at ../module-integration/full-types.tsv.gz and its raw SHA is recorded in the
full-vs-starting comparison. Gzip files preserve the complete text; comparing them
offline rechecks captured evidence, not fresh Lean elaboration.

checkpoint-ci.json records direct proxy403; checkpoint-ci-app.json records the
successful supported GitHub reader(0 check runs /0 workflows for0f5c3a7). Final
push head and CI are rechecked separately after this evidence commit.
SHA256.json hashes every evidence file except itself.
