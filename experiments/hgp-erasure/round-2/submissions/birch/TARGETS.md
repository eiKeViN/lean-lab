# Approved targets

Status: formalization in progress. No A–E target is certified complete yet.
Only targets with complete proofs, permitted transitive axioms, matched locked
types, and recorded semantic review will be marked complete here.

| Source | Planned module | Declaration mapping | Status |
|---|---|---|---|
| A: actual HGP checks and parameters | `Targets.Parameters` | Awaiting reviewed exports | In progress |
| B: arbitrary-erasure rank/complement identities, both sectors | `Targets.Erasure` | Awaiting reviewed exports | In progress |
| C: inference and minimum failing-erasure distance | `Targets.Inference` | Awaiting reviewed exports | In progress |
| D: both universal whole-strip identities | `Targets.Strip` | Awaiting reviewed exports | In progress |
| E: both concrete examples using the general objects | `Targets.Examples` | Awaiting reviewed exports | In progress |

The frozen project uses Lean 4.33.1 and the absolute local dependencies in
`lean/lake-manifest.json`. Do not run `lake update` or install dependencies.
In the supplied environment, build offline with:

```sh
cd lean
lake --no-cache build
```

The maintainer builds snapshots with `python3 tools/build.py`; successful
builds publish compiled artifacts from `local/buildtree/`. Once all target
statements have landed, the default build will also include `Challenge` and
`TargetsCheck`, and `python3 tools/audit.py` will run the type/axiom check and
local Lean comparator. Semantic review is recorded in `coord/targets-review.md`.

Initial infrastructure smoke builds and the library-root repair are green.
These builds do not establish any mathematical target's completion.
