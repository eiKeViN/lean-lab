# Execution evidence

Paths mirror `results/boundary/`. `*.inputs.json.gz` are pre-execution identities
from the repository recorder. JSON companions to logs contain actual command,
status, wall/CPU seconds and maximum child RSS. Expected failures are retained.
`core-run-v3` is the successful 23-case core suite; `project-replay` is the final
successful bounded project suite. Earlier attempts are failures/partial runs,
not extra successful validation. Fresh setup is `setup-recorded`, 313.23 seconds.

Only source/data/logs are retained, never .olean/.ir/native artifacts. Large
repr experiments and identities use deterministic gzip. `stalk-old.json` and
`stalk-new.json` and final replay's old/new JSON contain actual expression DAGs
and auxiliary proof values. `abandoned-repr-sources` records the final abandoned
text-codec iteration after execution; not every earlier uncommitted source
iteration is retained, though pre-execution hashes and failure logs are kept.
All final replay sources are in research/module-boundary or the two retained
shadow source files. Algebra links point at the sole project's artifacts during
execution; no long-lived project copy is included.

`production-identity.json` checks all 358 starting project/script/provenance
tracked files byte-for-byte. `pins.json` binds Lean's actual version, installed
official source-file hashes, Mathlib commit and clean status. `SHA256.json` binds
retained evidence files; the evidence index and this README are not self-hashed.
See the report for limits and interpretation of measurements, including core
runner's cumulative child RSS high-water fields. No reliable token telemetry.
