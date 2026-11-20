# Verification scripts

- `cache_inputs.py` collects the fixed workspace's Mathlib import frontier for the official cache.
- `audit.py` runs the Lean audit, rejects prohibited source constructs and checks module coverage.
- `record_acceptance.py` records a successful fresh check with dependency and source identities.
- `source_check.py` checks file structure and records source hashes.
- `audit.lean` inspects every exported project declaration, records its public type and transitive
  axioms, and rejects custom axioms, `sorryAx`, unsafe code and partial definitions.
- `nolints-style.txt` is intentionally empty: no text-style exceptions are granted.

Run `bash ../check.sh` from this directory's parent. `check.sh` owns build, tests, style and axiom
checks. `setup.sh` prepares the pinned Lean release and requests official binary cache entries.
