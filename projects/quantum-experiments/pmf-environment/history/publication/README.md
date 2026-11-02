# Publication acceptance — 2026-11-02

The final layout was checked with `source env.sh; python3 compare-check.py`.
Both libraries built successfully; all six new modules elaborated independently;
all 63 explicit declarations have only propext, Classical.choice and Quot.sound
in their transitive axiom closure. Exact commands, exits, source hashes and
local dependency slices are in report.json and the accompanying logs.
The 20 published baseline files passed SHA-256 identity checks.

No proof source or dependency pin changed from the accepted comparison.
The portable source-identity guard replaced local unpublished-Git and private
archive requirements. The clean-clone setup recipe was inspected and made
complete for its PMF cache dependencies, but a separate fresh download/build
was not run. Validation used the existing matching isolated toolchain/cache.
No whole-dependency independent kernel replay or deployment was performed.
