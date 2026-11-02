# Publication and preserved history

The publication is assembled on the current remote `main`, from the isolated
quantum experiment tree at local commit `8fa207059701cb2b44b4913017d3717b5682115b`.
It does not merge unrelated branch history. Original local commits and private
transfer archives remain on the original experiment branch and local ignored disk.

`source-baselines.json` binds all 14 published historical files and the six
previously accepted bridge sources. `draft-to-verified.patch` records the exact
six-file repairs. `failures/` contains a bounded selection of actual compiler
failures, including inference, finite enumeration, and function-expression
matching issues; these are historical failed attempts, not final build results.
No proof statement or dependency pin was changed for publication.

Publication adjustments make reproduction portable: source identity uses the
committed hashes rather than unpublished Git objects/private Library transfers;
setup fetches the additional PMF cache modules used by the real proof chain.
The old private receipts are deliberately excluded. This changes the scope of
archive-preservation checks, not the proof, axiom, or source-identity acceptance
criteria for published files. The previous full private archive verification
is not claimed as something a fresh public clone can repeat.

`publication/` holds the bounded final accepted build/audit report and logs.
These selected records are committed because this publication explicitly calls
for necessary validation/failure evidence; normal run output remains ignored.
The retained command paths describe the actual validation machine and are not
requirements for a new checkout. Run scripts from their own project directory.
