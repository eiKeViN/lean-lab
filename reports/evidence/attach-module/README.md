# Accepted three-module execution evidence

The full 49-stage run used code checkpoint 424bcdf25e746d12573af9a410e8e25ae6018fcf.
`full-acceptance.inputs.json.gz` binds all 1386 inputs before the run; its JSON
companion records total measured cost and successful exit. At completion all
inputs still matched. `final-input-match.json` identifies only two subsequent
README navigation changes; all executed Lean, policies, checker code and proof
data are unchanged. Additional report/evidence files were then created.

`stages/` contains exactly the logs from the successful stages.json, not unrelated
old output labels. Complete current/baseline/public TSVs are retained with gzip.
`full-record-compatibility-result.json` and `type-comparison-result.json` are
parsed copies of the actual successful command JSON, including raw failed
comparisons and explicit accepted-representation arrays. The raw difference is
not removed or relabelled as raw success. The former has 3947 records, zero
missing/added/relocated and one bound type difference; the latter separately
preserves the old 3902 and 45 additions results.

Local failed probes and regression-message failures remain under their original
labels. The first consumer preceded producer readiness and is not an API failure.
Public/raw-name assumptions were corrected after observing consumer-local private
equation realizations; the user-name controls are ordinary source code. No import
all consumer was used. OldAttrs/OldAPIControls and one old Basic source fixture
provide actual attribute and same-source rfl/rw/simp controls. No olean/ir/cache is
stored, and this is not a second maintained project.

`source-identity.json` establishes exactly three changed products and 258 unchanged
products, protected historical files, pins and clean Mathlib status. Old proof DAG
and live ordinary witness are maintained under experiments/kl-for-mathlib and are
hash-bound by the specific compatibility policy. SHA256.json binds retained
files except itself and this README.

No full build was repeated after acceptance. The final warm-build stage is the
inherited no-change regression, not another source rebuild. Timings are actual
integration costs, not controlled cold/warm speed comparisons. Child maximum RSS
is not summed concurrent usage; queue/lock job times must not be added. Token
telemetry is unavailable. GitHub CI is not asserted by these local results.
