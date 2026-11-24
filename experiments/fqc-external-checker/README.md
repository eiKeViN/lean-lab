# FQC external certificate checker

This experiment replaces the packed Stage 1/2 coverage computations and three
closed Cauchy predicates, an 8,192-input Boolean circuit check, two numerical
parameter families and selected closed decisions in Google's Photochemistry construction with explicitly
named external assumptions. The
external checker executes exact integer arithmetic as a native Lean program;
the geometric bridges, circuit construction and final correctness/cost proofs
retain their upstream Lean proofs.

Upstream: [`google-deepmind/formal-quantum-computation` at `a88de8f`](https://github.com/google-deepmind/formal-quantum-computation/tree/a88de8ff65d78af564b2373088ca369dc95f6547).
The implementation deliberately trusts the external checking/admission chain.
It does not describe native execution as a kernel proof.

There are two isolated Lean 4.35.0 workspaces:

| Workspace | Dependencies | Purpose |
|---|---|---|
| This directory | Lean/Init only | Native checker, original six-cell sample, kernel reference checks and 11 small correspondence lemmas |
| `integration/` | Exact upstream Mathlib/Physlib revisions and locked transitive dependencies | Original 107-module closure, materialized as 143 modules with admitted numerical interfaces and final theorem audits |

The isolated workspaces are necessary because the lightweight vendor slices and
full upstream modules declare the same original names. They must not be imported
together in one Lean environment.

## Run

Prerequisites: Linux/WSL2, Python 3.10+, Git, and the official Lean 4.35.0 toolchain
including its native compiler. An elan installation selects `lean-toolchain`;
a standalone installation can use
`export FQC_TOOLCHAIN_DIR=/absolute/path/to/lean-4.35.0-linux`.

```bash
cd experiments/fqc-external-checker
bash scripts/setup.sh
bash scripts/setup.sh full
bash scripts/check.sh full
```

Full setup verifies the committed dependency lock against upstream, installs
exact revisions, requests official Mathlib caches for the 112 required import
roots, and builds the relevant Physlib dependencies. It never executes the
preserved upstream FQC lakefile or updates dependency pins. No whole-Mathlib
source build is requested. A local upstream mirror can be selected with
`FQC_UPSTREAM_ROOT=/path/to/upstream`; all source hashes are still checked.

Full check reruns the original sample, all 1,656 native certificates, three original
Cauchy predicates, the borrow-wire check and both parameter families through external
`#eval`, 59 named decisions with fresh replay, representative Stage 2 kernel checks,
negative admission checks, source materialization, sequential
compilation and final type/axiom audits. Valid Lake build traces are reusable;
the native observations and audits are fresh. A fresh integration build is much
more expensive than the native certificate checks.

Individual steps are available for inspection and resumption:

```bash
bash scripts/check.sh full inventory
bash scripts/check.sh full coverage
python3 scripts/full_reference.py
bash scripts/check.sh full numeric
bash scripts/check.sh full materialize
bash scripts/check.sh full build
bash scripts/check.sh full audit
```

When using standalone Python commands, put the pinned toolchain's `bin` directory
on `PATH`. `bash scripts/setup.sh full --verify-only` checks installed revisions
without requesting caches/builds. The original small experiment remains available
through `bash scripts/check.sh`.

Generated sources, downloaded payloads, build products and runtime reports are
ignored. Their locations are `.cache/full/`, `integration/QuantumComputation*/`,
`.lake/` and `results/`. The committed source catalog is sufficient to reproduce
the full extracted payload from the pinned upstream snapshot.

## Full Photochemistry scope

| Coverage family | Original theorem groups / external axioms | Native batches | Cell occurrences |
|---|---:|---:|---:|
| Stage 1, two shards | 103 | 411 | 445 |
| Stage 2, four shards | 312 | 1,245 | 3,660 |
| Coverage total | **415** | **1,656** | **4,105** |

Three additional named assumptions assert the exact Boolean results of the
original `checkSegListAuto`, `checkTailAuto` and `checkHalfWalkUAuto` instances.
They support the finite, tail and lower-half-plane Cauchy bounds. Their original
predicate definitions and generic mathematical soundness proofs stay in Lean;
only the closed evaluations use the external runtime. The complete registry also includes one original 8,192-input borrow-wire check,
one 16-case pair batch, one 32-case ULP batch, and 59 individually named closed
decisions, for **480** registered external assumptions. The finite computations
are external; their relations to the gate semantics and analytic specifications
still follow from the upstream Lean proofs.

The named evaluator uses Lean's existing `nativeEqTrue` backend. Its temporary
native axiom is discarded; a successful evaluation creates one explicitly named
axiom asserting the exact original `decide P = true`, and the kernel checks the
ordinary derivation of `P`. Each entry records its original source position,
canonical elaborated proposition, decision expression and axiom type. Audit
reruns all decisions from exported Boolean definitions, checks their defining
equations, and compares the observed expressions against the committed goal
registry. False, open, unregistered and foreign-axiom goals are rejected. Two tiny
`fin_cases` sites remain kernel proofs, and comment text is never transformed.

Each original `c1_i`/`c2_i` conjunction is retained with the same declaration name
and proposition, proved from one corresponding named external axiom. Each axiom
is admitted only after every constituent batch accepts. The restricted parser
checks that the concatenated batch cells exactly match that conjunction's cells;
the catalog binds the complete input bytes, original blob identities and types.
Six data modules have coverage proofs replaced. `HalfPlaneCauchyWalkCore` is
split into 16 namespace partitions and `MidTap29Coul18Stage4K2` into seven, with
definitions modules and facades retaining their original import paths. The
Coulomb module has three section partitions, and the polynomial module five. Source
ranges, active scopes, one-time scoped instances and hashes are locked separately.
Four ULP shards use a shared batch assumption; five further modules use named
external decisions. **90 original modules remain byte-identical**. The original
107-module snapshot contains 26,440,485 bytes; the 143 generated modules contain
12,564,506 bytes, excluding the two hand-authored audit/evaluator helper modules.
The separate `top1D73_cov` theorem retains its original kernel proof.

The final program and both target theorem files are unchanged:

- `QuantumComputation.Specs.photochemistry_correctness`: the compiled circuit with
  clean ancillas realizes a single unitary approximating the specified discretized
  molecular Hamiltonian's time evolution, at time `1 fs`, with error `0.01` and
  success parameter `1`, for all input states and up to a global phase.
- `QuantumComputation.Specs.photochemistry_const_cost`: no primitive `TOFF` gates;
  `(systemQubits + photochemistryAncillas) * T-count ≤ photochemistryConstCost`.
  The original definitions use 5,616 system qubits, 417 ancillas and cost bound
  605,980,010,227,389.

Other exact arithmetic and all generic semantic/analytic reasoning retain the
original proofs. The original closure has 2,347 lexical `decide +kernel`
occurrences; 580 remain after the selected replacements. These are lexical
counts, including comments, rather than a count of elaborated proof obligations.

## Components

| Path | Responsibility |
|---|---|
| `FQCExternal/Vendor/` | Source-verified upstream logic slices without the large coverage payload |
| `FQCExternal/Entry.lean` | Kernel-checked single-word correspondence/soundness |
| `FQCExternal/Exec.lean`, `Exec2.lean` | Native Stage 1/2 dictionary, stream and geometric predicate checking |
| `Main.lean` | Strict JSON schemas, multi-file CLI, claim echo and exit status |
| `data/c1_0/` | Original four-batch, six-cell sample; 53,041 bytes |
| `FQCExternal/ExternalFacts.lean`, `Claim.lean` | Sample's four explicit assumptions and unchanged source-derived proposition |
| `provenance/upstream.json` | Small sample source/fixture/type lock |
| `provenance/photochemistry.json` | 107-module source lock; 415 exact propositions; 1,656 input identities |
| `provenance/photochemistry-spec.json` | Isolated original specification source identity |
| `provenance/photochemistry-shards.json` | Exact source ranges and active scopes of the 16 kernel-preserving namespace shards |
| `provenance/photochemistry-midtap-shards.json` | Seven original namespace ranges, scope reconstruction and one-time scoped instance declarations |
| `provenance/photochemistry-coulomb-shards.json`, `photochemistry-poly-shards.json` | Further original section ranges, restored scopes and single instance declarations |
| `provenance/photochemistry-midtap.json` | Exact 8,192-input preservation predicate and its parent semantic theorem |
| `provenance/photochemistry-cauchy.json` | Three exact scalar predicates, parent theorems and explicitly named Boolean assumptions |
| `provenance/photochemistry-families.json` | Exact 16-case pair and 32-case ULP predicates and source identities |
| `provenance/photochemistry-oracle-sites.json` | Closed decision source positions and retained finite-case exclusions |
| `provenance/photochemistry-oracle-goals.json` | Frozen elaborated propositions, decision/axiom expressions and dependencies |
| `integration/FQCOracle/Tactic.lean` | Named external evaluation, dependency rejection and fresh replay |
| `provenance/photochemistry-types.json` | Retained canonical elaborated public-type export, after successful audit |
| `scripts/full*.py` | Exact dependency setup, extraction, admission, integration and independent type/axiom checks |
| `integration/Audit/Export.lean` | Public type serialization without binder names or source metadata |
| `STATUS.md` | Work packages and validation checkpoint |

CLI status codes: 0 accepted, 1 rejected certificate, 2 malformed input/schema/IO
error. Mathematical tests use exact natural/signed-integer arithmetic, not
floating-point sampling. Python orchestrates and binds claims; it does not perform
the geometric arithmetic tests.

## Verification and trust

The complete check passed on 2026-11-24: both original final theorems compile,
all five public types match the reference export, and both theorem dependencies
are exactly the standard three plus the 480 registered external assumptions.
No external entry is unused. The separate checks and measured checkpoint are
recorded in [STATUS.md](STATUS.md).
`results/full/all-status.json` is published as `passed` only after the complete
check. Individual coverage, build, reference and axiom reports remain separate.
A failure or pending build is not final theorem acceptance.

The sample's public theorem depends on its four explicit external axioms and
`propext`. Eleven small bridge lemmas use only standard axioms. Fresh kernel
references accept original `c1_0` and `c2_0`; four corrupted certificate variants
per stage are rejected by both the native and kernel routes. Additional admission
checks reject changed catalog/checker/admission/binary identities, missing results
and duplicate admissions.

| External boundary | Retained kernel work | New assumptions |
|---|---|---:|
| Ported Stage 1/2 decoder and native execution | Small arithmetic correspondences; geometric and circuit proofs | 415 coverage propositions |
| Original Cauchy predicates executed by Lean `#eval` | Original predicate definitions and generic analytic soundness proofs | 3 Boolean equalities |
| Original borrow-wire simulation executed by Lean `#eval` | Original gate semantics and finite-enumeration soundness bridge | 1 Boolean equality |
| Original 16-case pair and 32-case ULP families via `#eval` | Original predicates and index-to-batch soundness | 2 batch equalities |
| Selected original closed decisions via `nativeEqTrue` | Original propositions and all downstream uses | 59 named `decide P = true` equalities |

The **whole executable coverage decoder's equivalence and soundness are not proved**.
The decoder implementation, compiler/runtime, JSON parsing, source extraction
and Python admission are explicitly trusted. Hashes establish identity, not
mathematical correctness. Coverage acceptance produces named axioms with
provenance rather than an implicit proof escape. Generated source verification
checks the exact approved transformation, not just a mutable output hash list.

The final type audit elaborates the original specification and derived solution
in separate Lean processes and compares their canonical `Expr` types for the
three public definitions and both final theorems. The Photochemistry specification's
candidate placeholders are used only in that isolated type export, never imported
by the solution. The imported StoppingPower specification also has unused
placeholders; none may contribute a reachable `sorryAx` to the audited declarations.
The solution audit rejects `sorryAx`, native-reduction axioms and
any assumption outside the standard three plus the 480 registered external
axioms. Definition bodies and final proof source are checked independently by
source identity.

Upstream Comparator is **not run**: its original three-axiom whitelist rejects
this deliberately extended trust boundary. A public-type comparison plus a Lean
axiom audit is not represented as an independent Comparator run. No claim is made
about reproducing or reducing the original project's reported 230 GB Comparator
peak.

## Measurements

Runtime reports keep native execution separate from build, source admission,
kernel reference elaboration and final audits. Native acceptance and kernel
reference proof have different trust boundaries and are not an equal-trust
speed comparison. Linux `wait4` max-RSS may include inherited pre-exec memory;
it is not aggregate concurrent RAM.

The initial sample checkpoint on 2026-11-24 recorded 0.24 s for four native checks,
19.14 s for its fresh original kernel proof, and 1.84 s for kernel rejection of
four corrupted inputs. Full native checkpoints recorded 26–33 s across 1,656
batches, excluding checker compilation, source parsing and downstream builds.
These observations are descriptive; normal checks generate fresh runtime reports.

For disk-constrained machines the large dependency build caches may live on a
separate volume using ordinary filesystem links. A RAM-backed cache consumes
available RAM; it is not excluded from the machine's memory budget.

The unsharded `HalfPlaneCauchyWalkCore` compilation was terminated with exit 137
on this 9.7 GiB machine. A diagnostic run without C output also
exceeded Lean's `-M4800` limit in the interpreter. The integration therefore uses
the source-preserving namespace shards, sequential compilation and one Lean
thread by default. A later shard isolated another failure at a closed Cauchy
predicate; the three related evaluations now use the unchanged original code via
external `#eval`. One checkpoint took 5.79 s including imports, the three predicates
and rejection of a zero-length segment. These evaluations are explicitly trusted.
The attempted `LEAN_NUM_THREADS` environment setting did not limit this version's
worker pool; explicit `-j1` is required. The integration now uses
`weakLeanArgs = ["-M4800", "-j1"]` to bound later Lean jobs without
changing dependency pins or invalidating already valid compilation traces.
The unpartitioned MidTap module also exceeded 4.8 GB with explicit `-j1`;
raising its budget to 6 GB led to exit 137 on this machine. Its seven namespace
shards retain the original proofs except the closed 8,192-input Boolean check
and 16 pair evaluations,
which also exceeded the smaller budget on its own. Its original runtime check
and a flipped-output negative probe took 8.05 s in one checkpoint; the generic
semantic proof remains in Lean.
These per-command observations do not establish an aggregate end-to-end RAM
peak or a Comparator result.

The 7,423-line Coulomb module also reached exit 137 after all 15 of its external
decisions accepted. It now uses its three original section boundaries. The
5,796-line polynomial module uses five original boundaries to keep later proof
units bounded. These partitions change file organization, not mathematical bodies.
