# Signed-dihedral paired ranks

A local refactoring experiment based on pristine `../kl` at lean-lab commit
`dc7adaa35047517a600a2b80ff5aefcf28eb905a`. Only
`OAI/RepresentationTheory/KazhdanLusztig/DihedralIntervals.lean` differs from its
34 preserved source modules. Upstream provenance and licenses remain in the lab
root. The pinned Lean, manifest and Lake configuration are unchanged.

From the lab root, with the validated baseline toolchain/artifacts available:

```bash
bash experiments/kl-signed-ranks/check.sh
# Also measure pristine and changed direct elaboration sequentially:
bash experiments/kl-signed-ranks/check.sh --measure
```

The runner checks pristine baseline identity, pins, configuration and the single
changed-source allowlist. It refuses missing baseline/Mathlib artifacts before
building the experiment. Dependency checkouts are shared; OAI build artifacts
are copied/reflinked separately, never shared writable. Caches are ignored by Git.
No `lake update`, upstream lakefile, network setup or full Mathlib source fallback.
On a new worker, first restore the baseline intentionally using the root README;
this runner does not silently accept the cost of compiling the original baseline.

Validation includes boundary examples, downstream compilation, eight axiom
closures, every existing non-private, non-internal declaration type across the 34
imported KL modules, and a warm repeat. Compiler-generated internal `_proof_`/`_simp_` names are not public API, using
Lean's `Name.isInternal` classification. Type comparison ignores metadata annotations only;
it preserves binder names/information and universes, using exact constructor
interning rather than hash-only comparison. Run one Lean validation at a time.
Logs/metrics are written to timestamped `results/signed-ranks/` directories.

The shared pair API replaces endpoint recombination in exactly the base,
positive-upper and negative-upper count proofs. The literal `c=j` cases and
singleton-top summand remain unchanged. No global simp attributes or new tactic.
