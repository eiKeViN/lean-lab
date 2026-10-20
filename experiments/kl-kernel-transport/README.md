# Kernel transport under linear equivalences

**Status:** compilation, axiom and focused checks pass; strict API acceptance
remains blocked by module-dependent compiler-generated instance binder names.
The runner deliberately still exits 1; see the report for evidence and the
required comparison-contract decision.

An isolated responsibility/namespace migration from `../kl-signed-ranks` at
`7225842219ed3844b2fbd9cf3d95f9b65bec862c`. Pristine `../kl`, signed-ranks and
their validation scripts stay unchanged.

`OAI.LinearAlgebra.KernelTransport` contains the three original implementation
bodies under `OAI.LinearEquiv`. Their nearby Mathlib APIs live in
`Algebra/Module/Submodule/{Ker,Equiv}` and `Algebra/Module/Equiv/Basic`; the local
file path is our classification, not a claim to mirror Mathlib's directory tree.
`OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat` preserves the old
`OAI.KLInvariance` definitions with explicit original types. Bott imports that
compatibility entry. Source/mixed transport still have the same two Bott clients;
target transport still has no production client. No proof rewrite or new class.

From the lab root, with the signed-ranks reference artifacts already available:

```bash
bash experiments/kl-kernel-transport/check.sh
```

The runner first verifies frozen source/tooling and pinned dependencies, then
refuses missing Mathlib/reference artifacts before accepting compilation costs.
It shares dependency checkouts and copies/reflinks separate build artifacts.
Checks run sequentially: independent imports and definitional projections,
compatibility, Bott, inherited signed boundaries, full downstream build, sixteen
axiom closures, exact types/kinds and module owners, and a warm build.

`api-manifest.json` specifies all 34 reference modules, the two added modules,
3899 existing public declarations, three new definitions and three owner moves.
Private/internal compiler declarations remain excluded by Lean's own predicates;
their counts are reported per module. No missing old API or unlisted addition is
accepted. Results are written to ignored `results/kernel-transport/`.

This establishes API discoverability, an independent local import boundary and
compatibility. It does not claim proof shortening, a new mathematical abstraction
or a speedup. See `../../reports/kernel-transport-implementation.md` for measured
results and limits.
