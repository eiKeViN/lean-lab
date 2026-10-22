# Library candidate coverage — 2026-10-22

Baseline `a0b5b59457f593c86d3054b086da3b820585c282`. All 207 implementation
files (205 migration entries plus two fixed kernel files) have source hashes and
a mechanical inventory of named theorem/lemma/def/abbrev/structure headings.
This recognizer is not a full Lean parser or a complete instance/generated-declaration
list. Another 54 import-only compatibility/umbrella files are checked separately,
covering all 261 library product modules at the file level. This is **not** a line-by-line proof audit.
Targeted source reading covers the selected files and the explicitly retained
files below; all other files are deferred after declaration/region screening.

| Region | Files | Selected files | Targeted retained files |
| --- | ---: | ---: | ---: |
| ForMathlib.Algebra.Algebra.ReflectionFrobenius | 2 | 0 | 0 |
| ForMathlib.Algebra.BigOperators.SingleCoordinate | 1 | 0 | 0 |
| ForMathlib.Algebra.Module.CoefficientChange | 2 | 0 | 0 |
| ForMathlib.Algebra.Module.Cover | 1 | 0 | 0 |
| ForMathlib.Algebra.Module.Flat | 1 | 0 | 0 |
| ForMathlib.Algebra.Module.Free | 1 | 0 | 0 |
| ForMathlib.Algebra.Module.Graded | 29 | 4 | 0 |
| ForMathlib.Algebra.Module.Localization | 4 | 2 | 0 |
| ForMathlib.Algebra.Module.Projective | 5 | 0 | 0 |
| ForMathlib.Algebra.Module.Quotient | 2 | 0 | 0 |
| ForMathlib.Algebra.Module.ReflectionPair | 3 | 0 | 0 |
| ForMathlib.Algebra.Module.Submodule | 3 | 0 | 0 |
| ForMathlib.Algebra.Order.Field | 1 | 0 | 0 |
| ForMathlib.Algebra.Polynomial.LowPart | 1 | 0 | 1 |
| ForMathlib.Algebra.Polynomial.Reciprocal | 1 | 1 | 0 |
| ForMathlib.Algebra.Polynomial.ScaledEvaluation | 1 | 0 | 0 |
| ForMathlib.Algebra.Polynomial.TransferEvaluation | 1 | 0 | 0 |
| ForMathlib.Combinatorics.Dihedral.SignedCount | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.Basic | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.Monotone | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.PositiveTransfer | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.ScalarMap | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.SortedSchedule | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.Subpaths | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.Suffix | 1 | 0 | 0 |
| ForMathlib.Combinatorics.DirectedPaths.Transfer | 1 | 0 | 0 |
| ForMathlib.Combinatorics.MomentGraph.Boundary | 6 | 0 | 0 |
| ForMathlib.Combinatorics.MomentGraph.Bruhat | 3 | 0 | 0 |
| ForMathlib.Combinatorics.MomentGraph.GradedSheaf | 13 | 0 | 0 |
| ForMathlib.Combinatorics.MomentGraph.OrderedGraph | 1 | 0 | 0 |
| ForMathlib.Combinatorics.MomentGraph.Sheaf | 13 | 4 | 0 |
| ForMathlib.GroupTheory.Coxeter.Bruhat | 7 | 0 | 0 |
| ForMathlib.GroupTheory.Coxeter.Dihedral | 5 | 0 | 0 |
| ForMathlib.GroupTheory.Coxeter.Exchange | 1 | 0 | 0 |
| ForMathlib.GroupTheory.Coxeter.Parabolic | 3 | 0 | 0 |
| ForMathlib.GroupTheory.Coxeter.Realization | 5 | 0 | 0 |
| ForMathlib.GroupTheory.Coxeter.Roots | 12 | 0 | 0 |
| ForMathlib.LinearAlgebra.Avoidance | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.ConjugateRange | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.CoordinateProjection | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.Dual.Adjoint | 1 | 0 | 1 |
| ForMathlib.LinearAlgebra.Dual.BalancedCut | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.Dual.Frobenius | 1 | 0 | 1 |
| ForMathlib.LinearAlgebra.Dual.IntegralSupport | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.Dual.Summand | 1 | 0 | 1 |
| ForMathlib.LinearAlgebra.Dual.TransportPairing | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.KernelCoordinates | 1 | 0 | 1 |
| ForMathlib.LinearAlgebra.KernelTransport | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.PairProjection | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.PlaneReduction | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.Quotient.Transport | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.Reflection.Bilinear | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.Reflection.Classification | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.Reflection.Plane | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal | 1 | 0 | 0 |
| ForMathlib.LinearAlgebra.TensorProduct.Coordinates | 1 | 0 | 0 |
| ForMathlib.Order.Interval.Diamonds | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.BottSamelson.TitsWords | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.Hecke.Coefficients | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.Hecke.DualR | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.Hecke.DyerPaths | 4 | 0 | 0 |
| ForMathlib.RepresentationTheory.Hecke.Inverse | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.Hecke.Operators | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.Hecke.OrdinaryR | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.Hecke.PositiveWord | 1 | 0 | 0 |
| ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials | 10 | 0 | 0 |
| ForMathlib.RingTheory.Localization.RelativePrime | 1 | 0 | 0 |
| OAI.KL.BottSamelson | 9 | 0 | 0 |
| OAI.KL.Comparison | 3 | 0 | 0 |
| OAI.KL.Compatibility | 1 | 0 | 0 |
| OAI.KL.Invariance | 2 | 0 | 0 |
| OAI.KL.Localization | 5 | 0 | 1 |
| OAI.KL.Sheaves | 6 | 0 | 3 |

## Targeted decisions

Twenty-one old proofs in eleven files are selected for their mathematical roles,
not a lemma quota. The exact per-proof decisions are in `plan.json`.

Retained/deferred after direct proof reading:

- LowPart: the coefficient case analysis is one coherent anti-reciprocal argument; a pointwise restatement would mostly rename the entire proof.
- Reciprocal difference degree bounds: existing degree-map/subtraction inequalities plus arithmetic already express the step.
- Dual/Frobenius/adjoint/summand and kernel coordinates: many steps already have mathematical names; new tensor-induction abstractions would require wider API design.
- Application support/FreeModel/StalkReciprocity/localization edge: the inspected support-equivalence and graph-kernel arguments either already use named interfaces or need a focused representation/API decision. No application theorem is changed just to broaden the file list.

Coxeter/root-plane/dihedral and Hecke operator/word regions remain inventory-level
deferred candidates in this round. This does not classify specialized research
mathematics as non-reusable, nor certify that these proofs need no refactoring.
The basis/generator constructions are similarly deferred to a dedicated proof read.

`coverage.json` lists every file, source hash, declaration/line inventory, actual
screening level and disposition. `proof-structures.json` will retain the selected
before/after arguments; prior APIs and active source files remain frozen.

`entrypoints.json` records those import-only files. `coverage-baseline-check.json`
verifies all 261 file hashes against the starting Git commit. The original mechanical
inventory is consolidated into `coverage.json`, avoiding a duplicate maintained dump.

Follow-up: a focused cross-check of `Hilbert/Numerator.hasSum_shift_coeff` and
its `numerator_add_shift` use withdrew the proposed duplicate shift helper. The
file remains unchanged and two old clients reuse its existing API through one
explicit same-layer import. This extra focused check is separate from the 20
preselected targeted-read files; the baseline hashes and inventory are unchanged.
