# Current-content upstream assessment

All 193 prior semantic modules are indexed below; the generic kernel module is
also staged, while its three-name compatibility wrapper remains project-owned.
These are current dependency-compatible candidates, not accepted or PR-ready
Mathlib additions. Mathematical suitability and present integration are separate.
No future interface extraction is performed. See README and the report for the
official criteria, limitations and family-level reasoning.

Original source references are in frozen `../kl-architecture`; declaration names
and line references are evidence for inspecting the actual statements, not a
claim that the first three names exhaust each module. Full spans: MIGRATION.md.

| Prior semantic module | New home | Current category | Declaration evidence (prior line) |
| --- | --- | --- | --- |
| `OAI.Algebra.Algebra.ReflectionFrobenius.Basic` | `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic` | current_candidate | `fixed`:16, `fixed_val`:24, `expand`:28 |
| `OAI.Algebra.Algebra.ReflectionFrobenius.Basis` | `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis` | current_candidate | `wallCoordinate`:18, `wallMatrix`:22, `wallMatrix_mulVec`:27 |
| `OAI.Algebra.BigOperators.FiniteCharacterCancellation` | `ForMathlib.Algebra.BigOperators.FiniteCharacterCancellation` | current_candidate | `finite_character_cancellation`:13 |
| `OAI.Algebra.Module.CoefficientChange.Basic` | `ForMathlib.Algebra.Module.CoefficientChange.Basic` | current_candidate | `equivVal`:21, `equiv`:42, `kEquiv`:52 |
| `OAI.Algebra.Module.CoefficientChange.Dual` | `ForMathlib.Algebra.Module.CoefficientChange.Dual` | current_candidate | `mapEquiv`:19, `dualTo`:26, `dualFrom`:35 |
| `OAI.Algebra.Module.Cover.Local` | `ForMathlib.Algebra.Module.Cover.Local` | current_candidate | `lift_surjective`:17, `splitEquiv`:36, `exists_split_minimal_cover`:58 |
| `OAI.Algebra.Module.Cover.Product` | `ForMathlib.Algebra.Module.Cover.Product` | current_candidate | `pi_mem_ideal_smul`:15 |
| `OAI.Algebra.Module.Flat.Kernel` | `ForMathlib.Algebra.Module.Flat.Kernel` | current_candidate | `baseChange_ker`:16, `baseChange_map`:21 |
| `OAI.Algebra.Module.Free.ScalarDivisibility` | `ForMathlib.Algebra.Module.Free.ScalarDivisibility` | current_candidate | `exists_smul_iff`:16, `exists_prod_smul`:30, `scalar_quotient_regular`:42 |
| `OAI.Algebra.Module.Graded.Adjoint` | `ForMathlib.Algebra.Module.Graded.Adjoint` | current_candidate | `perfect_inverse_of_homogeneous_functional`:21, `adjoint_homogeneous`:74 |
| `OAI.Algebra.Module.Graded.AlgebraMap` | `ForMathlib.Algebra.Module.Graded.AlgebraMap` | current_candidate | `basisPiece`:20, `mem_basisPiece`:24, `basis_mem_piece`:53 |
| `OAI.Algebra.Module.Graded.Components` | `ForMathlib.Algebra.Module.Graded.Components` | current_candidate | `component`:14, `positiveIdeal`:20, `subsingleton_of_positiveIdeal_smul_eq_top`:27 |
| `OAI.Algebra.Module.Graded.DualAndShift` | `ForMathlib.Algebra.Module.Graded.DualAndShift` | current_candidate | `equiv_inverse_homogeneous`:22, `pairing_to_dual_homogeneous`:42, `perfectPairing_inverse_homogeneous`:54 |
| `OAI.Algebra.Module.Graded.Generators` | `ForMathlib.Algebra.Module.Graded.Generators` | current_candidate | `internal_of_components`:16, `image_isInternal`:40, `subPiece`:78 |
| `OAI.Algebra.Module.Graded.Hilbert.Basic` | `ForMathlib.Algebra.Module.Graded.Hilbert.Basic` | current_candidate | `piece`:15, `term`:18, `value`:21 |
| `OAI.Algebra.Module.Graded.Hilbert.Images` | `ForMathlib.Algebra.Module.Graded.Hilbert.Images` | current_candidate | `scalarDegreeMap`:19, `scalarDegreeMap_surjective`:27, `scalarDegreeMap_injective`:41 |
| `OAI.Algebra.Module.Graded.Hilbert.Increment` | `ForMathlib.Algebra.Module.Graded.Hilbert.Increment` | current_candidate | `shifted_map_homogeneous`:18, `shiftedImagePieceMap`:29, `shiftedImagePieceMap_surjective`:40 |
| `OAI.Algebra.Module.Graded.Hilbert.RationalFunction` | `ForMathlib.Algebra.Module.Graded.Hilbert.RationalFunction` | current_candidate | `hasSum_shift_coeff`:12, `numerator_unique`:22, `numerator_add_shift`:36 |
| `OAI.Algebra.Module.Graded.Hilbert.Series` | `ForMathlib.Algebra.Module.Graded.Hilbert.Series` | current_candidate | `hasSum_monomials`:14, `intWeight_eq_natWeight`:38, `polynomialGrading_nat`:43 |
| `OAI.Algebra.Module.Graded.HomogeneousDual` | `ForMathlib.Algebra.Module.Graded.HomogeneousDual` | current_candidate | `mem_of_homogeneous_smul`:19, `homogeneous_basis_repr`:48, `dualBasis_homogeneous`:63 |
| `OAI.Algebra.Module.Graded.ModuleData.Basic` | `ForMathlib.Algebra.Module.Graded.ModuleData.Basic` | current_candidate | `ModuleData`:16, `Hom`:38, `sub`:42 |
| `OAI.Algebra.Module.Graded.ModuleData.Character` | `ForMathlib.Algebra.Module.Graded.ModuleData.Character` | current_candidate | `mapNonnegativeBasis`:17, `character_eq_of_gradedEquiv`:26, `char`:47 |
| `OAI.Algebra.Module.Graded.ModuleData.CharacterDual` | `ForMathlib.Algebra.Module.Graded.ModuleData.CharacterDual` | current_candidate | `unitPolynomialBasis`:16, `char_unit`:29, `char_natDegree_le_of_dual_equiv`:48 |
| `OAI.Algebra.Module.Graded.ModuleData.CoefficientChange` | `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange` | current_candidate | `unchangeHom`:18, `changeUnitHom`:48, `changeUnitInvHom`:60 |
| `OAI.Algebra.Module.Graded.ModuleData.CoverUniqueness` | `ForMathlib.Algebra.Module.Graded.ModuleData.CoverUniqueness` | current_candidate | `MinimalCover.hom_bijective`:20 |
| `OAI.Algebra.Module.Graded.ModuleData.Duality` | `ForMathlib.Algebra.Module.Graded.ModuleData.Duality` | current_candidate | `equivOfEq_inverse`:18, `homOfEq`:23, `unit_endomorphisms_commute`:38 |
| `OAI.Algebra.Module.Graded.ModuleData.Equality` | `ForMathlib.Algebra.Module.Graded.ModuleData.Equality` | current_candidate | `Hom.ofEq`:15, `Hom.ofEq_apply`:19, `Hom.ofEq_bijective`:33 |
| `OAI.Algebra.Module.Graded.ModuleData.MinimalCover` | `ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover` | current_candidate | `idempotent_eq_zero`:17, `MinimalCover.bijective_of_boundaryIso`:51, `inverse`:94 |
| `OAI.Algebra.Module.Graded.ModuleData.QuotientHom` | `ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom` | current_candidate | `quotientHom`:17, `quotientHom_apply`:27 |
| `OAI.Algebra.Module.Graded.ModuleData.Range` | `ForMathlib.Algebra.Module.Graded.ModuleData.Range` | current_candidate | `rangeMap`:18, `rangeInclusion`:25, `rangeProjection`:29 |
| `OAI.Algebra.Module.Graded.ModuleData.Transport` | `ForMathlib.Algebra.Module.Graded.ModuleData.Transport` | current_candidate | `zero`:16, `Hom.zero`:31, `Hom.pi`:34 |
| `OAI.Algebra.Module.Graded.NonnegativeBasis` | `ForMathlib.Algebra.Module.Graded.NonnegativeBasis` | current_candidate | `polynomial_scalar_mod_positive`:14, `basis_coordinates_graded`:42, `NonnegativeBasis`:79 |
| `OAI.Algebra.Module.Graded.RegularScalar` | `ForMathlib.Algebra.Module.Graded.RegularScalar` | current_candidate | `homogeneous_positive_nonzero`:18, `dual_mem_ideal`:35, `local_diagonal_strict_degree`:52 |
| `OAI.Algebra.Module.Localization.FiniteCharacters` | `ForMathlib.Algebra.Module.Localization.FiniteCharacters` | current_candidate | `diagonal`:15, `stabilizer`:20, `diagonal_mem`:45 |
| `OAI.Algebra.Module.Localization.Lattice` | `ForMathlib.Algebra.Module.Localization.Lattice` | current_candidate | `mem_of_prime_local_membership`:42, `exists_denominator_of_localized_mem`:86, `mem_iff_localized_at_height_one`:103 |
| `OAI.Algebra.Module.Localization.Membership` | `ForMathlib.Algebra.Module.Localization.Membership` | current_candidate | `baseChange_eq_localized`:17, `denominator`:22 |
| `OAI.Algebra.Module.Localization.Products` | `ForMathlib.Algebra.Module.Localization.Products` | current_candidate | `smul_top_le_of_map_dvd`:15, `smul_top_eq_of_map_associated`:25, `associated_prod_power`:32 |
| `OAI.Algebra.Module.Localization.ProjectiveLattice` | `ForMathlib.Algebra.Module.Localization.ProjectiveLattice` | current_candidate | `finsupp_divide`:13, `prime_divide_of_relation`:29, `mem_of_prime_local_membership`:47 |
| `OAI.Algebra.Module.Projective.Range` | `ForMathlib.Algebra.Module.Projective.Range` | current_candidate | `descend`:17, `descend_apply`:21, `projective_of_end`:27 |
| `OAI.Algebra.Module.Projective.ReverseFiltration` | `ForMathlib.Algebra.Module.Projective.ReverseFiltration` | current_candidate | `kernel_projective_of_presentation`:17 |
| `OAI.Algebra.Module.Projective.ScalarKernel` | `ForMathlib.Algebra.Module.Projective.ScalarKernel` | current_candidate | `scalarKernelEquiv`:20, `projective_kernel_of_scalar_presentation`:36, `imageMapKernelEquiv`:47 |
| `OAI.Algebra.Module.Projective.ScalarQuotient` | `ForMathlib.Algebra.Module.Projective.ScalarQuotient` | current_candidate | `scalarQuotientMap`:15, `scalarQuotientMap_surjective`:22, `scalarKernelMap`:31 |
| `OAI.Algebra.Module.Projective.Transport` | `ForMathlib.Algebra.Module.Projective.Transport` | current_candidate | `projective_of_same_range`:17, `projective`:26 |
| `OAI.Algebra.Module.Quotient.EdgeEquiv` | `ForMathlib.LinearAlgebra.Quotient.Transport` | current_candidate | `iso`:15, `map_kernel_scalar`:27, `exists_scalar_iso`:42 |
| `OAI.Algebra.Module.Quotient.EdgeHom` | `ForMathlib.LinearAlgebra.Quotient.Transport` | current_candidate | `descend`:15, `descend_apply`:20, `kernel_scalar_le`:26 |
| `OAI.Algebra.Module.Quotient.EdgeImage` | `ForMathlib.Algebra.Module.Quotient.KernelReduction` | current_candidate | `kernel_saturated`:17, `reduced_kernel_injective`:30, `reducedInclusion`:49 |
| `OAI.Algebra.Module.Quotient.ScalarImage` | `ForMathlib.Algebra.Module.Quotient.ScalarImage` | current_candidate | `coordinateReduction`:20, `coordinateReduction_surjective`:25, `coordinateReduction_kernel`:33 |
| `OAI.Algebra.Module.ReflectionPair.TensorDescent` | `ForMathlib.Algebra.Module.ReflectionPair.TensorDescent` | current_candidate | `tensorFirst_map`:18, `tensorSecond_map`:26, `tensor_difference`:50 |
| `OAI.Algebra.Module.ReflectionPair.TensorKernel` | `ForMathlib.Algebra.Module.ReflectionPair.TensorKernel` | current_candidate | `scalarEquiv`:26, `tensorFirst`:47, `tensorSecond`:54 |
| `OAI.Algebra.Module.ReflectionPair.Twist` | `ForMathlib.Algebra.Module.ReflectionPair.Twist` | current_candidate | `equivVal`:25, `equiv`:35, `lattice`:58 |
| `OAI.Algebra.Module.Submodule.ScaledImage` | `ForMathlib.Algebra.Module.Submodule.ScaledImage` | current_candidate | `scaled`:13, `map_scaled`:16, `map_eq_scaled_iff`:24 |
| `OAI.Combinatorics.Dihedral.SignedCount` | `ForMathlib.Combinatorics.Dihedral.SignedCount` | current_candidate | `Before`:13, `before_same_source_pos`:16, `before_same_source_neg`:28 |
| `OAI.Combinatorics.DirectedPaths.Basic` | `ForMathlib.Combinatorics.DirectedPaths.Basic` | current_candidate | `IsPath`:16, `pathTerm`:21, `step`:27 |
| `OAI.Combinatorics.DirectedPaths.Monotone` | `ForMathlib.Combinatorics.DirectedPaths.Monotone` | current_candidate | `mem_suffix_iff_score_lt`:14, `mem_suffix_iff_score_lt_injective`:30, `step_monotone`:52 |
| `OAI.Combinatorics.DirectedPaths.PositiveTransfer` | `ForMathlib.Combinatorics.DirectedPaths.PositiveTransfer` | current_candidate | `transfer`:18, `transfer_monotone`:21, `transfer_injective`:29 |
| `OAI.Combinatorics.DirectedPaths.ScalarMap` | `ForMathlib.Combinatorics.DirectedPaths.ScalarMap` | current_candidate | `dispatch_map`:17 |
| `OAI.Combinatorics.DirectedPaths.SortedSchedule` | `ForMathlib.Combinatorics.DirectedPaths.SortedSchedule` | current_candidate | `sortedSchedule`:17, `sortedSchedule_nodup`:23, `sortedSchedule_pairwise`:27 |
| `OAI.Combinatorics.DirectedPaths.Subpaths` | `ForMathlib.Combinatorics.DirectedPaths.Subpaths` | current_candidate | `IsPath.map`:14, `IsPath.isChain`:25, `IsPath.pairwise_map_of_local`:39 |
| `OAI.Combinatorics.DirectedPaths.Suffix` | `ForMathlib.Combinatorics.DirectedPaths.Suffix` | current_candidate | `exists_suffix_score_gt`:13 |
| `OAI.Combinatorics.DirectedPaths.Transfer` | `ForMathlib.Combinatorics.DirectedPaths.Transfer` | current_candidate | `dispatch_append`:18, `dispatch_add`:25, `dispatch_mul_right`:36 |
| `OAI.Combinatorics.MomentGraph.Boundary.Basic` | `ForMathlib.Combinatorics.MomentGraph.Boundary.Basic` | current_candidate | `BoundarySheaf`:19, `singletonSheaf`:31, `singleton_boundarySheaf`:37 |
| `OAI.Combinatorics.MomentGraph.Boundary.Extension` | `ForMathlib.Combinatorics.MomentGraph.Boundary.Extension` | current_candidate | `extend_iso`:24, `exists_gradedIso`:47 |
| `OAI.Combinatorics.MomentGraph.Boundary.Hom` | `ForMathlib.Combinatorics.MomentGraph.Boundary.Hom` | current_candidate | `idempotent_zero_of_top_zero`:19, `idempotent_trivial`:56, `endomorphism_bijective_of_top`:103 |
| `OAI.Combinatorics.MomentGraph.Boundary.Models` | `ForMathlib.Combinatorics.MomentGraph.Boundary.Models` | current_candidate | `top_nontrivial`:21, `iso_of_primitive_top_split`:31, `iso_coefficientChange`:66 |
| `OAI.Combinatorics.MomentGraph.Boundary.Summand` | `ForMathlib.Combinatorics.MomentGraph.Boundary.Summand` | current_candidate | `primitive_identity`:20, `split_projector_primitive`:42 |
| `OAI.Combinatorics.MomentGraph.Boundary.Uniqueness` | `ForMathlib.Combinatorics.MomentGraph.Boundary.Uniqueness` | current_candidate | `hom_vertex_bijective`:25, `homIso`:49, `hom_vertex_bijective_of_iso`:75 |
| `OAI.Combinatorics.MomentGraph.Bruhat.Basic` | `ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic` | current_candidate | `Edge`:19, `source`:26, `target`:27 |
| `OAI.Combinatorics.MomentGraph.Bruhat.DihedralModel` | `ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel` | current_candidate | `reflection_of_parity`:25, `oppositeExternal`:32, `sameExternal`:36 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Basic` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Basic` | current_candidate | `GradedSheaf`:18, `forget`:27, `EdgeFlabby`:35 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Character` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character` | current_candidate | `freeStalkChar`:18, `ModelSum.character`:23, `exists_stalkCharacter_decomposition`:69 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Duality` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality` | current_candidate | `dualToSupport_homogeneous`:32, `UpperQuotient.annihilates`:59, `upwardSubmodule_saturated`:77 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Extension` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension` | current_candidate | `lowerAt`:21, `lowerAt_map`:26, `upwardSubmodule`:32 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Hilbert` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hilbert` | current_candidate | `kernelHilbert`:19, `lowerImage`:22, `upperImage`:26 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Hom` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom` | current_candidate | `Endomorphism`:18, `complement`:29, `complement_idempotent`:45 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Models` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models` | current_candidate | `kernelData`:23, `kernelProdEquiv`:26, `kernelProdEquiv_graded`:37 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Summand` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand` | current_candidate | `Hom.eq_of_maps`:18, `Hom.eq_of_vertex`:31, `Hom.zero`:51 |
| `OAI.Combinatorics.MomentGraph.GradedSheaf.Uniqueness` | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness` | current_candidate | `Hom.edge_bijective_of_vertex`:18, `Hom.isoOfBijective`:36, `Hom.aboveIso`:46 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Basic` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic` | current_candidate | `OrderedGraph`:13, `Sheaf`:20, `Assignment`:29 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Duality` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality` | current_candidate | `scaled_single_section`:19, `labelProduct`:27, `labelProduct_ne_zero`:29 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Extension` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Extension` | current_candidate | `baseChange`:17, `tensorAssignments`:23, `baseChange_tmul_compatible`:29 |
| `OAI.Combinatorics.MomentGraph.Sheaf.FlowDown` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown` | current_candidate | `modelOutgoing`:18, `modelProduct`:27, `HasFlowDown`:29 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Hom` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Hom` | current_candidate | `split_stalk_graded`:24 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Isomorphism` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Isomorphism` | current_candidate | `Iso`:18, `symm`:28, `assignments`:38 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Localization` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Localization` | current_candidate | `edge_subsingleton_of_unit`:16, `supportedOutgoing`:41, `kernelProduct`:45 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Models` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Models` | current_candidate | `LocalModels`:22, `ModelSum`:34, `mono`:45 |
| `OAI.Combinatorics.MomentGraph.Sheaf.ScaledImages` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages` | current_candidate | `outgoingLabelProduct`:21, `outgoingLabelProduct_dvd`:24, `outgoingLabelProduct_smul_mem`:28 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Uniqueness` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Uniqueness` | current_candidate | `stalk_hom_bijective`:24 |
| `OAI.Combinatorics.MomentGraph.Sheaf.Zero` | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Zero` | current_candidate | `zero`:15, `prod`:21, `prod_generated`:27 |
| `OAI.Data.Polynomial.Avoidance` | `ForMathlib.LinearAlgebra.Avoidance` | current_candidate | `coordinatePolynomial`:15, `coordinatePolynomial_coeff`:18, `coordinatePolynomial_injective`:30 |
| `OAI.Data.Polynomial.LowPart` | `ForMathlib.Algebra.Polynomial.LowPart` | current_candidate | `lowPart`:11, `lowPart_degree`:22, `lowPart_solution`:31 |
| `OAI.Data.Polynomial.ReciprocalRigidity` | `ForMathlib.Algebra.Polynomial.Reciprocal` | current_candidate | `low_degree_reflect_eq_self`:13, `low_degree_zero_of_eval_reciprocal`:29, `eq_of_eval_difference_reciprocal`:55 |
| `OAI.Data.Polynomial.ReflectEvaluation` | `ForMathlib.Algebra.Polynomial.Reciprocal` | current_candidate | `eval₂_reflect_unit`:11 |
| `OAI.Data.Polynomial.ScaledComparison` | `ForMathlib.Algebra.Polynomial.TransferEvaluation`, `ForMathlib.Algebra.Order.Field.RealScaling`, `ForMathlib.Algebra.Polynomial.ScaledReciprocity` | current_candidate | `polynomial_eq_of_transfer_eval_eq`:12, `edge_scalar_identity`:33, `transferCoefficient_pos`:48 |
| `OAI.GroupTheory.Coxeter.Bruhat.Basic` | `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic` | current_candidate | `bruhat_refl`:19, `bruhat_trans`:22, `length_le_of_bruhat`:26 |
| `OAI.GroupTheory.Coxeter.Bruhat.Defs` | `ForMathlib.GroupTheory.Coxeter.Bruhat.Defs` | current_candidate | `BruhatStep`:12, `BruhatLE`:16, `Interval`:20 |
| `OAI.GroupTheory.Coxeter.Bruhat.Descent` | `ForMathlib.GroupTheory.Coxeter.Bruhat.Descent` | current_candidate | `simple_mul_bruhat_of_descent`:16, `lower_parity_balance`:25, `externalLower`:48 |
| `OAI.GroupTheory.Coxeter.Bruhat.DiamondClosure` | `ForMathlib.GroupTheory.Coxeter.Bruhat.DiamondClosure` | current_candidate | `bruhatStep_of_interval_covBy`:12, `diamondEdges_bruhatStep`:28 |
| `OAI.GroupTheory.Coxeter.Bruhat.Diamonds` | `ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds` | current_candidate | `diamondEdges_of_bruhatStep`:16, `intervalIso_bruhatStep_iff`:75, `diamondEdges_of_bruhatStep_general`:99 |
| `OAI.GroupTheory.Coxeter.Bruhat.LowerFinset` | `ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset` | current_candidate | `lowerFinset`:21 |
| `OAI.GroupTheory.Coxeter.Bruhat.Transport` | `ForMathlib.GroupTheory.Coxeter.Bruhat.Transport` | current_candidate | `intervalIso_restrict`:18 |
| `OAI.GroupTheory.Coxeter.Dihedral.Diamonds` | `ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds` | current_candidate | `alt_add_two`:15, `alt_odd_sandwich`:19, `odd_alt_reflection`:29 |
| `OAI.GroupTheory.Coxeter.Dihedral.IntervalTransport` | `ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport` | current_candidate | `rank_two_of_two_step_bound`:16, `swapHom`:58, `swap`:83 |
| `OAI.GroupTheory.Coxeter.Dihedral.PlaneSystem` | `ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem` | current_candidate | `pairMatrix`:16, `wordProd_alt_even`:33, `injective_of_simple_order`:45 |
| `OAI.GroupTheory.Coxeter.Dihedral.SignedWords` | `ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords` | current_candidate | `wordProd_alt_odd`:17, `rotation`:26, `simple_rotation`:28 |
| `OAI.GroupTheory.Coxeter.Dihedral.Words` | `ForMathlib.GroupTheory.Coxeter.Dihedral.Words` | current_candidate | `alt`:16, `reduced_cons_cons_ne`:35, `reduced_cons_eq_alt`:43 |
| `OAI.GroupTheory.Coxeter.Exchange` | `ForMathlib.GroupTheory.Coxeter.Exchange` | current_candidate | `simpleAction`:19, `wordAction`:47, `wordAction_concat`:52 |
| `OAI.GroupTheory.Coxeter.Parabolic.InversionList` | `ForMathlib.GroupTheory.Coxeter.Parabolic.InversionList` | current_candidate | `leftInvSeq_inclusion`:17, `reflection_inclusion`:32, `bruhatStep_inclusion_iff`:38 |
| `OAI.GroupTheory.Coxeter.Parabolic.Standard` | `ForMathlib.GroupTheory.Coxeter.Parabolic.Standard` | current_candidate | `matrix`:17, `system`:23, `inclusion`:26 |
| `OAI.GroupTheory.Coxeter.Parabolic.Support` | `ForMathlib.GroupTheory.Coxeter.Parabolic.Support` | current_candidate | `reduced_of_append`:16, `reduced_pair_eq_alternating`:21, `alternating_length_bound`:47 |
| `OAI.GroupTheory.Coxeter.Realization.Cotangent` | `ForMathlib.GroupTheory.Coxeter.Realization.Cotangent` | current_candidate | `root`:16, `normal_root`:18, `simple`:21 |
| `OAI.GroupTheory.Coxeter.Realization.Faithful` | `ForMathlib.GroupTheory.Coxeter.Realization.Faithful` | current_candidate | `extendedAction_injective`:18, `involution_of_moving_rank_one`:37, `isReflection_of_moving_rank_one`:57 |
| `OAI.GroupTheory.Coxeter.Realization.Geometric` | `ForMathlib.GroupTheory.Coxeter.Realization.Geometric` | current_candidate | `simple_normal_value`:21, `geometricSimple`:25, `geometricSimple_liftable`:28 |
| `OAI.GroupTheory.Coxeter.Realization.Positivity` | `ForMathlib.GroupTheory.Coxeter.Realization.Positivity` | current_candidate | `rootCoeff`:18, `rootCoeff_succ`:31, `alternating_root`:43 |
| `OAI.GroupTheory.Coxeter.Realization.Tits` | `ForMathlib.GroupTheory.Coxeter.Realization.Tits` | current_candidate | `gram`:17, `root`:19, `normal`:23 |
| `OAI.GroupTheory.Coxeter.Roots.Basic` | `ForMathlib.GroupTheory.Coxeter.Roots.Basic` | current_candidate | `IsRoot`:19, `Represents`:22, `embed`:25 |
| `OAI.GroupTheory.Coxeter.Roots.DihedralOrder` | `ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder` | current_candidate | `prefixRoot`:19, `negPrefixRoot`:22, `prefixRoot_strictMono`:25 |
| `OAI.GroupTheory.Coxeter.Roots.LaterCount` | `ForMathlib.GroupTheory.Coxeter.Roots.LaterCount` | current_candidate | `edgeRoot_same_table`:20, `edgeRoot_next_table`:39, `afterIndicator`:58 |
| `OAI.GroupTheory.Coxeter.Roots.Order` | `ForMathlib.GroupTheory.Coxeter.Roots.Order` | current_candidate | `height`:18, `PositiveRoot.height_pos`:25, `normalizedRoot`:35 |
| `OAI.GroupTheory.Coxeter.Roots.PlaneBasis` | `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis` | current_candidate | `rootPlane_eq_of_mem`:20, `positive_combination_of_slope_between`:33, `noninverted_of_positive_combination`:72 |
| `OAI.GroupTheory.Coxeter.Roots.PlaneLength` | `ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength` | current_candidate | `planeLength`:21, `rootPlane_grouped_erase`:24, `planeDefect_eq_relative_difference`:49 |
| `OAI.GroupTheory.Coxeter.Roots.PlaneSubgroup` | `ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup` | current_candidate | `movingSubgroup`:19, `planeSubgroup`:36, `planeSubgroup_le_moving`:39 |
| `OAI.GroupTheory.Coxeter.Roots.PlaneTransport` | `ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport` | current_candidate | `graphRoot_mem`:21, `graphRoot_path_plane`:30, `twoStep_mem_coset`:39 |
| `OAI.GroupTheory.Coxeter.Roots.RatioOrder` | `ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder` | current_candidate | `simplePositive`:20, `simplePositive_injective`:30, `coordinate_sum`:36 |
| `OAI.GroupTheory.Coxeter.Roots.ReflectionLabels` | `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionLabels` | current_candidate | `Represents.triple_isReflection`:20, `BruhatStep.label_reflection`:55, `BruhatStep.composable_labels_ne`:61 |
| `OAI.GroupTheory.Coxeter.Roots.ReflectionOrder` | `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder` | current_candidate | `normalizedRoot_mem_iff`:33, `rootPlane_eq_normalized_span`:41, `normalizedRoot_affine`:59 |
| `OAI.GroupTheory.Coxeter.Roots.Splines` | `ForMathlib.GroupTheory.Coxeter.Roots.Splines` | current_candidate | `linearPolynomial`:18, `orbitSpline`:22, `orbitSpline_self`:25 |
| `OAI.LinearAlgebra.ConjugateRange` | `ForMathlib.LinearAlgebra.ConjugateRange` | current_candidate | `conjugate`:18, `map`:20, `map_bijective`:27 |
| `OAI.LinearAlgebra.CoordinateProjection` | `ForMathlib.LinearAlgebra.CoordinateProjection` | current_candidate | `eval`:16, `image`:17, `project`:18 |
| `OAI.LinearAlgebra.Descent` | `ForMathlib.LinearAlgebra.Quotient.Transport` | current_candidate | `descend`:18, `descend_apply`:22, `descend_idempotent`:28 |
| `OAI.LinearAlgebra.Dual.Adjoint` | `ForMathlib.LinearAlgebra.Dual.Adjoint` | current_candidate | `adjoint`:18, `pairing`:21, `adjoint_comp`:26 |
| `OAI.LinearAlgebra.Dual.BalancedCut` | `ForMathlib.LinearAlgebra.Dual.BalancedCut` | current_candidate | `balanced_two`:20, `balanced`:44 |
| `OAI.LinearAlgebra.Dual.Frobenius` | `ForMathlib.LinearAlgebra.Dual.Frobenius` | current_candidate | `restrictDual`:19, `fiber`:24, `trace_recover_fiber`:31 |
| `OAI.LinearAlgebra.Dual.IntegralSupport` | `ForMathlib.LinearAlgebra.Dual.IntegralSupport` | current_candidate | `projection`:16, `supported`:18, `cut`:27 |
| `OAI.LinearAlgebra.Dual.Summand` | `ForMathlib.LinearAlgebra.Dual.Summand` | current_candidate | `dualSection`:18, `dualProjection`:21, `projection_section`:24 |
| `OAI.LinearAlgebra.Dual.TransportPairing` | `ForMathlib.LinearAlgebra.Dual.TransportPairing` | current_candidate | `balanced`:14, `symmetric`:25 |
| `OAI.LinearAlgebra.KernelCoordinates` | `ForMathlib.LinearAlgebra.KernelCoordinates` | current_candidate | `injective_of_zero_lift`:18, `maps_eq_iff_of_zero_iff`:25, `functions_eq_of_surjective`:29 |
| `OAI.LinearAlgebra.PairProjection.Basic` | `ForMathlib.LinearAlgebra.PairProjection` | current_candidate | `relation`:18, `Edge`:19, `lower`:21 |
| `OAI.LinearAlgebra.PairProjection.Kernel` | `ForMathlib.LinearAlgebra.PairProjection` | current_candidate | `kernel_upper`:18, `upper_kernel_of_divisibility`:23 |
| `OAI.LinearAlgebra.PairProjection.Lifting` | `ForMathlib.LinearAlgebra.PairProjection` | current_candidate | `cross_lift`:18 |
| `OAI.LinearAlgebra.PlaneReduction` | `ForMathlib.LinearAlgebra.PlaneReduction` | current_candidate | `scalar_reduction`:14, `associated_reduction`:27 |
| `OAI.LinearAlgebra.Reflection.Classification` | `ForMathlib.LinearAlgebra.Reflection.Classification` | current_candidate | `orthogonal_eq_id_or_rootReflection`:13 |
| `OAI.LinearAlgebra.Reflection.Forms` | `ForMathlib.LinearAlgebra.Reflection.Forms` | current_candidate | `finrank_moving_conj`:14, `rank_one_eq_reflection_of_negates`:25, `negates_of_commutes_nonpos`:58 |
| `OAI.LinearAlgebra.Reflection.Plane` | `ForMathlib.LinearAlgebra.Reflection.Plane` | current_candidate | `formPair_surjective`:13, `range_preReflection_product_sub_id`:41, `range_reflection_product_sub_id`:65 |
| `OAI.LinearAlgebra.SymmetricAlgebra.Quotient` | `ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient` | current_candidate | `ideal`:14, `quotientMap`:17, `ideal_le_ker`:25 |
| `OAI.LinearAlgebra.SymmetricAlgebra.RootIdeal` | `ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal` | current_candidate | `symmetric_ι_injective`:15, `rootIdeal`:27, `rootLine`:30 |
| `OAI.LinearAlgebra.TensorProduct.Coordinates` | `ForMathlib.LinearAlgebra.TensorProduct.Coordinates` | current_candidate | `tensor_range_le_of_one_tmul`:16, `tensor_maps_eq_of_one_tmul`:27, `codRestrict_surjective_of_range_le`:38 |
| `OAI.Order.Interval.Diamonds` | `ForMathlib.Order.Interval.Diamonds` | current_candidate | `DiamondEdges`:15, `DiamondEdges.map`:24, `DiamondEdges.map_iff`:32 |
| `OAI.RepresentationTheory.BottSamelson.AdjointSheaf` | `OAI.KL.BottSamelson.AdjointSheaf` | project_current_interface | `symmetricCoefficientNoetherian`:22, `bottVertexProjection`:39, `bottVertexProjection_injective`:44 |
| `OAI.RepresentationTheory.BottSamelson.CanonicalPairing` | `OAI.KL.BottSamelson.CanonicalPairing` | project_current_interface | `bottCanonicalAdjointHom`:24, `bottCanonicalAdjointHom_top_bijective`:28, `bottCanonicalAdjointIso`:35 |
| `OAI.RepresentationTheory.BottSamelson.Character` | `OAI.KL.BottSamelson.Character` | project_current_interface | `bottSplitRightWord`:24, `bottSplitLeftWord`:29, `bottSplitRightWord_coordinates`:36 |
| `OAI.RepresentationTheory.BottSamelson.CharacterDecomposition` | `OAI.KL.BottSamelson.CharacterDecomposition` | project_current_interface | `bottCharacter_decomposition_both`:18 |
| `OAI.RepresentationTheory.BottSamelson.Pairings` | `OAI.KL.BottSamelson.Pairings` | project_current_interface | `reflection_character_congruence_iff`:26, `reflection_character_separates`:82, `isReflection_of_prime_character_congruence`:103 |
| `OAI.RepresentationTheory.BottSamelson.Stalks` | `OAI.KL.BottSamelson.Stalks` | project_current_interface | `bottWeightProjection_range_le`:25, `bottTensor_maps_eq`:35, `bottFullIndex`:57 |
| `OAI.RepresentationTheory.BottSamelson.Support` | `OAI.KL.BottSamelson.Support` | project_current_interface | `symmetricGrading_zero`:21, `bottSupported_of_stalkSupport`:43, `bottStalk_supported_annihilates`:53 |
| `OAI.RepresentationTheory.BottSamelson.Words` | `ForMathlib.RepresentationTheory.BottSamelson.TitsWords` | current_candidate | `SymmetricCoefficient`:21, `coefficientAction`:23, `coefficientAction_simple`:31 |
| `OAI.RepresentationTheory.Hecke.Coefficients` | `ForMathlib.RepresentationTheory.Hecke.Coefficients` | current_candidate | `left_coeff`:15, `left_plus_coeff`:60, `positiveWord`:67 |
| `OAI.RepresentationTheory.Hecke.Dihedral` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Dihedral` | current_candidate | `lowerSum`:20, `double_string`:40, `left_plus_coeff`:113 |
| `OAI.RepresentationTheory.Hecke.DualR` | `ForMathlib.RepresentationTheory.Hecke.DualR` | current_candidate | `dualR`:16, `dualR_zero`:24, `dualR_recursion`:28 |
| `OAI.RepresentationTheory.Hecke.DyerPaths.Adapted` | `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted` | current_candidate | `Edge`:21, `source`:22, `target`:23 |
| `OAI.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder` | `ForMathlib.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder` | current_candidate | `lexRootScore`:26, `lexRootScore_injective`:29, `lexEdgeScore`:35 |
| `OAI.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates` | `ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates` | current_candidate | `path_coordinates`:24, `intervalToAmbient`:55, `intervalToAmbient_injective`:58 |
| `OAI.RepresentationTheory.Hecke.DyerPaths.Wall` | `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall` | current_candidate | `rootValue`:20, `rootPlaneTies`:23, `schedule`:28 |
| `OAI.RepresentationTheory.Hecke.Inverse` | `ForMathlib.RepresentationTheory.Hecke.Inverse` | current_candidate | `bar_coeff_inverse`:25, `rValue_inverse_factor`:39, `rValue_inverse`:55 |
| `OAI.RepresentationTheory.Hecke.Operators` | `ForMathlib.RepresentationTheory.Hecke.Operators` | current_candidate | `Space`:23, `basis`:25, `end_ext`:28 |
| `OAI.RepresentationTheory.Hecke.OrdinaryR` | `ForMathlib.RepresentationTheory.Hecke.OrdinaryR` | current_candidate | `variableUnit`:25, `rValue_polynomial`:32, `polynomial`:63 |
| `OAI.RepresentationTheory.Hecke.PositiveWord` | `ForMathlib.RepresentationTheory.Hecke.PositiveWord` | current_candidate | `one_add_leftInv`:17, `barLinear_positiveWord`:24, `positiveWord_support`:36 |
| `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Freeness` | `OAI.KL.Comparison.SuffixFreeness` | project_current_interface | `no_conditions_free`:23, `schedule_kernels_free_of_images_eq`:37, `schedule_kernels_free_of_endpoint_eq`:73 |
| `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Propagation` | `OAI.KL.Comparison.Propagation` | project_current_interface | `actual_edge_increment_le`:28, `actual_edge_increment_eq_iff`:49, `partial_kernel_projective_of_image_eq`:92 |
| `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Transport` | `OAI.KL.Comparison.Transport` | project_current_interface | `boundarySheaf_gradedIso`:26, `stalkCharacter_eq_character`:35, `upperInclusion`:58 |
| `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Finite` | `OAI.KL.Invariance.Finite` | project_current_interface | `comparison_of_source02`:24, `comparison_difference_le`:53, `bottom_eq_of_comparisons`:88 |
| `OAI.RepresentationTheory.KazhdanLusztig.Invariance.FiniteModel` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.FiniteRankReduction` | current_candidate | `FiniteIntervalModel`:16, `exists_finiteIntervalModel`:24, `intervalEndpointCongr`:36 |
| `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Induction` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.IntervalTransport` | current_candidate | `rankDifference_subinterval_lt`:20, `rTilde_transport_all`:33, `scaledKL_eq_scaledPolynomial`:67 |
| `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Main` | `OAI.KL.Invariance.Main` | project_current_interface | `combinatorial_invariance`:17 |
| `OAI.RepresentationTheory.KazhdanLusztig.Localization.Ambient` | `OAI.KL.Localization.Ambient` | project_current_interface | `exists_outgoing_below`:16, `polynomialRoot`:37, `polynomialRoot_homogeneous`:41 |
| `OAI.RepresentationTheory.KazhdanLusztig.Localization.Edge` | `OAI.KL.Localization.Edge` | project_current_interface | `EdgeRing`:20, `edgeRingEquiv`:23, `reducedPolynomialRoot_prime`:43 |
| `OAI.RepresentationTheory.KazhdanLusztig.Localization.Embed` | `OAI.KL.Localization.GraphEmbedding` | project_current_interface | `embedLinear`:21, `embedLinear_injective`:26, `planePrime`:30 |
| `OAI.RepresentationTheory.KazhdanLusztig.Localization.Plane` | `OAI.KL.Localization.Plane` | project_current_interface | `CosetVertex`:22, `cosetAmbient`:31, `cosetAmbient_injective`:34 |
| `OAI.RepresentationTheory.KazhdanLusztig.Localization.PlaneModel` | `ForMathlib.Combinatorics.MomentGraph.Bruhat.PlaneModel` | current_candidate | `modelLabel`:20, `model_flabby`:24, `model_generated`:30 |
| `OAI.RepresentationTheory.KazhdanLusztig.Localization.Terminal` | `OAI.KL.Localization.TerminalImages` | project_current_interface | `localized_boundary_decomposition`:21, `scheduledLower_root_ne`:63, `outgoingUpper_root_ne`:78 |
| `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical` | current_candidate | `polynomial`:26, `polynomial_zero`:47, `defect`:51 |
| `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization` | current_candidate | `rPolynomial_normalization`:18, `scaledKL`:72, `scaledKL_reciprocity_inverse`:79 |
| `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized` | current_candidate | `PolynomialFamilies`:13, `NormalizedKL`:20, `klFamilies`:39 |
| `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic` | current_candidate | `normalized_restriction`:19, `klFamilies_inclusion`:58, `klPolynomial_inclusion`:65 |
| `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity` | current_candidate | `scaledKL_reciprocity_upper`:16 |
| `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR` | current_candidate | `rPolynomial`:18 |
| `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Unique` | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Unique` | current_candidate | `normalized_R_unique`:16, `normalized_P_unique`:52, `normalizedKL_unique`:105 |
| `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Boundary` | `OAI.KL.Sheaves.Boundary` | project_current_interface | `Coefficient`:25, `root`:27, `polynomialLabel`:30 |
| `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.FreeModel` | `OAI.KL.Sheaves.FreeModel` | project_current_interface | `SectionDualityObligation`:23, `sectionDualityObligation_of_perfectPairing`:46, `FreeSheaf`:75 |
| `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.LowerCharacter` | `OAI.KL.Sheaves.LowerCharacter` | project_current_interface | `lowerCharacter`:20, `boundaryModels_character`:24, `lowerCharacter_zero`:39 |
| `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Reciprocity` | `OAI.KL.Sheaves.Reciprocity` | project_current_interface | `boundarySheaf_perfectPairing`:18, `sectionDualityObligation`:37, `boundaryFreeSheaf`:61 |
| `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.StalkReciprocity` | `OAI.KL.Sheaves.StalkReciprocity` | project_current_interface | `stalkCharacter_reciprocity`:23 |
| `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Support` | `OAI.KL.Sheaves.Support` | project_current_interface | `incomingEquivInversions`:20, `incoming_card`:49, `root_injective_on_labels`:74 |
| `OAI.RingTheory.Localization.RelativePrime` | `ForMathlib.RingTheory.Localization.RelativePrime` | current_candidate | `not_dvd_map`:13, `map_prime`:21, `map_relPrime`:30 |

The full machine-readable inventory, current basis and candidate preparation
items are in `upstream-assessment.json`. ForMathlib → OAI dependencies: **0**.
The 34 original KL import entrypoints plus two kernel import entrypoints are
wrappers, not additional proposed upstream mathematics.
