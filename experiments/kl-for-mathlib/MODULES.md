# Current module guide

Use `import OAI.KL` for the application theorem. Use a focused `ForMathlib.*`
module for reusable mathematics. `ForMathlib` imports all candidates and
`OAI.Architecture` imports all implementations for auditing; neither is the
minimal project entrypoint. Compatibility paths are listed separately below.

The declaration anchors are navigation examples, not an exhaustive API export.
Public-type validation covers all 3902 declarations. Source spans: MIGRATION.md.

## Algebra

| Current implementation | Declaration anchors |
| --- | --- |
| [`ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic`](ForMathlib/Algebra/Algebra/ReflectionFrobenius/Basic.lean) | `fixed`, `fixed_val`, `expand` |
| [`ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis`](ForMathlib/Algebra/Algebra/ReflectionFrobenius/Basis.lean) | `wallCoordinate`, `wallMatrix`, `wallMatrix_mulVec` |
| [`ForMathlib.Algebra.BigOperators.SingleCoordinate`](ForMathlib/Algebra/BigOperators/SingleCoordinate.lean) | `finite_character_cancellation`, `matrix_difference_single`, `matrix_difference_le` |
| [`ForMathlib.Algebra.Module.CoefficientChange.Basic`](ForMathlib/Algebra/Module/CoefficientChange/Basic.lean) | `equivVal`, `_root_.OAI.KLInvariance.CoefficientChange.instAddCommGroup`, `_root_.OAI.KLInvariance.CoefficientChange.instModule` |
| [`ForMathlib.Algebra.Module.CoefficientChange.Dual`](ForMathlib/Algebra/Module/CoefficientChange/Dual.lean) | `mapEquiv`, `dualTo`, `dualFrom` |
| [`ForMathlib.Algebra.Module.Cover.Local`](ForMathlib/Algebra/Module/Cover/Local.lean) | `lift_surjective`, `splitEquiv`, `exists_split_minimal_cover` |
| [`ForMathlib.Algebra.Module.Flat.Kernel`](ForMathlib/Algebra/Module/Flat/Kernel.lean) | `baseChange_ker`, `baseChange_map` |
| [`ForMathlib.Algebra.Module.Free.ScalarDivisibility`](ForMathlib/Algebra/Module/Free/ScalarDivisibility.lean) | `exists_smul_iff`, `exists_prod_smul`, `scalar_quotient_regular` |
| [`ForMathlib.Algebra.Module.Graded.Adjoint`](ForMathlib/Algebra/Module/Graded/Adjoint.lean) | `perfect_inverse_of_homogeneous_functional`, `adjoint_homogeneous` |
| [`ForMathlib.Algebra.Module.Graded.Basis`](ForMathlib/Algebra/Module/Graded/Basis.lean) | `basisPiece`, `mem_basisPiece`, `basisPiece_decomposition` |
| [`ForMathlib.Algebra.Module.Graded.Components`](ForMathlib/Algebra/Module/Graded/Components.lean) | `component`, `positiveIdeal`, `subsingleton_of_positiveIdeal_smul_eq_top` |
| [`ForMathlib.Algebra.Module.Graded.FinitePieces`](ForMathlib/Algebra/Module/Graded/FinitePieces.lean) | `subPiece_finite`, `piPiece_finite` |
| [`ForMathlib.Algebra.Module.Graded.Generators`](ForMathlib/Algebra/Module/Graded/Generators.lean) | `internal_of_components`, `image_isInternal`, `subPiece` |
| [`ForMathlib.Algebra.Module.Graded.Hilbert.Basic`](ForMathlib/Algebra/Module/Graded/Hilbert/Basic.lean) | `piece`, `term`, `value` |
| [`ForMathlib.Algebra.Module.Graded.Hilbert.Images`](ForMathlib/Algebra/Module/Graded/Hilbert/Images.lean) | `scalarDegreeMap`, `scalarDegreeMap_surjective`, `scalarDegreeMap_injective` |
| [`ForMathlib.Algebra.Module.Graded.Hilbert.Increment`](ForMathlib/Algebra/Module/Graded/Hilbert/Increment.lean) | `shifted_map_homogeneous`, `shiftedImagePieceMap`, `shiftedImagePieceMap_surjective` |
| [`ForMathlib.Algebra.Module.Graded.Hilbert.Numerator`](ForMathlib/Algebra/Module/Graded/Hilbert/Numerator.lean) | `hasSum_shift_coeff`, `numerator_unique`, `numerator_add_shift` |
| [`ForMathlib.Algebra.Module.Graded.Hilbert.Series`](ForMathlib/Algebra/Module/Graded/Hilbert/Series.lean) | `hasSum_monomials`, `intWeight_eq_natWeight`, `polynomialGrading_nat` |
| [`ForMathlib.Algebra.Module.Graded.HomogeneousDual`](ForMathlib/Algebra/Module/Graded/HomogeneousDual.lean) | `mem_of_homogeneous_smul`, `homogeneous_basis_repr`, `dualBasis_homogeneous` |
| [`ForMathlib.Algebra.Module.Graded.HomogeneousEquiv`](ForMathlib/Algebra/Module/Graded/HomogeneousEquiv.lean) | `equiv_inverse_homogeneous`, `pairing_to_dual_homogeneous`, `perfectPairing_inverse_homogeneous` |
| [`ForMathlib.Algebra.Module.Graded.HomogeneousMul`](ForMathlib/Algebra/Module/Graded/HomogeneousMul.lean) | `homogeneous_of_mul` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.Basic`](ForMathlib/Algebra/Module/Graded/ModuleData/Basic.lean) | `ModuleData`, `_root_.OAI.KLInvariance.Graded.instCoeSortModuleDataType`, `_root_.OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.Character`](ForMathlib/Algebra/Module/Graded/ModuleData/Character.lean) | `mapNonnegativeBasis`, `character_eq_of_gradedEquiv`, `char` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.CharacterDual`](ForMathlib/Algebra/Module/Graded/ModuleData/CharacterDual.lean) | `unitPolynomialBasis`, `char_unit`, `char_natDegree_le_of_dual_equiv` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange`](ForMathlib/Algebra/Module/Graded/ModuleData/CoefficientChange.lean) | `unchangeHom`, `changeUnitHom`, `changeUnitInvHom` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic`](ForMathlib/Algebra/Module/Graded/ModuleData/CoefficientChange/Basic.lean) | `changePiece`, `mem_changePiece`, `change` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.CoverUniqueness`](ForMathlib/Algebra/Module/Graded/ModuleData/CoverUniqueness.lean) | `MinimalCover.hom_bijective` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.Duality`](ForMathlib/Algebra/Module/Graded/ModuleData/Duality.lean) | `equivOfEq_inverse`, `homOfEq`, `unit_endomorphisms_commute` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.Equality`](ForMathlib/Algebra/Module/Graded/ModuleData/Equality.lean) | `Hom.ofEq`, `Hom.ofEq_apply`, `Hom.ofEq_bijective` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover`](ForMathlib/Algebra/Module/Graded/ModuleData/MinimalCover.lean) | `idempotent_eq_zero`, `MinimalCover.bijective_of_boundaryIso`, `inverse` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection`](ForMathlib/Algebra/Module/Graded/ModuleData/PairProjection.lean) | `pairLower_kernel_homogeneous`, `pairEdgePiece`, `pairEdge` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom`](ForMathlib/Algebra/Module/Graded/ModuleData/QuotientHom.lean) | `quotientHom`, `quotientHom_apply` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.Range`](ForMathlib/Algebra/Module/Graded/ModuleData/Range.lean) | `rangeMap`, `rangeInclusion`, `rangeProjection` |
| [`ForMathlib.Algebra.Module.Graded.ModuleData.Transport`](ForMathlib/Algebra/Module/Graded/ModuleData/Transport.lean) | `zero`, `Hom.zero`, `Hom.pi` |
| [`ForMathlib.Algebra.Module.Graded.NonnegativeBasis`](ForMathlib/Algebra/Module/Graded/NonnegativeBasis.lean) | `polynomial_scalar_mod_positive`, `basis_coordinates_graded`, `NonnegativeBasis` |
| [`ForMathlib.Algebra.Module.Graded.PolynomialMap`](ForMathlib/Algebra/Module/Graded/PolynomialMap.lean) | `algHom_polynomialGrading` |
| [`ForMathlib.Algebra.Module.Graded.RegularScalar`](ForMathlib/Algebra/Module/Graded/RegularScalar.lean) | `homogeneous_positive_nonzero`, `dual_mem_ideal`, `local_diagonal_strict_degree` |
| [`ForMathlib.Algebra.Module.Localization.FiniteCharacters`](ForMathlib/Algebra/Module/Localization/FiniteCharacters.lean) | `diagonal`, `stabilizer`, `diagonal_mem` |
| [`ForMathlib.Algebra.Module.Localization.Lattice`](ForMathlib/Algebra/Module/Localization/Lattice.lean) | `finsupp_divide`, `basis_divide`, `mem_of_prime_local_membership` |
| [`ForMathlib.Algebra.Module.Localization.Membership`](ForMathlib/Algebra/Module/Localization/Membership.lean) | `baseChange_eq_localized`, `denominator` |
| [`ForMathlib.Algebra.Module.Localization.ProjectiveLattice`](ForMathlib/Algebra/Module/Localization/ProjectiveLattice.lean) | `finsupp_divide`, `prime_divide_of_relation`, `mem_of_prime_local_membership` |
| [`ForMathlib.Algebra.Module.Projective.Range`](ForMathlib/Algebra/Module/Projective/Range.lean) | `descend`, `descend_apply`, `projective_of_end` |
| [`ForMathlib.Algebra.Module.Projective.ReverseFiltration`](ForMathlib/Algebra/Module/Projective/ReverseFiltration.lean) | `kernel_projective_of_presentation` |
| [`ForMathlib.Algebra.Module.Projective.ScalarKernel`](ForMathlib/Algebra/Module/Projective/ScalarKernel.lean) | `scalarKernelEquiv`, `projective_kernel_of_scalar_presentation`, `imageMapKernelEquiv` |
| [`ForMathlib.Algebra.Module.Projective.ScalarQuotient`](ForMathlib/Algebra/Module/Projective/ScalarQuotient.lean) | `scalarQuotientMap`, `scalarQuotientMap_surjective`, `scalarKernelMap` |
| [`ForMathlib.Algebra.Module.Projective.Transport`](ForMathlib/Algebra/Module/Projective/Transport.lean) | `projective_of_same_range`, `projective` |
| [`ForMathlib.Algebra.Module.Quotient.KernelReduction`](ForMathlib/Algebra/Module/Quotient/KernelReduction.lean) | `kernel_saturated`, `reduced_kernel_injective`, `reducedInclusion` |
| [`ForMathlib.Algebra.Module.Quotient.ScalarImage`](ForMathlib/Algebra/Module/Quotient/ScalarImage.lean) | `coordinateReduction`, `coordinateReduction_surjective`, `coordinateReduction_kernel` |
| [`ForMathlib.Algebra.Module.ReflectionPair.TensorDescent`](ForMathlib/Algebra/Module/ReflectionPair/TensorDescent.lean) | `tensorFirst_map`, `tensorSecond_map`, `tensor_difference` |
| [`ForMathlib.Algebra.Module.ReflectionPair.TensorKernel`](ForMathlib/Algebra/Module/ReflectionPair/TensorKernel.lean) | `scalarModule`, `scalarTower`, `scalarEquiv` |
| [`ForMathlib.Algebra.Module.ReflectionPair.Twist`](ForMathlib/Algebra/Module/ReflectionPair/Twist.lean) | `equivVal`, `_root_.OAI.KLInvariance.ReflectionPairTranslation.Twist.instAddCommGroup`, `_root_.OAI.KLInvariance.ReflectionPairTranslation.Twist.instModule` |
| [`ForMathlib.Algebra.Module.Submodule.PiIdeal`](ForMathlib/Algebra/Module/Submodule/PiIdeal.lean) | `pi_mem_ideal_smul` |
| [`ForMathlib.Algebra.Module.Submodule.ProductScaling`](ForMathlib/Algebra/Module/Submodule/ProductScaling.lean) | `smul_top_le_of_map_dvd`, `smul_top_eq_of_map_associated`, `associated_prod_power` |
| [`ForMathlib.Algebra.Module.Submodule.ScaledImage`](ForMathlib/Algebra/Module/Submodule/ScaledImage.lean) | `scaled`, `map_scaled`, `map_eq_scaled_iff` |
| [`ForMathlib.Algebra.Order.Field.RealScaling`](ForMathlib/Algebra/Order/Field/RealScaling.lean) | `edge_scalar_identity`, `transferCoefficient_pos`, `stateScale_pos` |
| [`ForMathlib.Algebra.Polynomial.LowPart`](ForMathlib/Algebra/Polynomial/LowPart.lean) | `lowPart`, `lowPart_degree`, `lowPart_solution` |
| [`ForMathlib.Algebra.Polynomial.Reciprocal`](ForMathlib/Algebra/Polynomial/Reciprocal.lean) | `low_degree_reflect_eq_self`, `low_degree_zero_of_eval_reciprocal`, `eq_of_eval_difference_reciprocal` |
| [`ForMathlib.Algebra.Polynomial.ScaledEvaluation`](ForMathlib/Algebra/Polynomial/ScaledEvaluation.lean) | `scaledPolynomial`, `eq_of_scaled_difference_reciprocal` |
| [`ForMathlib.Algebra.Polynomial.TransferEvaluation`](ForMathlib/Algebra/Polynomial/TransferEvaluation.lean) | `polynomial_eq_of_transfer_eval_eq` |
## Combinatorics

| Current implementation | Declaration anchors |
| --- | --- |
| [`ForMathlib.Combinatorics.Dihedral.SignedCount`](ForMathlib/Combinatorics/Dihedral/SignedCount.lean) | `Before`, `before_same_source_pos`, `before_same_source_neg` |
| [`ForMathlib.Combinatorics.DirectedPaths.Basic`](ForMathlib/Combinatorics/DirectedPaths/Basic.lean) | `IsPath`, `pathTerm`, `step` |
| [`ForMathlib.Combinatorics.DirectedPaths.Monotone`](ForMathlib/Combinatorics/DirectedPaths/Monotone.lean) | `mem_suffix_iff_score_lt`, `mem_suffix_iff_score_lt_injective`, `step_monotone` |
| [`ForMathlib.Combinatorics.DirectedPaths.PositiveTransfer`](ForMathlib/Combinatorics/DirectedPaths/PositiveTransfer.lean) | `transfer`, `transfer_monotone`, `transfer_injective` |
| [`ForMathlib.Combinatorics.DirectedPaths.ScalarMap`](ForMathlib/Combinatorics/DirectedPaths/ScalarMap.lean) | `dispatch_map` |
| [`ForMathlib.Combinatorics.DirectedPaths.SortedSchedule`](ForMathlib/Combinatorics/DirectedPaths/SortedSchedule.lean) | `sortedSchedule`, `sortedSchedule_nodup`, `sortedSchedule_pairwise` |
| [`ForMathlib.Combinatorics.DirectedPaths.Subpaths`](ForMathlib/Combinatorics/DirectedPaths/Subpaths.lean) | `IsPath.map`, `IsPath.isChain`, `IsPath.pairwise_map_of_local` |
| [`ForMathlib.Combinatorics.DirectedPaths.Suffix`](ForMathlib/Combinatorics/DirectedPaths/Suffix.lean) | `exists_suffix_score_gt` |
| [`ForMathlib.Combinatorics.DirectedPaths.Transfer`](ForMathlib/Combinatorics/DirectedPaths/Transfer.lean) | `dispatch_append`, `dispatch_add`, `dispatch_mul_right` |
| [`ForMathlib.Combinatorics.MomentGraph.Boundary.Basic`](ForMathlib/Combinatorics/MomentGraph/Boundary/Basic.lean) | `BoundarySheaf`, `singletonSheaf`, `singleton_boundarySheaf` |
| [`ForMathlib.Combinatorics.MomentGraph.Boundary.Extension`](ForMathlib/Combinatorics/MomentGraph/Boundary/Extension.lean) | `extend_iso`, `exists_gradedIso` |
| [`ForMathlib.Combinatorics.MomentGraph.Boundary.Hom`](ForMathlib/Combinatorics/MomentGraph/Boundary/Hom.lean) | `idempotent_zero_of_top_zero`, `idempotent_trivial`, `endomorphism_bijective_of_top` |
| [`ForMathlib.Combinatorics.MomentGraph.Boundary.Models`](ForMathlib/Combinatorics/MomentGraph/Boundary/Models.lean) | `top_nontrivial`, `iso_of_primitive_top_split`, `iso_coefficientChange` |
| [`ForMathlib.Combinatorics.MomentGraph.Boundary.Summand`](ForMathlib/Combinatorics/MomentGraph/Boundary/Summand.lean) | `primitive_identity`, `split_projector_primitive` |
| [`ForMathlib.Combinatorics.MomentGraph.Boundary.Uniqueness`](ForMathlib/Combinatorics/MomentGraph/Boundary/Uniqueness.lean) | `hom_vertex_bijective`, `homIso`, `hom_vertex_bijective_of_iso` |
| [`ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic`](ForMathlib/Combinatorics/MomentGraph/Bruhat/Basic.lean) | `Edge`, `_root_.OAI.KLInvariance.BruhatGraph.instFiniteEdge`, `source` |
| [`ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel`](ForMathlib/Combinatorics/MomentGraph/Bruhat/DihedralModel.lean) | `reflection_of_parity`, `oppositeExternal`, `sameExternal` |
| [`ForMathlib.Combinatorics.MomentGraph.Bruhat.PlaneModel`](ForMathlib/Combinatorics/MomentGraph/Bruhat/PlaneModel.lean) | `modelLabel`, `model_flabby`, `model_generated` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/AttachBottom.lean) | `bottomGraph`, `attachEdges`, `attachQuotient` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Character.lean) | `freeStalkChar`, `ModelSum.character`, `exists_stalkCharacter_decomposition` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Defs.lean) | `GradedSheaf`, `forget`, `EdgeFlabby` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Duality.lean) | `dualToSupport_homogeneous`, `UpperQuotient.annihilates`, `upwardSubmodule_saturated` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Extension.lean) | `lowerAt`, `lowerAt_map`, `upwardSubmodule` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hilbert`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Hilbert.lean) | `kernelHilbert`, `lowerImage`, `upperImage` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Hom.lean) | `Endomorphism`, `complement`, `complement_idempotent` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Models.lean) | `kernelData`, `kernelProdEquiv`, `kernelProdEquiv_graded` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Properties.lean) | `FreeStalks`, `UpperQuotient`, `KernelMinimal` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Reindex.lean) | `GraphEquiv`, `reindex`, `reindexAssignment` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean) | `Hom.eq_of_maps`, `Hom.eq_of_vertex`, `Hom.zero` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Uniqueness.lean) | `Hom.edge_bijective_of_vertex`, `Hom.isoOfBijective`, `Hom.aboveIso` |
| [`ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion`](ForMathlib/Combinatorics/MomentGraph/OrderedGraph/VertexDeletion.lean) | `removeGraph`, `removeTarget`, `splitVertex` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange`](ForMathlib/Combinatorics/MomentGraph/Sheaf/BaseChange.lean) | `baseChange`, `tensorAssignments`, `baseChange_tmul_compatible` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Basic.lean) | `OrderedGraph`, `Sheaf`, `Assignment` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Duality.lean) | `scaled_single_section`, `labelProduct`, `labelProduct_ne_zero` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown`](ForMathlib/Combinatorics/MomentGraph/Sheaf/FlowDown.lean) | `modelOutgoing`, `modelProduct`, `HasFlowDown` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Hom`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Hom.lean) | `split_stalk_graded` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Iso.lean) | `Iso`, `symm`, `assignments` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Localization`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Localization.lean) | `edge_subsingleton_of_unit`, `supportedOutgoing`, `kernelProduct` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Models`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Models.lean) | `zeroVertex_subsingleton`, `zeroEdge_subsingleton`, `LocalModels` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Pi.lean) | `pi`, `pi_compatible`, `pi_generated` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Products`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Products.lean) | `zero`, `prod`, `prod_generated` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Pullback.lean) | `GraphMap`, `moduleEq`, `moduleEq_apply` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Restriction`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Restriction.lean) | `inducedGraph`, `restrict`, `restrictAssignment` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages`](ForMathlib/Combinatorics/MomentGraph/Sheaf/ScaledImages.lean) | `outgoingLabelProduct`, `outgoingLabelProduct_dvd`, `outgoingLabelProduct_smul_mem` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Structure.lean) | `quotientLinear`, `structureSheaf`, `structureSheaf_free` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Uniqueness`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Uniqueness.lean) | `stalk_hom_bijective` |
## GroupTheory

| Current implementation | Declaration anchors |
| --- | --- |
| [`ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`](ForMathlib/GroupTheory/Coxeter/Bruhat/Basic.lean) | `bruhat_refl`, `bruhat_trans`, `length_le_of_bruhat` |
| [`ForMathlib.GroupTheory.Coxeter.Bruhat.Defs`](ForMathlib/GroupTheory/Coxeter/Bruhat/Defs.lean) | `BruhatStep`, `BruhatLE`, `Interval` |
| [`ForMathlib.GroupTheory.Coxeter.Bruhat.Descent`](ForMathlib/GroupTheory/Coxeter/Bruhat/Descent.lean) | `simple_mul_bruhat_of_descent`, `lower_parity_balance`, `externalLower` |
| [`ForMathlib.GroupTheory.Coxeter.Bruhat.DiamondClosure`](ForMathlib/GroupTheory/Coxeter/Bruhat/DiamondClosure.lean) | `bruhatStep_of_interval_covBy`, `diamondEdges_bruhatStep` |
| [`ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds`](ForMathlib/GroupTheory/Coxeter/Bruhat/Diamonds.lean) | `diamondEdges_of_bruhatStep`, `intervalIso_bruhatStep_iff`, `diamondEdges_of_bruhatStep_general` |
| [`ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset`](ForMathlib/GroupTheory/Coxeter/Bruhat/LowerFinset.lean) | `lowerFinset` |
| [`ForMathlib.GroupTheory.Coxeter.Bruhat.Transport`](ForMathlib/GroupTheory/Coxeter/Bruhat/Transport.lean) | `intervalIso_restrict` |
| [`ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds`](ForMathlib/GroupTheory/Coxeter/Dihedral/Diamonds.lean) | `alt_add_two`, `alt_odd_sandwich`, `odd_alt_reflection` |
| [`ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport`](ForMathlib/GroupTheory/Coxeter/Dihedral/IntervalTransport.lean) | `rank_two_of_two_step_bound`, `swapHom`, `swap` |
| [`ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem`](ForMathlib/GroupTheory/Coxeter/Dihedral/PlaneSystem.lean) | `pairMatrix`, `wordProd_alt_even`, `injective_of_simple_order` |
| [`ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords`](ForMathlib/GroupTheory/Coxeter/Dihedral/SignedWords.lean) | `wordProd_alt_odd`, `rotation`, `simple_rotation` |
| [`ForMathlib.GroupTheory.Coxeter.Dihedral.Words`](ForMathlib/GroupTheory/Coxeter/Dihedral/Words.lean) | `alt`, `reduced_cons_cons_ne`, `reduced_cons_eq_alt` |
| [`ForMathlib.GroupTheory.Coxeter.Exchange`](ForMathlib/GroupTheory/Coxeter/Exchange.lean) | `simpleAction`, `wordAction`, `wordAction_concat` |
| [`ForMathlib.GroupTheory.Coxeter.Parabolic.InversionList`](ForMathlib/GroupTheory/Coxeter/Parabolic/InversionList.lean) | `leftInvSeq_inclusion`, `reflection_inclusion`, `bruhatStep_inclusion_iff` |
| [`ForMathlib.GroupTheory.Coxeter.Parabolic.Standard`](ForMathlib/GroupTheory/Coxeter/Parabolic/Standard.lean) | `matrix`, `system`, `inclusion` |
| [`ForMathlib.GroupTheory.Coxeter.Parabolic.Support`](ForMathlib/GroupTheory/Coxeter/Parabolic/Support.lean) | `reduced_of_append`, `reduced_pair_eq_alternating`, `alternating_length_bound` |
| [`ForMathlib.GroupTheory.Coxeter.Realization.Cotangent`](ForMathlib/GroupTheory/Coxeter/Realization/Cotangent.lean) | `root`, `normal_root`, `simple` |
| [`ForMathlib.GroupTheory.Coxeter.Realization.Faithful`](ForMathlib/GroupTheory/Coxeter/Realization/Faithful.lean) | `extendedAction_injective`, `involution_of_moving_rank_one`, `isReflection_of_moving_rank_one` |
| [`ForMathlib.GroupTheory.Coxeter.Realization.Geometric`](ForMathlib/GroupTheory/Coxeter/Realization/Geometric.lean) | `simple_normal_value`, `geometricSimple`, `geometricSimple_liftable` |
| [`ForMathlib.GroupTheory.Coxeter.Realization.Positivity`](ForMathlib/GroupTheory/Coxeter/Realization/Positivity.lean) | `rootCoeff`, `rootCoeff_succ`, `alternating_root` |
| [`ForMathlib.GroupTheory.Coxeter.Realization.Tits`](ForMathlib/GroupTheory/Coxeter/Realization/Tits.lean) | `gram`, `root`, `normal` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.Basic`](ForMathlib/GroupTheory/Coxeter/Roots/Basic.lean) | `IsRoot`, `Represents`, `embed` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder`](ForMathlib/GroupTheory/Coxeter/Roots/DihedralOrder.lean) | `prefixRoot`, `negPrefixRoot`, `prefixRoot_strictMono` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.LaterCount`](ForMathlib/GroupTheory/Coxeter/Roots/LaterCount.lean) | `edgeRoot_same_table`, `edgeRoot_next_table`, `afterIndicator` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.Order`](ForMathlib/GroupTheory/Coxeter/Roots/Order.lean) | `height`, `PositiveRoot.height_pos`, `normalizedRoot` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`](ForMathlib/GroupTheory/Coxeter/Roots/PlaneBasis.lean) | `rootPlane_eq_of_mem`, `positive_combination_of_slope_between`, `noninverted_of_positive_combination` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength`](ForMathlib/GroupTheory/Coxeter/Roots/PlaneLength.lean) | `planeLength`, `rootPlane_grouped_erase`, `planeDefect_eq_relative_difference` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup`](ForMathlib/GroupTheory/Coxeter/Roots/PlaneSubgroup.lean) | `movingSubgroup`, `planeSubgroup`, `planeSubgroup_le_moving` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport`](ForMathlib/GroupTheory/Coxeter/Roots/PlaneTransport.lean) | `graphRoot_mem`, `graphRoot_path_plane`, `twoStep_mem_coset` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder`](ForMathlib/GroupTheory/Coxeter/Roots/RatioOrder.lean) | `simplePositive`, `simplePositive_injective`, `coordinate_sum` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.ReflectionLabels`](ForMathlib/GroupTheory/Coxeter/Roots/ReflectionLabels.lean) | `Represents.triple_isReflection`, `BruhatStep.label_reflection`, `BruhatStep.composable_labels_ne` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder`](ForMathlib/GroupTheory/Coxeter/Roots/ReflectionOrder.lean) | `normalizedRoot_mem_iff`, `rootPlane_eq_normalized_span`, `normalizedRoot_affine` |
| [`ForMathlib.GroupTheory.Coxeter.Roots.Splines`](ForMathlib/GroupTheory/Coxeter/Roots/Splines.lean) | `linearPolynomial`, `orbitSpline`, `orbitSpline_self` |
## LinearAlgebra

| Current implementation | Declaration anchors |
| --- | --- |
| [`ForMathlib.LinearAlgebra.Avoidance`](ForMathlib/LinearAlgebra/Avoidance.lean) | `coordinatePolynomial`, `coordinatePolynomial_coeff`, `coordinatePolynomial_injective` |
| [`ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension`](ForMathlib/LinearAlgebra/BilinearForm/NondegenerateExtension.lean) | `Extension`, `extensionForm`, `extensionForm_symm` |
| [`ForMathlib.LinearAlgebra.ConjugateRange`](ForMathlib/LinearAlgebra/ConjugateRange.lean) | `conjugate`, `map`, `map_bijective` |
| [`ForMathlib.LinearAlgebra.CoordinateProjection`](ForMathlib/LinearAlgebra/CoordinateProjection.lean) | `eval`, `image`, `project` |
| [`ForMathlib.LinearAlgebra.Dual.Adjoint`](ForMathlib/LinearAlgebra/Dual/Adjoint.lean) | `adjoint`, `pairing`, `adjoint_comp` |
| [`ForMathlib.LinearAlgebra.Dual.BalancedCut`](ForMathlib/LinearAlgebra/Dual/BalancedCut.lean) | `balanced_two`, `balanced` |
| [`ForMathlib.LinearAlgebra.Dual.Frobenius`](ForMathlib/LinearAlgebra/Dual/Frobenius.lean) | `restrictDual`, `fiber`, `trace_recover_fiber` |
| [`ForMathlib.LinearAlgebra.Dual.IntegralSupport`](ForMathlib/LinearAlgebra/Dual/IntegralSupport.lean) | `projection`, `supported`, `cut` |
| [`ForMathlib.LinearAlgebra.Dual.Summand`](ForMathlib/LinearAlgebra/Dual/Summand.lean) | `dualSection`, `dualProjection`, `projection_section` |
| [`ForMathlib.LinearAlgebra.Dual.TransportPairing`](ForMathlib/LinearAlgebra/Dual/TransportPairing.lean) | `balanced`, `symmetric` |
| [`ForMathlib.LinearAlgebra.KernelCoordinates`](ForMathlib/LinearAlgebra/KernelCoordinates.lean) | `injective_of_zero_lift`, `maps_eq_iff_of_zero_iff`, `functions_eq_of_surjective` |
| [`ForMathlib.LinearAlgebra.KernelTransport`](ForMathlib/LinearAlgebra/KernelTransport.lean) | `kernelSourceEquiv`, `kernelTargetEquiv`, `kernelMixedEquiv` |
| [`ForMathlib.LinearAlgebra.PairProjection`](ForMathlib/LinearAlgebra/PairProjection.lean) | `relation`, `Edge`, `lower` |
| [`ForMathlib.LinearAlgebra.PlaneReduction`](ForMathlib/LinearAlgebra/PlaneReduction.lean) | `scalar_reduction`, `associated_reduction` |
| [`ForMathlib.LinearAlgebra.Quotient.Transport`](ForMathlib/LinearAlgebra/Quotient/Transport.lean) | `descend`, `descend_apply`, `descend_idempotent` |
| [`ForMathlib.LinearAlgebra.Reflection.Bilinear`](ForMathlib/LinearAlgebra/Reflection/Bilinear.lean) | `finrank_moving_conj`, `rank_one_eq_reflection_of_negates`, `negates_of_commutes_nonpos` |
| [`ForMathlib.LinearAlgebra.Reflection.Classification`](ForMathlib/LinearAlgebra/Reflection/Classification.lean) | `orthogonal_eq_id_or_rootReflection` |
| [`ForMathlib.LinearAlgebra.Reflection.Plane`](ForMathlib/LinearAlgebra/Reflection/Plane.lean) | `formPair_surjective`, `range_preReflection_product_sub_id`, `range_reflection_product_sub_id` |
| [`ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient`](ForMathlib/LinearAlgebra/SymmetricAlgebra/Quotient.lean) | `ideal`, `quotientMap`, `ideal_le_ker` |
| [`ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal`](ForMathlib/LinearAlgebra/SymmetricAlgebra/RootIdeal.lean) | `symmetric_ι_injective`, `rootIdeal`, `rootLine` |
| [`ForMathlib.LinearAlgebra.TensorProduct.Coordinates`](ForMathlib/LinearAlgebra/TensorProduct/Coordinates.lean) | `tensor_range_le_of_one_tmul`, `tensor_maps_eq_of_one_tmul`, `codRestrict_surjective_of_range_le` |
## Order

| Current implementation | Declaration anchors |
| --- | --- |
| [`ForMathlib.Order.Interval.Diamonds`](ForMathlib/Order/Interval/Diamonds.lean) | `DiamondEdges.map`, `DiamondEdges.map_iff` |
## RepresentationTheory

| Current implementation | Declaration anchors |
| --- | --- |
| [`ForMathlib.RepresentationTheory.BottSamelson.TitsWords`](ForMathlib/RepresentationTheory/BottSamelson/TitsWords.lean) | `SymmetricCoefficient`, `coefficientAction`, `coefficientAction_simple` |
| [`ForMathlib.RepresentationTheory.Hecke.Coefficients`](ForMathlib/RepresentationTheory/Hecke/Coefficients.lean) | `left_coeff`, `left_plus_coeff`, `positiveWord` |
| [`ForMathlib.RepresentationTheory.Hecke.DualR`](ForMathlib/RepresentationTheory/Hecke/DualR.lean) | `dualR`, `dualR_zero`, `dualR_recursion` |
| [`ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted`](ForMathlib/RepresentationTheory/Hecke/DyerPaths/Adapted.lean) | `Edge`, `source`, `target` |
| [`ForMathlib.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder`](ForMathlib/RepresentationTheory/Hecke/DyerPaths/LexicographicOrder.lean) | `lexRootScore`, `lexRootScore_injective`, `lexEdgeScore` |
| [`ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates`](ForMathlib/RepresentationTheory/Hecke/DyerPaths/PlaneCoordinates.lean) | `path_coordinates`, `intervalToAmbient`, `intervalToAmbient_injective` |
| [`ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall`](ForMathlib/RepresentationTheory/Hecke/DyerPaths/Wall.lean) | `rootValue`, `rootPlaneTies`, `schedule` |
| [`ForMathlib.RepresentationTheory.Hecke.Inverse`](ForMathlib/RepresentationTheory/Hecke/Inverse.lean) | `bar_coeff_inverse`, `rValue_inverse_factor`, `rValue_inverse` |
| [`ForMathlib.RepresentationTheory.Hecke.Operators`](ForMathlib/RepresentationTheory/Hecke/Operators.lean) | `Space`, `basis`, `end_ext` |
| [`ForMathlib.RepresentationTheory.Hecke.OrdinaryR`](ForMathlib/RepresentationTheory/Hecke/OrdinaryR.lean) | `variableUnit`, `rValue_polynomial`, `polynomial` |
| [`ForMathlib.RepresentationTheory.Hecke.PositiveWord`](ForMathlib/RepresentationTheory/Hecke/PositiveWord.lean) | `one_add_leftInv`, `barLinear_positiveWord`, `positiveWord_support` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Canonical.lean) | `polynomial`, `polynomial_zero`, `defect` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Dihedral`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Dihedral.lean) | `lowerSum`, `double_string`, `left_plus_coeff` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.FiniteRankReduction`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/FiniteRankReduction.lean) | `FiniteIntervalModel`, `exists_finiteIntervalModel`, `intervalEndpointCongr` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.IntervalTransport`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/IntervalTransport.lean) | `rankDifference_subinterval_lt`, `rTilde_transport_all`, `scaledKL_eq_scaledPolynomial` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Normalization.lean) | `rPolynomial_normalization`, `scaledKL`, `scaledKL_reciprocity_inverse` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Normalized.lean) | `PolynomialFamilies`, `NormalizedKL`, `klFamilies` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Parabolic.lean) | `normalized_restriction`, `klFamilies_inclusion`, `klPolynomial_inclusion` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/ScaledReciprocity.lean) | `scaledKL_reciprocity_upper` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/SelectedR.lean) | `rPolynomial` |
| [`ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Unique`](ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Unique.lean) | `normalized_R_unique`, `normalized_P_unique`, `normalizedKL_unique` |
## RingTheory

| Current implementation | Declaration anchors |
| --- | --- |
| [`ForMathlib.RingTheory.Localization.RelativePrime`](ForMathlib/RingTheory/Localization/RelativePrime.lean) | `not_dvd_map`, `map_prime`, `map_relPrime` |
## Application / compatibility implementation

| Current implementation | Declaration anchors |
| --- | --- |
| [`OAI.KL.BottSamelson.AdjointSheaf`](OAI/KL/BottSamelson/AdjointSheaf.lean) | `symmetricCoefficientNoetherian`, `bottVertexProjection`, `bottVertexProjection_injective` |
| [`OAI.KL.BottSamelson.CanonicalPairing`](OAI/KL/BottSamelson/CanonicalPairing.lean) | `bottCanonicalAdjointHom`, `bottCanonicalAdjointHom_top_bijective`, `bottCanonicalAdjointIso` |
| [`OAI.KL.BottSamelson.Character`](OAI/KL/BottSamelson/Character.lean) | `bottSplitRightWord`, `bottSplitLeftWord`, `bottSplitRightWord_coordinates` |
| [`OAI.KL.BottSamelson.CharacterDecomposition`](OAI/KL/BottSamelson/CharacterDecomposition.lean) | `bottCharacter_decomposition_both` |
| [`OAI.KL.BottSamelson.Flabby`](OAI/KL/BottSamelson/Flabby.lean) | `bottStalk_subsingleton_of_not_bruhat`, `intervalUpperClosure`, `intervalUpperClosure_upper` |
| [`OAI.KL.BottSamelson.StalkCharacter`](OAI/KL/BottSamelson/StalkCharacter.lean) | `bottStalk_finrank_descent`, `bottStalkCharacter_ascent`, `bottStalkCharacter_descent` |
| [`OAI.KL.BottSamelson.Stalks`](OAI/KL/BottSamelson/Stalks.lean) | `bottWeightProjection_range_le`, `bottTensor_maps_eq`, `bottFullIndex` |
| [`OAI.KL.BottSamelson.Support`](OAI/KL/BottSamelson/Support.lean) | `symmetricGrading_zero`, `bottSupported_of_stalkSupport`, `bottStalk_supported_annihilates` |
| [`OAI.KL.BottSamelson.UpperSections`](OAI/KL/BottSamelson/UpperSections.lean) | `reflection_character_congruence_iff`, `reflection_character_separates`, `isReflection_of_prime_character_congruence` |
| [`OAI.KL.Comparison.Propagation`](OAI/KL/Comparison/Propagation.lean) | `actual_edge_increment_le`, `actual_edge_increment_eq_iff`, `partial_kernel_projective_of_image_eq` |
| [`OAI.KL.Comparison.SuffixFreeness`](OAI/KL/Comparison/SuffixFreeness.lean) | `no_conditions_free`, `schedule_kernels_free_of_images_eq`, `schedule_kernels_free_of_endpoint_eq` |
| [`OAI.KL.Comparison.Transport`](OAI/KL/Comparison/Transport.lean) | `boundarySheaf_gradedIso`, `stalkCharacter_eq_character`, `upperInclusion` |
| [`OAI.KL.Compatibility.KernelTransport`](OAI/KL/Compatibility/KernelTransport.lean) | `kernelSourceEquiv`, `kernelTargetEquiv`, `kernelMixedEquiv` |
| [`OAI.KL.Invariance.Finite`](OAI/KL/Invariance/Finite.lean) | `comparison_of_source02`, `comparison_difference_le`, `bottom_eq_of_comparisons` |
| [`OAI.KL.Invariance.Main`](OAI/KL/Invariance/Main.lean) | `combinatorial_invariance` |
| [`OAI.KL.Localization.Ambient`](OAI/KL/Localization/Ambient.lean) | `exists_outgoing_below`, `polynomialRoot`, `polynomialRoot_homogeneous` |
| [`OAI.KL.Localization.Edge`](OAI/KL/Localization/Edge.lean) | `EdgeRing`, `edgeRingEquiv`, `edgeRing_isDomain` |
| [`OAI.KL.Localization.GraphEmbedding`](OAI/KL/Localization/GraphEmbedding.lean) | `embedLinear`, `embedLinear_injective`, `planePrime` |
| [`OAI.KL.Localization.Plane`](OAI/KL/Localization/Plane.lean) | `CosetVertex`, `cosetOrder`, `cosetAmbient` |
| [`OAI.KL.Localization.TerminalImages`](OAI/KL/Localization/TerminalImages.lean) | `localized_boundary_decomposition`, `scheduledLower_root_ne`, `outgoingUpper_root_ne` |
| [`OAI.KL.Sheaves.Boundary`](OAI/KL/Sheaves/Boundary.lean) | `Coefficient`, `root`, `polynomialLabel` |
| [`OAI.KL.Sheaves.FreeModel`](OAI/KL/Sheaves/FreeModel.lean) | `SectionDualityObligation`, `sectionDualityObligation_of_perfectPairing`, `FreeSheaf` |
| [`OAI.KL.Sheaves.LowerCharacter`](OAI/KL/Sheaves/LowerCharacter.lean) | `lowerCharacter`, `boundaryModels_character`, `lowerCharacter_zero` |
| [`OAI.KL.Sheaves.Reciprocity`](OAI/KL/Sheaves/Reciprocity.lean) | `boundarySheaf_perfectPairing`, `sectionDualityObligation`, `boundaryFreeSheaf` |
| [`OAI.KL.Sheaves.StalkReciprocity`](OAI/KL/Sheaves/StalkReciprocity.lean) | `stalkCharacter_reciprocity` |
| [`OAI.KL.Sheaves.Support`](OAI/KL/Sheaves/Support.lean) | `incomingEquivInversions`, `incoming_card`, `root_injective_on_labels` |

## Published compatibility imports

These files contain imports only; implementations use current homes directly.

| Compatibility path | Current imports |
| --- | --- |
| [`ForMathlib.Algebra.BigOperators.FiniteCharacterCancellation`](ForMathlib/Algebra/BigOperators/FiniteCharacterCancellation.lean) | `ForMathlib.Algebra.BigOperators.SingleCoordinate` |
| [`ForMathlib.Algebra.Module.Cover.Product`](ForMathlib/Algebra/Module/Cover/Product.lean) | `ForMathlib.Algebra.Module.Submodule.PiIdeal` |
| [`ForMathlib.Algebra.Module.Graded.AlgebraMap`](ForMathlib/Algebra/Module/Graded/AlgebraMap.lean) | `ForMathlib.Algebra.Module.Graded.Basis`, `ForMathlib.Algebra.Module.Graded.PolynomialMap`, `ForMathlib.Algebra.Module.Graded.HomogeneousMul`, `ForMathlib.Algebra.Module.Graded.Generators` |
| [`ForMathlib.Algebra.Module.Graded.DualAndShift`](ForMathlib/Algebra/Module/Graded/DualAndShift.lean) | `ForMathlib.Algebra.Module.Graded.HomogeneousEquiv`, `ForMathlib.Algebra.Module.Graded.FinitePieces`, `ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection`, `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic`, `ForMathlib.Algebra.Module.CoefficientChange.Basic`, `ForMathlib.Algebra.Module.Graded.AlgebraMap`, `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`, `ForMathlib.LinearAlgebra.PairProjection` |
| [`ForMathlib.Algebra.Module.Graded.Hilbert.RationalFunction`](ForMathlib/Algebra/Module/Graded/Hilbert/RationalFunction.lean) | `ForMathlib.Algebra.Module.Graded.Hilbert.Numerator` |
| [`ForMathlib.Algebra.Module.Localization.Products`](ForMathlib/Algebra/Module/Localization/Products.lean) | `ForMathlib.Algebra.Module.Submodule.ProductScaling` |
| [`ForMathlib.Algebra.Polynomial.ScaledReciprocity`](ForMathlib/Algebra/Polynomial/ScaledReciprocity.lean) | `ForMathlib.Algebra.Polynomial.ScaledEvaluation`, `ForMathlib.Algebra.BigOperators.SingleCoordinate` |
| [`ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Basic`](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Basic.lean) | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties`, `ForMathlib.Algebra.Module.Graded.ModuleData.Equality`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Extension`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Extension.lean) | `ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Restriction`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Isomorphism`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Isomorphism.lean) | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi`, `ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion`, `ForMathlib.Algebra.Module.Cover.Local`, `ForMathlib.Algebra.Module.Cover.Product`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Basic`, `ForMathlib.LinearAlgebra.Quotient.Transport` |
| [`ForMathlib.Combinatorics.MomentGraph.Sheaf.Zero`](ForMathlib/Combinatorics/MomentGraph/Sheaf/Zero.lean) | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Products`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Isomorphism` |
| [`ForMathlib.LinearAlgebra.Reflection.Forms`](ForMathlib/LinearAlgebra/Reflection/Forms.lean) | `ForMathlib.LinearAlgebra.Reflection.Bilinear`, `ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension` |
| [`OAI.KL.BottSamelson.Pairings`](OAI/KL/BottSamelson/Pairings.lean) | `OAI.KL.BottSamelson.UpperSections`, `OAI.KL.BottSamelson.StalkCharacter`, `OAI.KL.BottSamelson.Flabby`, `ForMathlib.Algebra.Module.Graded.Hilbert.RationalFunction`, `ForMathlib.Algebra.Module.Localization.FiniteCharacters`, `ForMathlib.Algebra.Module.Localization.ProjectiveLattice`, `ForMathlib.Algebra.Module.Projective.Range`, `ForMathlib.Algebra.Module.ReflectionPair.TensorDescent`, `ForMathlib.LinearAlgebra.KernelCoordinates`, `ForMathlib.LinearAlgebra.PairProjection`, `ForMathlib.LinearAlgebra.Reflection.Classification`, `ForMathlib.RepresentationTheory.Hecke.Coefficients`, `OAI.KL.BottSamelson.Stalks` |
| [`OAI.LinearAlgebra.KernelTransport`](OAI/LinearAlgebra/KernelTransport.lean) | `ForMathlib.LinearAlgebra.KernelTransport` |
| [`OAI.RepresentationTheory.KazhdanLusztig.BalancedPairings`](OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean) | `ForMathlib.Algebra.Module.Graded.ModuleData.Range`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Summand`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand`, `ForMathlib.LinearAlgebra.ConjugateRange`, `ForMathlib.LinearAlgebra.Dual.Adjoint`, `ForMathlib.LinearAlgebra.Dual.Summand`, `ForMathlib.LinearAlgebra.Dual.TransportPairing`, `ForMathlib.LinearAlgebra.Quotient.Transport`, `OAI.KL.BottSamelson.AdjointSheaf`, `OAI.RepresentationTheory.KazhdanLusztig.IntegralPairings` |
| [`OAI.RepresentationTheory.KazhdanLusztig.BottSamelson`](OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean) | `ForMathlib.Algebra.Module.CoefficientChange.Basic`, `ForMathlib.Algebra.Module.Free.ScalarDivisibility`, `ForMathlib.Algebra.Module.Graded.HomogeneousEquiv`, `ForMathlib.Algebra.Module.Graded.FinitePieces`, `ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection`, `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic`, `ForMathlib.Algebra.Module.ReflectionPair.TensorKernel`, `ForMathlib.LinearAlgebra.TensorProduct.Coordinates`, `OAI.KL.BottSamelson.Stalks`, `OAI.KL.Compatibility.KernelTransport`, `OAI.RepresentationTheory.KazhdanLusztig.Frobenius` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Bruhat`](OAI/RepresentationTheory/KazhdanLusztig/Bruhat.lean) | `ForMathlib.Algebra.Polynomial.Reciprocal`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Unique`, `OAI.RepresentationTheory.KazhdanLusztig.Coxeter`, `OAI.RepresentationTheory.KazhdanLusztig.Model` |
| [`OAI.RepresentationTheory.KazhdanLusztig.CanonicalKL`](OAI/RepresentationTheory/KazhdanLusztig/CanonicalKL.lean) | `ForMathlib.Algebra.Polynomial.LowPart`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`, `OAI.RepresentationTheory.KazhdanLusztig.OrdinaryR` |
| [`OAI.RepresentationTheory.KazhdanLusztig.CharacterReciprocity`](OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean) | `ForMathlib.Algebra.Module.Graded.ModuleData.CharacterDual`, `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Models`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Models`, `ForMathlib.LinearAlgebra.Dual.BalancedCut`, `ForMathlib.RepresentationTheory.Hecke.PositiveWord`, `OAI.KL.BottSamelson.Character`, `OAI.KL.BottSamelson.CharacterDecomposition`, `OAI.KL.Sheaves.FreeModel`, `OAI.KL.Sheaves.Reciprocity`, `OAI.RepresentationTheory.KazhdanLusztig.Support` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Comparison`](OAI/RepresentationTheory/KazhdanLusztig/Comparison.lean) | `ForMathlib.Algebra.Polynomial.Reciprocal`, `ForMathlib.Combinatorics.DirectedPaths.PositiveTransfer`, `Mathlib` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Coxeter`](OAI/RepresentationTheory/KazhdanLusztig/Coxeter.lean) | `ForMathlib.GroupTheory.Coxeter.Exchange`, `Mathlib` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Decomposition`](OAI/RepresentationTheory/KazhdanLusztig/Decomposition.lean) | `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds`, `ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`, `ForMathlib.LinearAlgebra.PairProjection`, `OAI.KL.Sheaves.LowerCharacter`, `OAI.RepresentationTheory.KazhdanLusztig.SheafMorphisms` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Dihedral`](OAI/RepresentationTheory/KazhdanLusztig/Dihedral.lean) | `ForMathlib.GroupTheory.Coxeter.Bruhat.Transport`, `ForMathlib.GroupTheory.Coxeter.Dihedral.Words`, `ForMathlib.RepresentationTheory.Hecke.DualR`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Dihedral`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`, `OAI.RepresentationTheory.KazhdanLusztig.CanonicalKL` |
| [`OAI.RepresentationTheory.KazhdanLusztig.DihedralIntervals`](OAI/RepresentationTheory/KazhdanLusztig/DihedralIntervals.lean) | `ForMathlib.Combinatorics.Dihedral.SignedCount`, `ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel`, `ForMathlib.Combinatorics.MomentGraph.Bruhat.PlaneModel`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown`, `ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords`, `ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder`, `ForMathlib.GroupTheory.Coxeter.Roots.LaterCount`, `ForMathlib.GroupTheory.Coxeter.Roots.Splines`, `OAI.RepresentationTheory.KazhdanLusztig.ReflectionOrders` |
| [`OAI.RepresentationTheory.KazhdanLusztig.DyerPaths`](OAI/RepresentationTheory/KazhdanLusztig/DyerPaths.lean) | `ForMathlib.Algebra.BigOperators.SingleCoordinate`, `ForMathlib.Combinatorics.DirectedPaths.Subpaths`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds`, `ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport`, `ForMathlib.GroupTheory.Coxeter.Parabolic.InversionList`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport`, `ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted`, `OAI.KL.Sheaves.StalkReciprocity`, `OAI.RepresentationTheory.KazhdanLusztig.CharacterReciprocity` |
| [`OAI.RepresentationTheory.KazhdanLusztig.EdgeLocalization`](OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean) | `ForMathlib.Algebra.Module.Graded.ModuleData.CoverUniqueness`, `ForMathlib.Algebra.Module.Graded.RegularScalar`, `ForMathlib.Combinatorics.DirectedPaths.ScalarMap`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Uniqueness`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Uniqueness`, `ForMathlib.LinearAlgebra.Dual.IntegralSupport`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity`, `OAI.KL.BottSamelson.CanonicalPairing`, `OAI.KL.Comparison.Transport`, `OAI.RepresentationTheory.KazhdanLusztig.PlaneLocalization` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Frobenius`](OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean) | `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis`, `ForMathlib.Algebra.Module.Graded.Basis`, `ForMathlib.Algebra.Module.Graded.PolynomialMap`, `ForMathlib.Algebra.Module.Graded.HomogeneousMul`, `ForMathlib.Algebra.Module.ReflectionPair.Twist`, `ForMathlib.LinearAlgebra.Dual.Frobenius`, `ForMathlib.LinearAlgebra.PairProjection`, `ForMathlib.RepresentationTheory.BottSamelson.TitsWords`, `OAI.RepresentationTheory.KazhdanLusztig.Decomposition` |
| [`OAI.RepresentationTheory.KazhdanLusztig.GradedModules`](OAI/RepresentationTheory/KazhdanLusztig/GradedModules.lean) | `ForMathlib.Algebra.Module.Graded.Generators`, `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`, `ForMathlib.Algebra.Module.Projective.ScalarQuotient`, `OAI.RepresentationTheory.KazhdanLusztig.ModuleAlgebra` |
| [`OAI.RepresentationTheory.KazhdanLusztig.GradedSheaves`](OAI/RepresentationTheory/KazhdanLusztig/GradedSheaves.lean) | `ForMathlib.Algebra.Module.Submodule.PiIdeal`, `ForMathlib.Algebra.Module.Graded.ModuleData.Equality`, `ForMathlib.Algebra.Module.Submodule.ScaledImage`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Basic`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi`, `ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion`, `ForMathlib.LinearAlgebra.Quotient.Transport`, `OAI.RepresentationTheory.KazhdanLusztig.GradedModules`, `OAI.RepresentationTheory.KazhdanLusztig.ReflectionSchedules`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Hecke`](OAI/RepresentationTheory/KazhdanLusztig/Hecke.lean) | `ForMathlib.Algebra.Polynomial.Reciprocal`, `ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset`, `ForMathlib.RepresentationTheory.Hecke.Inverse`, `ForMathlib.RepresentationTheory.Hecke.Operators`, `OAI.RepresentationTheory.KazhdanLusztig.Bruhat` |
| [`OAI.RepresentationTheory.KazhdanLusztig.HilbertSeries`](OAI/RepresentationTheory/KazhdanLusztig/HilbertSeries.lean) | `ForMathlib.Algebra.Module.Graded.Hilbert.Series`, `OAI.RepresentationTheory.KazhdanLusztig.GradedSheaves` |
| [`OAI.RepresentationTheory.KazhdanLusztig.IntegralPairings`](OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean) | `ForMathlib.Algebra.Module.Graded.Adjoint`, `ForMathlib.Algebra.Module.Graded.Hilbert.Numerator`, `ForMathlib.Algebra.Module.Localization.FiniteCharacters`, `ForMathlib.Algebra.Module.Localization.ProjectiveLattice`, `ForMathlib.Algebra.Module.Projective.Range`, `ForMathlib.Algebra.Module.Projective.Transport`, `ForMathlib.Algebra.Module.ReflectionPair.TensorDescent`, `ForMathlib.LinearAlgebra.CoordinateProjection`, `ForMathlib.LinearAlgebra.Dual.Adjoint`, `ForMathlib.LinearAlgebra.KernelCoordinates`, `ForMathlib.LinearAlgebra.PairProjection`, `ForMathlib.LinearAlgebra.Reflection.Classification`, `ForMathlib.RepresentationTheory.Hecke.Coefficients`, `OAI.KL.BottSamelson.UpperSections`, `OAI.KL.BottSamelson.StalkCharacter`, `OAI.KL.BottSamelson.Flabby`, `OAI.RepresentationTheory.KazhdanLusztig.BottSamelson` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Invariance`](OAI/RepresentationTheory/KazhdanLusztig/Invariance.lean) | `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.FiniteRankReduction`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.IntervalTransport`, `OAI.KL.Invariance.Finite`, `OAI.KL.Invariance.Main`, `OAI.RepresentationTheory.KazhdanLusztig.SimultaneousInvariance` |
| [`OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat`](OAI/RepresentationTheory/KazhdanLusztig/KernelTransportCompat.lean) | `OAI.KL.Compatibility.KernelTransport` |
| [`OAI.RepresentationTheory.KazhdanLusztig.MinimalExtensions`](OAI/RepresentationTheory/KazhdanLusztig/MinimalExtensions.lean) | `ForMathlib.Algebra.Module.Graded.ModuleData.Transport`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Extension`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Restriction`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Products`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback`, `OAI.RepresentationTheory.KazhdanLusztig.Comparison`, `OAI.RepresentationTheory.KazhdanLusztig.HilbertSeries` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Model`](OAI/RepresentationTheory/KazhdanLusztig/Model.lean) | `ForMathlib.GroupTheory.Coxeter.Bruhat.Defs`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`, `Mathlib` |
| [`OAI.RepresentationTheory.KazhdanLusztig.ModuleAlgebra`](OAI/RepresentationTheory/KazhdanLusztig/ModuleAlgebra.lean) | `ForMathlib.Algebra.Module.Cover.Local`, `ForMathlib.Algebra.Module.Graded.Components`, `ForMathlib.Algebra.Module.Graded.Hilbert.Basic`, `ForMathlib.Algebra.Module.Localization.Lattice`, `ForMathlib.Algebra.Module.Projective.ReverseFiltration`, `ForMathlib.Algebra.Module.Quotient.KernelReduction`, `Mathlib` |
| [`OAI.RepresentationTheory.KazhdanLusztig.OrdinaryR`](OAI/RepresentationTheory/KazhdanLusztig/OrdinaryR.lean) | `ForMathlib.RepresentationTheory.Hecke.OrdinaryR`, `OAI.RepresentationTheory.KazhdanLusztig.Hecke` |
| [`OAI.RepresentationTheory.KazhdanLusztig.PlaneLocalization`](OAI/RepresentationTheory/KazhdanLusztig/PlaneLocalization.lean) | `ForMathlib.Algebra.Module.Submodule.ProductScaling`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Localization`, `ForMathlib.LinearAlgebra.PlaneReduction`, `ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient`, `ForMathlib.RingTheory.Localization.RelativePrime`, `OAI.KL.Localization.Ambient`, `OAI.KL.Localization.GraphEmbedding`, `OAI.KL.Localization.Plane`, `OAI.RepresentationTheory.KazhdanLusztig.DihedralIntervals` |
| [`OAI.RepresentationTheory.KazhdanLusztig.PositiveTransfer`](OAI/RepresentationTheory/KazhdanLusztig/PositiveTransfer.lean) | `ForMathlib.Algebra.BigOperators.SingleCoordinate`, `ForMathlib.Algebra.Module.Graded.Hilbert.Increment`, `ForMathlib.Algebra.Module.Projective.ScalarKernel`, `ForMathlib.Algebra.Order.Field.RealScaling`, `ForMathlib.Algebra.Polynomial.ScaledEvaluation`, `ForMathlib.Algebra.Polynomial.TransferEvaluation`, `ForMathlib.Combinatorics.DirectedPaths.Monotone`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hilbert`, `OAI.KL.Comparison.Propagation`, `OAI.RepresentationTheory.KazhdanLusztig.EdgeLocalization` |
| [`OAI.RepresentationTheory.KazhdanLusztig.ReflectionOrders`](OAI/RepresentationTheory/KazhdanLusztig/ReflectionOrders.lean) | `ForMathlib.Combinatorics.DirectedPaths.SortedSchedule`, `ForMathlib.Combinatorics.DirectedPaths.Transfer`, `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder`, `ForMathlib.LinearAlgebra.Avoidance`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall`, `OAI.RepresentationTheory.KazhdanLusztig.DyerPaths` |
| [`OAI.RepresentationTheory.KazhdanLusztig.ReflectionPlane`](OAI/RepresentationTheory/KazhdanLusztig/ReflectionPlane.lean) | `ForMathlib.LinearAlgebra.Reflection.Plane`, `Mathlib` |
| [`OAI.RepresentationTheory.KazhdanLusztig.ReflectionSchedules`](OAI/RepresentationTheory/KazhdanLusztig/ReflectionSchedules.lean) | `ForMathlib.Combinatorics.DirectedPaths.Basic`, `ForMathlib.GroupTheory.Coxeter.Bruhat.DiamondClosure`, `ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds`, `ForMathlib.GroupTheory.Coxeter.Roots.Order`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength`, `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionLabels`, `ForMathlib.LinearAlgebra.Avoidance`, `ForMathlib.LinearAlgebra.Reflection.Plane`, `ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal`, `ForMathlib.Order.Interval.Diamonds`, `OAI.RepresentationTheory.KazhdanLusztig.ModuleAlgebra`, `OAI.RepresentationTheory.KazhdanLusztig.Tits` |
| [`OAI.RepresentationTheory.KazhdanLusztig.SheafMorphisms`](OAI/RepresentationTheory/KazhdanLusztig/SheafMorphisms.lean) | `ForMathlib.Algebra.Module.Graded.ModuleData.Character`, `ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover`, `ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom`, `ForMathlib.Algebra.Module.Graded.NonnegativeBasis`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Hom`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Hom`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Descent`, `ForMathlib.LinearAlgebra.Quotient.Transport`, `OAI.KL.Sheaves.Boundary`, `OAI.RepresentationTheory.KazhdanLusztig.MinimalExtensions` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Sheaves`](OAI/RepresentationTheory/KazhdanLusztig/Sheaves.lean) | `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`, `Mathlib` |
| [`OAI.RepresentationTheory.KazhdanLusztig.SimultaneousInvariance`](OAI/RepresentationTheory/KazhdanLusztig/SimultaneousInvariance.lean) | `ForMathlib.Algebra.BigOperators.SingleCoordinate`, `ForMathlib.Algebra.Order.Field.RealScaling`, `ForMathlib.Algebra.Polynomial.ScaledEvaluation`, `ForMathlib.Algebra.Polynomial.TransferEvaluation`, `OAI.KL.Comparison.SuffixFreeness`, `OAI.RepresentationTheory.KazhdanLusztig.TerminalKernels` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Support`](OAI/RepresentationTheory/KazhdanLusztig/Support.lean) | `ForMathlib.Algebra.Module.CoefficientChange.Dual`, `ForMathlib.Algebra.Module.Graded.Hilbert.Images`, `ForMathlib.Algebra.Module.Graded.HomogeneousDual`, `ForMathlib.Algebra.Module.Graded.ModuleData.Duality`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality`, `ForMathlib.LinearAlgebra.Dual.BalancedCut`, `ForMathlib.LinearAlgebra.Dual.IntegralSupport`, `OAI.KL.BottSamelson.Support`, `OAI.KL.Sheaves.Support`, `OAI.RepresentationTheory.KazhdanLusztig.BalancedPairings` |
| [`OAI.RepresentationTheory.KazhdanLusztig.TerminalKernels`](OAI/RepresentationTheory/KazhdanLusztig/TerminalKernels.lean) | `ForMathlib.Algebra.Module.Flat.Kernel`, `ForMathlib.Algebra.Module.Localization.Membership`, `ForMathlib.Algebra.Module.Quotient.ScalarImage`, `ForMathlib.Combinatorics.DirectedPaths.Suffix`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages`, `OAI.KL.Localization.Edge`, `OAI.KL.Localization.TerminalImages`, `OAI.RepresentationTheory.KazhdanLusztig.PositiveTransfer` |
| [`OAI.RepresentationTheory.KazhdanLusztig.Tits`](OAI/RepresentationTheory/KazhdanLusztig/Tits.lean) | `ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic`, `ForMathlib.GroupTheory.Coxeter.Parabolic.Standard`, `ForMathlib.GroupTheory.Coxeter.Parabolic.Support`, `ForMathlib.GroupTheory.Coxeter.Realization.Cotangent`, `ForMathlib.GroupTheory.Coxeter.Realization.Faithful`, `ForMathlib.GroupTheory.Coxeter.Realization.Geometric`, `ForMathlib.GroupTheory.Coxeter.Realization.Positivity`, `ForMathlib.GroupTheory.Coxeter.Realization.Tits`, `ForMathlib.GroupTheory.Coxeter.Roots.Basic`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup`, `ForMathlib.LinearAlgebra.Reflection.Bilinear`, `ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic`, `OAI.RepresentationTheory.KazhdanLusztig.Bruhat`, `OAI.RepresentationTheory.KazhdanLusztig.Dihedral`, `OAI.RepresentationTheory.KazhdanLusztig.ReflectionPlane`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves` |
