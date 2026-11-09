# Graded / reflection API discovery

This index covers the fourth through sixth experiments. Definitions remain exposed. Existing
APIs from the earlier experiments are linked from the project README.

| Operation | Semantic entry points | Real clients |
| --- | --- | --- |
| Graded sheaf morphisms and sections | `Hom.comp_vertex_apply`, `comp_edge_apply`; `Hom.sectionMap_comp`, `sectionMap_id` | `SplitIn.projection_comp_inclusion`, `sections_split` |
| Induced maps on ranges | `rangeMap_projection` is the commuting square with range projections; `rangeMap_val`, `rangeProjection_val`, `rangeInclusion_apply` evaluate its underlying vectors | `Hom.imageInclusion`, `imageProjection` |
| Idempotents and splittings | `range_fixed` says an idempotent fixes its range; `SplitIn.projection_comp_inclusion` is the retraction law; `projector_apply_vertex/edge` evaluate the projector | `Hom.imageSplit`, `imageSection_fixed`; existing projector idempotence proofs |
| Twisted lattices | `Twist.val_add`, `val_smul`; `mem_lattice_iff` gives common lifts; `left_apply`, `right_apply` give the projections; `kernelMap_snd_val`, `rightKernelMap_fst` give multiplication by α on the kernel coordinate | Saturation, both kernel surjectivity/injectivity arguments |
| Reflected tensor maps | `twistMap_val`; `tensorFirst_natural`, `tensorSecond_natural` for arbitrary A-linear maps | Existing endomorphism APIs `tensorFirst_map`, `tensorSecond_map`; `tensor_difference`, `twistMap_injective` |

Sources:

- [ModuleData.Range](ForMathlib/Algebra/Module/Graded/ModuleData/Range.lean)
- [GradedSheaf.Summand](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean)
- [ReflectionPair.Twist](ForMathlib/Algebra/Module/ReflectionPair/Twist.lean)
- [ReflectionPair.TensorKernel](ForMathlib/Algebra/Module/ReflectionPair/TensorKernel.lean)
- [ReflectionPair.TensorDescent](ForMathlib/Algebra/Module/ReflectionPair/TensorDescent.lean)
- [KernelCoordinates](ForMathlib/LinearAlgebra/KernelCoordinates.lean)

Point evaluations simplify toward the original vector operations. Composition
of section maps, the range projection square, common-lift membership and the
fixed-point law are explicit APIs. Existing `Hom.eq_of_maps`, `Subtype.ext`,
`LinearMap.ext`, `Twist.ext` and function extensionality suffice; no new ext or
instance automation is introduced.

The tensor naturality family extends existing endomorphism laws; its current
production consumers retain those names as compatibility entry points. The
ordinary import check also verifies a composition with different source/target
modules. This is not a claim of a new cross-object production application.

## Supported sections, costalks and split operations (round 5)

This batch keeps exposed definitions and adds the following semantic boundaries.

| Family | Entry points | Production consumers |
| --- | --- | --- |
| Single support and costalk coordinates (new) | `Sheaf.singleStalkEquivSupport_val`, `apply_self`, `symm_val`; `Sheaf.kernelEquivSingleStalk_val` | Both boundary and free-model `kernelEquivSingleSupport_apply` |
| Supported duality and degree transport (new) | `Sheaf.singleSupportEquivDual_pairing`, `symm_pairing`; `GradedSheaf.singleSupportEquivDual_symm_homogeneous` | `Propagation.costalkEquivDual_pairing`, both inverse-homogeneity proofs |
| Image-section range (completion) | `Hom.imageSectionEquiv_val` | `bottImageSectionWordEquiv_coordinates` |
| Split corner algebra (completion) | `SplitIn.liftEnd_vertex_apply`, `edge_apply`, `compress_liftEnd`, `liftEnd_id` | Injectivity, composition, primitive-projector transfer in `Summand` |

The first family separates a support equivalence from multiplication by
incoming labels. Supported duality uses the section pairing for its characterization;
it does not prescribe an inverse construction. The range formula specifies the
image inclusion, while compression is a retraction law for corner extension.
Coordinate formulas and the identity corner extension are `simp` rules; pairing,
degree transport and compression remain explicit. No new `ext` or instances.
General tensor naturality already covers the inspected use sites; this round does
not claim a new cross-object tensor application.

## Morphism, range and image/corner laws (round 6)

These are completions of existing families, with no new structures or instances.

| Family | Entry points | Use and evidence |
| --- | --- | --- |
| Morphism algebra and inverse | `Hom.comp_assoc`, `id_comp`, `comp_id`, `inverse_comp`, `comp_inverse` | Association and units support corner/primitive proofs. Inverse laws support future cancellation of pointwise bijective sheaf maps; ordinary-import example composes distinct objects and takes sections. |
| Functorial ranges | `ModuleData.rangeMap_id`, `rangeMap_comp`, `rangeInclusion_comp_rangeMap` | Identity, composition and inclusion square for arbitrary commuting maps, without idempotence assumptions. Future-facing saturation; no new production cross-object application claimed. |
| Image factorization and sections | `Hom.imageInclusion_comp_imageProjection`, `imageSplit_projector`, `imageSectionMap_val` | Section-map bijectivity, `imageSectionEquiv_val`, splitting-to-image roundtrips, and `primitive_image` compose these with earlier range and section APIs. |
| Corner compression | `SplitIn.downEnd_comp`, `liftEnd_downEnd` | Compression multiplies with an intermediate projector; extension of compression is two-sided projector multiplication. `downEnd_idempotent` and `lift_down` use these explicitly; `compress_liftEnd` already supplies the retraction. |

Sources are [ModuleData.Range](ForMathlib/Algebra/Module/Graded/ModuleData/Range.lean)
and [GradedSheaf.Summand](ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean).
The locked mathlib patterns and selection decisions are documented in
[round 6 report](../../reports/api-saturation.md). Units, inverse cancellation,
range identity and image-split projector simplify by
removing operations. Associativity, composition/naturality, factorization and
projector sandwiches remain explicit, avoiding a global expansion normal form.
Existing extensionality mechanisms suffice. All definitions retain `expose`.
