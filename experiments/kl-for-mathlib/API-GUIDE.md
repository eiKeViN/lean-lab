# Graded / reflection API discovery

This index covers the fourth experiment. Definitions remain exposed. Existing
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
