# Lean formalization

The offline project is in `project/lean`. Build with:

```sh
cd project/lean
lake build
```

All public declarations are in namespace `HGPExperiment`. The intended downstream import is `HGPExperiment`.

| Source target | Module | Declarations |
| --- | --- | --- |
| A: actual checks, commutation, length, logical dimensions, representative distance bound | `HGPExperiment.Parameters` | `xChecks`, `zChecks`, `checks_commute`, `hgp_length`, `ZLogical`, `XLogical`, `zLogical_dimension`, `xLogical_dimension`, `hgpDistance`, `hgp_distance_lower`, `logical_representative_lower`, `zClass_representative_lower`, `xClass_representative_lower`, `zero_code_distance` |
| B: actual supported quotient images, two rank identities | `HGPExperiment.Erasure` | `coordinateSpace`, `cycles`, `boundaries`, `supportedLogical`, `supportedDim`, `zDim`, `xDim`, `restrictColumns`, `zDim_rank_identity`, `xDim_rank_identity`, `logicalDim`, `logicalDim_add_ranks`, `logicalDim_eq_length_sub_ranks`, `logicalDim_swap`, `zDim_add_xDim_compl`, `xDim_add_zDim_compl` |
| B: equivalence with the supported image inside the cycle quotient | `HGPExperiment.LogicalSemantics` | `LogicalQuotient`, `supportedWithin`, `supportedLogicalEquiv`, `supportedDim_eq_finrank_within` |
| C: error pairs, syndromes, equivalence, failure and least failing erasure | `HGPExperiment.Inference` | `ErrorPair`, `syndrome`, `errorEquivalent`, `erasureSucceeds`, `erasureFails`, `erasureSucceeds_iff`, `erasureFails_iff`, `matrixCSSDistance`, `erasureDistance`, `erasureDistance_eq_cssDistance`, `erasureDistance_eq_top_iff` |
| A–C: connection between the matrix erasure model and the supplied HGP parameter theorem | `HGPExperiment.Integration` | `cycles_xChecks`, `cycles_zChecks`, `boundaries_xChecks`, `boundaries_zChecks`, `matrixLogical_iff_qec`, `matrixCSSDistance_eq_hgpDistance`, `hgp_erasureDistance`, `hgp_small_erasure_succeeds`, `logicalDim_hgp` |

Work in progress: the universal strip formulas D and the final concrete call sites E. This record will be updated after the final build.
