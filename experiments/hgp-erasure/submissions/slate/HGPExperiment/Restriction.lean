import HGPExperiment.Erasure

namespace HGPExperiment
variable {Q X : Type*} [Fintype Q] [Fintype X]

/-- Restricting a subspace loses exactly its words supported on the complement. -/
theorem finrank_restrict_add_complement (U : Submodule F (Q → F)) (S : Set Q) :
    Module.finrank F (U.map (restrictMap S)) +
      Module.finrank F ↥(U ⊓ supportedSpace Sᶜ) = Module.finrank F U := by
  simpa only [ker_restrictMap] using finrank_map_add_inf_ker U (restrictMap S)

/-- The restriction of the input kernel and the shortened row space have
complementary dimensions on S. This also covers empty S and dependent rows. -/
theorem restriction_kernel_finrank_add_supported_row (H : Matrix X Q F) (S : Set Q) :
    Module.finrank F ((cycles H).map (restrictMap S)) +
      Module.finrank F ↥(boundaries H ⊓ supportedSpace S) = Nat.card S := by
  classical
  have hres := finrank_restrict_add_complement (cycles H) S
  have hker := cycles_supported_finrank H Sᶜ
  have hrow := boundaries_supported_finrank H S
  have htotal := H.mulVecLin.finrank_range_add_finrank_ker
  have hrank : Module.finrank F H.mulVecLin.range = H.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_mulVecLin]
  change Module.finrank F H.mulVecLin.range + Module.finrank F (cycles H) = _ at htotal
  rw [hrank, Module.finrank_pi] at htotal
  have hcard : Nat.card S + Nat.card Sᶜ = Fintype.card Q := by
    have hs := Fintype.card_subtype_le (fun q : Q => q ∈ S)
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    omega
  omega

end HGPExperiment
