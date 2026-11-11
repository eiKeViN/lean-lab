import HGPExperiment.Erasure

noncomputable section
namespace HGPExperiment
variable {F Q R : Type*} [Field F] [Fintype Q] [Fintype R]

/-- Shortening the row space and puncturing its orthogonal kernel have
complementary dimensions on a set of coordinates. -/
theorem shortened_row_add_punctured_kernel (H : Matrix R Q F) (E : Set Q)
    [Fintype E] [Fintype ↥(Eᶜ)] :
    Module.finrank F ↥(boundaries H ⊓ coordinateSpace E) +
      Module.finrank F ((cycles H).map (restrictCoords E)) = Fintype.card E := by
  classical
  have hmap := finrank_map_add_finrank_inf_ker (cycles H) (restrictCoords E)
  rw [ker_restrictCoords] at hmap
  have hker := finrank_cycles_add_rank H
  have hsupport := finrank_supported_cycles_add_rank H Eᶜ
  have hrow := finrank_supported_boundaries_add_rank H E
  have hcard : Fintype.card (E ⊕ ↥(Eᶜ)) = Fintype.card Q :=
    Fintype.card_congr (Equiv.Set.sumCompl E)
  rw [Fintype.card_sum] at hcard
  omega

/-- Kernel of the column restriction is the shortened kernel, represented on E. -/
theorem finrank_shortened_kernel (H : Matrix R Q F) (E : Set Q) [Fintype E] :
    Module.finrank F ↥(cycles H ⊓ coordinateSpace E) =
      Module.finrank F (cycles (restrictColumns H E)) := by
  have h1 := finrank_supported_cycles_add_rank H E
  have h2 := finrank_cycles_add_rank (restrictColumns H E)
  omega

end HGPExperiment
