import HGPExperiment.Erasure

noncomputable section
namespace HGPExperiment

variable {C R : Type*} [Fintype C] [Fintype R]

/-- Coordinate restriction, with its actual image used for puncturing. -/
def coordinateRestriction (S : Set C) : (C → F₂) →ₗ[F₂] (S → F₂) where
  toFun v s := v s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_coordinateRestriction (S : Set C) :
    LinearMap.ker (coordinateRestriction S) = supportSpace Sᶜ := by
  classical
  ext v
  constructor
  · intro h q hq
    have hmem : q ∈ S := by simpa using hq
    exact congrFun h ⟨q, hmem⟩
  · intro h
    change coordinateRestriction S v = 0
    funext q
    exact h q (by simpa using q.property)

/-- Puncturing a kernel and shortening its row space have complementary dimensions. -/
theorem finrank_restricted_kernel_add_finrank_supported_rows
    (H : Matrix R C F₂) (S : Set C) [Fintype S] :
    Module.finrank F₂ ((cycles H).map (coordinateRestriction S)) +
      Module.finrank F₂ (boundaries H ⊓ supportSpace S) = Fintype.card S := by
  classical
  letI : Fintype Sᶜ := Fintype.ofFinite Sᶜ
  have hi := finrank_map_add_finrank_inf_ker (coordinateRestriction S) (cycles H)
  rw [ker_coordinateRestriction] at hi
  have hc := finrank_cycles_inf_support_add_rank H Sᶜ
  have hb := finrank_boundaries_inf_support_add_rank H S
  have hg := (Matrix.toLin' H).finrank_range_add_finrank_ker
  have hr : Module.finrank F₂ (LinearMap.range (Matrix.toLin' H)) = H.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_toLin']
  rw [hr] at hg
  have hcard := Fintype.card_subtype_compl (fun c => c ∈ S)
  have hle := Fintype.card_subtype_le (fun c => c ∈ S)
  change H.rank + Module.finrank F₂ (cycles H) = Fintype.card C at hg
  omega

end HGPExperiment
