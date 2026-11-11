import Paper.Support

/-! Rank-nullity identities for the actual supported quotient image (source.md B). -/
noncomputable section
namespace Paper
open QEC QEC.Coding QEC.Coding.HypergraphProduct Module
universe u v
variable {F : Type u} [Field F] {Q R T : Type v}
  [Fintype Q] [DecidableEq Q] [Fintype R] [Fintype T]

/-- Restriction to a coordinate subset, used for row-space puncturing in source.md B. -/
def restrictCoords (E : Finset Q) : (Q → F) →ₗ[F] ({q // q ∈ E} → F) where
  toFun v q := v q.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the complement has the supported coordinate subspace as kernel. -/
theorem ker_restrictCoords_compl (E : Finset Q) :
    LinearMap.ker (restrictCoords (F := F) Eᶜ) = supportSpace E := by
  ext v
  rw [mem_supportSpace]
  constructor
  · intro hv q hq
    exact congrFun hv ⟨q, Finset.mem_compl.mpr hq⟩
  · intro hv
    funext q
    exact hv q (Finset.mem_compl.mp q.2)

/-- Column rank equals the dimension of the check image of the coordinate subspace. -/
theorem rank_restrict_eq (M : Matrix R Q F) (E : Finset Q) :
    (restrictColumns M E).rank =
      finrank F ((supportSpace E).map (Matrix.toLin' M)) := by
  rw [supportSpace, Submodule.map_range, ← finrank_range_toLin'_eq_rank]
  congr 1
  congr 1
  ext v r
  exact congrFun (toLin'_restrictColumns M E v).symm r

/-- Row-space restriction has precisely the rank of the column-restricted matrix. -/
theorem finrank_restrict_rowSpace (M : Matrix R Q F) (E : Finset Q) :
    finrank F ((LinearMap.range (Matrix.toLin' M.transpose)).map (restrictCoords E)) =
      (restrictColumns M E).rank := by
  rw [Submodule.map_range]
  have heq : (restrictCoords (F := F) E).comp (Matrix.toLin' M.transpose) =
      Matrix.toLin' (restrictColumns M E).transpose := by
    ext v q
    rfl
  rw [heq, finrank_range_toLin'_eq_rank, Matrix.rank_transpose]

/-- Source.md B rank identity in one sector. The proof is three applications of
rank-nullity: supported cycles, supported boundaries, and the quotient image. -/
theorem supported_rank_identity (P : Matrix R Q F) (D : Matrix T Q F)
    (hDP : LinearMap.range (Matrix.toLin' D.transpose) ≤ LinearMap.ker (Matrix.toLin' P))
    (E : Finset Q) :
    supportedDim (LinearMap.ker (Matrix.toLin' P))
        (LinearMap.range (Matrix.toLin' D.transpose)) E +
      (restrictColumns P E).rank + D.rank =
        E.card + (restrictColumns D Eᶜ).rank := by
  let C := LinearMap.ker (Matrix.toLin' P)
  let B := LinearMap.range (Matrix.toLin' D.transpose)
  have hq := supportedDim_add_boundary C B E hDP
  have hc := finrank_image_add_inf_ker (supportSpace (F := F) E) (Matrix.toLin' P)
  rw [← rank_restrict_eq, finrank_supportSpace, inf_comm] at hc
  have hb := finrank_image_add_inf_ker B (restrictCoords (F := F) Eᶜ)
  rw [ker_restrictCoords_compl, finrank_restrict_rowSpace,
    finrank_range_toLin'_eq_rank, Matrix.rank_transpose] at hb
  change supportedDim C B E + _ + _ = _
  change _ + finrank F (C ⊓ supportSpace E) = _ at hc
  omega

end Paper
