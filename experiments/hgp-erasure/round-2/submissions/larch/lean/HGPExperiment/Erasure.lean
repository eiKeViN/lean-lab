import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! Logical information supported in a coordinate erasure, for arbitrary CSS checks.
The quotient image below is an actual subspace of the ambient space modulo boundaries.
When boundaries lie in cycles this is canonically the image in cycles/boundaries. -/
namespace HGPExperiment

variable {F Q R S : Type*} [Field F] [Fintype Q]

/-- Words vanishing outside the erasure. -/
def coordinateSpace (E : Set Q) : Submodule F (Q → F) where
  carrier := {v | ∀ q, q ∉ E → v q = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy q hq; simp [hx q hq, hy q hq]
  smul_mem' := by intro a x hx q hq; simp [hx q hq]

@[simp] theorem mem_coordinateSpace (E : Set Q) (v : Q → F) :
    v ∈ coordinateSpace (F := F) E ↔ ∀ q, q ∉ E → v q = 0 := Iff.rfl

/-- The parity-check kernel. -/
def cycles (P : Matrix R Q F) : Submodule F (Q → F) := LinearMap.ker P.mulVecLin

/-- The row space of a check matrix, including dependent rows. -/
def boundaries [Fintype S] (D : Matrix S Q F) : Submodule F (Q → F) :=
  LinearMap.range D.transpose.mulVecLin

/-- Image of supported cycles in the quotient by boundaries. -/
def supportedLogical (C B : Submodule F (Q → F)) (E : Set Q) :
    Submodule F ((Q → F) ⧸ B) := (C ⊓ coordinateSpace E).map B.mkQ

/-- Actual dimension of the quotient image. -/
noncomputable def supportedDim (C B : Submodule F (Q → F)) (E : Set Q) : ℕ :=
  Module.finrank F (supportedLogical C B E)

noncomputable def zDim [Fintype S] (P : Matrix R Q F) (D : Matrix S Q F)
    (E : Set Q) : ℕ := supportedDim (cycles P) (boundaries D) E

noncomputable def xDim [Fintype R] (P : Matrix R Q F) (D : Matrix S Q F)
    (E : Set Q) : ℕ := zDim D P E

theorem supportedDim_eq_zero_iff (C B : Submodule F (Q → F)) (E : Set Q) :
    supportedDim C B E = 0 ↔ C ⊓ coordinateSpace E ≤ B := by
  rw [supportedDim, Submodule.finrank_eq_zero, supportedLogical,
    ← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]

/-- Rank-nullity for a linear map on a subspace, in ambient coordinates. -/
theorem finrank_map_add_finrank_inf_ker
    {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] (U : Submodule F V) (f : V →ₗ[F] W) :
    Module.finrank F (U.map f) + Module.finrank F ↥(U ⊓ LinearMap.ker f) =
      Module.finrank F U := by
  have h := (f.comp U.subtype).finrank_range_add_finrank_ker
  have hk : Module.finrank F (LinearMap.ker (f.comp U.subtype)) =
      Module.finrank F ↥(U ⊓ LinearMap.ker f) := by
    rw [← Submodule.map_comap_subtype U (LinearMap.ker f),
      Submodule.finrank_map_subtype_eq, LinearMap.ker_comp]
  rw [LinearMap.range_comp, Submodule.range_subtype, hk] at h
  exact h

/-- Dimension of supported cycles is image dimension plus supported boundaries. -/
theorem supportedDim_add_finrank_boundary
    (C B : Submodule F (Q → F)) (hBC : B ≤ C) (E : Set Q) :
    supportedDim C B E + Module.finrank F ↥(B ⊓ coordinateSpace E) =
      Module.finrank F ↥(C ⊓ coordinateSpace E) := by
  have h := finrank_map_add_finrank_inf_ker (C ⊓ coordinateSpace E) B.mkQ
  rw [Submodule.ker_mkQ] at h
  have he : (C ⊓ coordinateSpace E) ⊓ B = B ⊓ coordinateSpace E := by
    ext v
    constructor
    · intro hv; exact ⟨hv.2, hv.1.2⟩
    · intro hv; exact ⟨⟨hBC hv.1, hv.2⟩, hv.1⟩
  rw [he] at h
  exact h

/-- Restriction to a set of coordinates. -/
def restrictCoords (E : Set Q) : (Q → F) →ₗ[F] (E → F) :=
  LinearMap.funLeft F F Subtype.val

@[simp] theorem restrictCoords_apply (E : Set Q) (v : Q → F) (q : E) :
    restrictCoords E v q = v q := rfl

@[simp] theorem ker_restrictCoords (E : Set Q) :
    LinearMap.ker (restrictCoords (F := F) E) = coordinateSpace Eᶜ := by
  ext v
  simp only [LinearMap.mem_ker, mem_coordinateSpace, Set.mem_compl_iff,
    not_not, funext_iff, restrictCoords_apply, Pi.zero_apply]
  constructor
  · intro h q hq; exact h ⟨q, hq⟩
  · intro h q; exact h q q.property

/-- A word on E is the same thing as an ambient word supported in E. -/
noncomputable def coordinateEquiv (E : Set Q) :
    coordinateSpace (F := F) E ≃ₗ[F] (E → F) := by
  classical
  exact
    { toFun := fun v q => v.val q
      invFun := fun v => ⟨fun q => if h : q ∈ E then v ⟨q,h⟩ else 0, by
        intro q hq; simp [hq]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext q
        change (if h : q ∈ E then v.val q else 0) = v.val q
        split_ifs with hq
        · rfl
        · exact (v.property q hq).symm
      right_inv := by intro v; funext q; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem finrank_coordinateSpace (E : Set Q) [Fintype E] :
    Module.finrank F (coordinateSpace (F := F) E) = Fintype.card E := by
  rw [(coordinateEquiv (F := F) E).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- Matrix column restriction is literal submatrix restriction. -/
def restrictColumns (P : Matrix R Q F) (E : Set Q) : Matrix R E F :=
  P.submatrix id Subtype.val

/-- Restricting the row space is the row space of the column restriction. -/
theorem rank_restrictColumns [Fintype R] (P : Matrix R Q F)
    (E : Set Q) [Fintype E] :
    (restrictColumns P E).rank =
      Module.finrank F ((boundaries P).map (restrictCoords E)) := by
  rw [← Matrix.rank_transpose, Matrix.rank, boundaries, ← LinearMap.range_comp]
  rfl

theorem finrank_boundaries [Fintype R] (P : Matrix R Q F) :
    Module.finrank F (boundaries P) = P.rank := by
  exact Matrix.rank_transpose P

/-- A row-space restriction has precisely the supported rows as its kernel. -/
theorem finrank_supported_boundaries_add_rank [Fintype R]
    (P : Matrix R Q F) (E : Set Q) [Fintype ↥(Eᶜ)] :
    Module.finrank F ↥(boundaries P ⊓ coordinateSpace E) +
      (restrictColumns P Eᶜ).rank = P.rank := by
  have h := finrank_map_add_finrank_inf_ker (boundaries P) (restrictCoords Eᶜ)
  rw [ker_restrictCoords, compl_compl, ← rank_restrictColumns,
    finrank_boundaries] at h
  omega

/-- Ordinary rank-nullity for a check matrix. -/
theorem finrank_cycles_add_rank (P : Matrix R Q F) :
    Module.finrank F (cycles P) + P.rank = Fintype.card Q := by
  have h := P.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  change Module.finrank F (LinearMap.ker P.mulVecLin) +
    Module.finrank F (LinearMap.range P.mulVecLin) = _
  omega

/-- Multiplication of a supported word uses exactly the columns in its support set. -/
theorem mulVec_restrict_supported (P : Matrix R Q F) (E : Set Q) [Fintype E]
    (v : coordinateSpace (F := F) E) :
    (restrictColumns P E).mulVecLin (coordinateEquiv E v) = P.mulVecLin v.val := by
  classical
  ext r
  change (∑ q : E, P r q * v.val q) = ∑ q : Q, P r q * v.val q
  rw [← Finset.sum_subtype E.toFinset (by simp) (fun q : Q => P r q * v.val q)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  rw [v.property q (by simpa using hq), mul_zero]

/-- The range of a check restricted to supported words is its column submatrix range. -/
theorem map_coordinateSpace_eq_range_restrictColumns (P : Matrix R Q F)
    (E : Set Q) [Fintype E] :
    (coordinateSpace E).map P.mulVecLin = LinearMap.range (restrictColumns P E).mulVecLin := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨coordinateEquiv E ⟨v,hv⟩, mulVec_restrict_supported P E ⟨v,hv⟩⟩
  · rintro ⟨v, rfl⟩
    let w := (coordinateEquiv (F := F) E).symm v
    refine ⟨w.val, w.property, ?_⟩
    have h := mulVec_restrict_supported P E w
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- Rank-nullity on the erasure coordinates. -/
theorem finrank_supported_cycles_add_rank (P : Matrix R Q F)
    (E : Set Q) [Fintype E] :
    Module.finrank F ↥(cycles P ⊓ coordinateSpace E) +
      (restrictColumns P E).rank = Fintype.card E := by
  have h := finrank_map_add_finrank_inf_ker (coordinateSpace E) P.mulVecLin
  rw [map_coordinateSpace_eq_range_restrictColumns, finrank_coordinateSpace] at h
  rw [inf_comm (coordinateSpace E) (LinearMap.ker P.mulVecLin)] at h
  change (restrictColumns P E).rank +
    Module.finrank F ↥(cycles P ⊓ coordinateSpace E) = _ at h
  omega

/-- CSS commutation says that the boundary row space consists of cycles. -/
theorem boundaries_le_cycles [Fintype S] (P : Matrix R Q F) (D : Matrix S Q F)
    (hPD : P * D.transpose = 0) : boundaries D ≤ cycles P := by
  rintro v ⟨w, rfl⟩
  change P.mulVecLin (D.transpose.mulVecLin w) = 0
  rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hPD]
  simp

/-- The Z rank identity, for arbitrary dependent checks and any erasure. -/
theorem zDim_rank_identity [Fintype S] (P : Matrix R Q F) (D : Matrix S Q F)
    (hPD : P * D.transpose = 0) (E : Set Q) [Fintype E] [Fintype ↥(Eᶜ)] :
    zDim P D E + (restrictColumns P E).rank + D.rank =
      Fintype.card E + (restrictColumns D Eᶜ).rank := by
  have hi := supportedDim_add_finrank_boundary (cycles P) (boundaries D)
    (boundaries_le_cycles P D hPD) E
  have hc := finrank_supported_cycles_add_rank P E
  have hb := finrank_supported_boundaries_add_rank D E
  unfold zDim
  omega

/-- Swapping the two checks preserves CSS commutation. -/
theorem checks_commute_swap [Fintype R] [Fintype S]
    (P : Matrix R Q F) (D : Matrix S Q F) (hPD : P * D.transpose = 0) :
    D * P.transpose = 0 := by
  have h := congrArg Matrix.transpose hPD
  simpa using h

/-- The X rank identity. -/
theorem xDim_rank_identity [Fintype R] [Fintype S]
    (P : Matrix R Q F) (D : Matrix S Q F) (hPD : P * D.transpose = 0)
    (E : Set Q) [Fintype E] [Fintype ↥(Eᶜ)] :
    xDim P D E + (restrictColumns D E).rank + P.rank =
      Fintype.card E + (restrictColumns P Eᶜ).rank :=
  zDim_rank_identity D P (checks_commute_swap P D hPD) E

@[simp] theorem coordinateSpace_univ :
    coordinateSpace (F := F) (Set.univ : Set Q) = ⊤ := by
  ext v
  simp [mem_coordinateSpace]

@[simp] theorem coordinateSpace_empty :
    coordinateSpace (F := F) (∅ : Set Q) = ⊥ := by
  ext v
  simp [mem_coordinateSpace, funext_iff]

/-- Global logical dimension, defined by the actual quotient image. -/
noncomputable def logicalDim [Fintype S] (P : Matrix R Q F) (D : Matrix S Q F) : ℕ :=
  zDim P D Set.univ

/-- The global quotient dimension satisfies the usual CSS parameter equation. -/
theorem logicalDim_add_ranks [Fintype S]
    (P : Matrix R Q F) (D : Matrix S Q F) (hPD : P * D.transpose = 0) :
    logicalDim P D + P.rank + D.rank = Fintype.card Q := by
  have hi := supportedDim_add_finrank_boundary (cycles P) (boundaries D)
    (boundaries_le_cycles P D hPD) Set.univ
  have hc' : cycles P ⊓ coordinateSpace (F := F) (Set.univ : Set Q) = cycles P := by
    rw [coordinateSpace_univ, inf_top_eq]
  have hb' : boundaries D ⊓ coordinateSpace (F := F) (Set.univ : Set Q) = boundaries D := by
    rw [coordinateSpace_univ, inf_top_eq]
  rw [hc', hb', finrank_boundaries] at hi
  have hc := finrank_cycles_add_rank P
  change supportedDim (cycles P) (boundaries D) Set.univ + P.rank + D.rank = _
  omega

theorem logicalDim_eq_length_sub_ranks [Fintype S]
    (P : Matrix R Q F) (D : Matrix S Q F) (hPD : P * D.transpose = 0) :
    logicalDim P D = Fintype.card Q - P.rank - D.rank := by
  have h := logicalDim_add_ranks P D hPD
  omega

/-- X and Z global logical spaces have the same dimension. -/
theorem logicalDim_swap [Fintype R] [Fintype S]
    (P : Matrix R Q F) (D : Matrix S Q F) (hPD : P * D.transpose = 0) :
    logicalDim D P = logicalDim P D := by
  have h := logicalDim_add_ranks P D hPD
  have h' := logicalDim_add_ranks D P (checks_commute_swap P D hPD)
  omega

/-- Complementary erasures split the global logical dimension between sectors. -/
theorem zDim_add_xDim_compl [Fintype R] [Fintype S]
    (P : Matrix R Q F) (D : Matrix S Q F) (hPD : P * D.transpose = 0)
    (E : Set Q) [Fintype E] [Fintype ↥(Eᶜ)] :
    zDim P D E + xDim P D Eᶜ = logicalDim P D := by
  classical
  have hz := zDim_rank_identity P D hPD E
  have hx := xDim_rank_identity P D hPD (Eᶜ)
  rw [rank_restrictColumns, rank_restrictColumns] at hz hx
  let rP : Set Q → ℕ := fun A => Module.finrank F ((boundaries P).map (restrictCoords A))
  let rD : Set Q → ℕ := fun A => Module.finrank F ((boundaries D).map (restrictCoords A))
  change zDim P D E + rP E + D.rank = Fintype.card E + rD (Eᶜ) at hz
  change xDim P D (Eᶜ) + rD (Eᶜ) + P.rank = Fintype.card ↥(Eᶜ) + rP (Eᶜᶜ) at hx
  rw [compl_compl] at hx
  have hk := logicalDim_add_ranks P D hPD
  have hcard : Fintype.card (E ⊕ ↥(Eᶜ)) = Fintype.card Q :=
    Fintype.card_congr (Equiv.Set.sumCompl E)
  rw [Fintype.card_sum] at hcard
  omega

/-- The other sector's complementary-erasure identity. -/
theorem xDim_add_zDim_compl [Fintype R] [Fintype S]
    (P : Matrix R Q F) (D : Matrix S Q F) (hPD : P * D.transpose = 0)
    (E : Set Q) [Fintype E] [Fintype ↥(Eᶜ)] :
    xDim P D E + zDim P D Eᶜ = logicalDim P D := by
  have h := zDim_add_xDim_compl D P (checks_commute_swap P D hPD) E
  rw [logicalDim_swap P D hPD] at h
  exact h

end HGPExperiment
