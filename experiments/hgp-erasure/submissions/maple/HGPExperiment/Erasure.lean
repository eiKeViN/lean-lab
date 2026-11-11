import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod
import Lean.Elab.Tactic.Omega

namespace HGPExperiment

abbrev F₂ := ZMod 2

open Module

variable {Q RX RZ : Type*} [Fintype Q] [Fintype RX] [Fintype RZ]

/-- Vectors supported in the specified erasure. -/
def supportSpace (E : Set Q) : Submodule F₂ (Q → F₂) where
  carrier := {v | ∀ q, q ∉ E → v q = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb q hq; simp [ha q hq, hb q hq]
  smul_mem' := by intro a v hv q hq; simp [hv q hq]

@[simp] theorem mem_supportSpace (E : Set Q) (v : Q → F₂) :
    v ∈ supportSpace E ↔ ∀ q, q ∉ E → v q = 0 := Iff.rfl

noncomputable def cycles (P : Matrix RX Q F₂) : Submodule F₂ (Q → F₂) :=
  by classical exact LinearMap.ker (Matrix.toLin' P)

noncomputable def boundaries (D : Matrix RZ Q F₂) : Submodule F₂ (Q → F₂) :=
  by classical exact LinearMap.range (Matrix.toLin' D.transpose)

/-- The actual image of supported cycles in the quotient by the boundary space. -/
noncomputable def supportedLogical (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (E : Set Q) : Submodule F₂ ((Q → F₂) ⧸ boundaries D) :=
  (cycles P ⊓ supportSpace E).map (boundaries D).mkQ

noncomputable def logicalDimension (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (E : Set Q) : ℕ := finrank F₂ ↥(supportedLogical P D E)

noncomputable def restrictColumns (P : Matrix RX Q F₂) (E : Set Q) : Matrix RX E F₂ :=
  P.submatrix id Subtype.val

@[simp] theorem logicalDimension_eq_zero_iff (P : Matrix RX Q F₂)
    (D : Matrix RZ Q F₂) (E : Set Q) :
    logicalDimension P D E = 0 ↔
      ∀ v, v ∈ cycles P → v ∈ supportSpace E → v ∈ boundaries D := by
  rw [logicalDimension, Submodule.finrank_eq_zero]
  change (cycles P ⊓ supportSpace E).map (boundaries D).mkQ = ⊥ ↔ _
  rw [eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
  exact ⟨fun h v hp he => h ⟨hp, he⟩, fun h v hv => h v hv.1 hv.2⟩

/-- CSS commutation ensures every boundary is a cycle. -/
theorem boundaries_le_cycles (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (hcomm : P * D.transpose = 0) : boundaries D ≤ cycles P := by
  classical
  rintro v ⟨w, rfl⟩
  change Matrix.toLin' P (Matrix.toLin' D.transpose w) = 0
  rw [← Matrix.toLin'_mul_apply, hcomm]
  simp

/-- Rank-nullity for the restriction of a linear map to a subspace, expressed
    entirely in the ambient space. -/
theorem finrank_map_add_finrank_inf_ker {V W : Type*} [AddCommGroup V]
    [Module F₂ V] [FiniteDimensional F₂ V] [AddCommGroup W] [Module F₂ W]
    (f : V →ₗ[F₂] W) (S : Submodule F₂ V) :
    finrank F₂ ↥(S.map f) + finrank F₂ ↥(S ⊓ LinearMap.ker f) = finrank F₂ S := by
  have h := (f.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have heq : finrank F₂ ↥(Submodule.comap S.subtype (LinearMap.ker f)) =
      finrank F₂ ↥(S ⊓ LinearMap.ker f) := by
    rw [← Submodule.map_comap_subtype S (LinearMap.ker f),
      Submodule.finrank_map_subtype_eq]
  rwa [heq] at h

/-- Restrict a supported word to its support coordinates. -/
noncomputable def supportEquiv (E : Set Q) : supportSpace E ≃ₗ[F₂] (E → F₂) := by
  classical
  exact
    { toFun := fun v q => v.1 q
      invFun := fun v => ⟨fun q => if h : q ∈ E then v ⟨q, h⟩ else 0,
        by intro q hq; simp [hq]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext q
        change (if h : q ∈ E then v.1 q else 0) = v.1 q
        split_ifs with h
        · rfl
        · exact (v.2 q h).symm
      right_inv := by intro v; funext q; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The support space has one coordinate for each erased qubit. -/
theorem finrank_supportSpace (E : Set Q) [Fintype E] :
    finrank F₂ ↥(supportSpace E) = Fintype.card E := by
  rw [(supportEquiv E).finrank_eq, Module.finrank_pi]

/-- A supported logical class is represented by a supported cycle modulo a
    boundary which is itself supported. -/
theorem logicalDimension_add_finrank_boundaries_inf_support
    (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (hcomm : P * D.transpose = 0) (E : Set Q) :
    logicalDimension P D E + finrank F₂ ↥(boundaries D ⊓ supportSpace E) =
      finrank F₂ ↥(cycles P ⊓ supportSpace E) := by
  have h := finrank_map_add_finrank_inf_ker (boundaries D).mkQ
    (cycles P ⊓ supportSpace E)
  rw [Submodule.ker_mkQ] at h
  have hi : (cycles P ⊓ supportSpace E) ⊓ boundaries D =
      boundaries D ⊓ supportSpace E := by
    apply le_antisymm
    · intro v hv; exact ⟨hv.2, hv.1.2⟩
    · intro v hv; exact ⟨⟨boundaries_le_cycles P D hcomm hv.1, hv.2⟩, hv.1⟩
  rw [hi] at h
  exact h

noncomputable def restrictMap (E : Set Q) : (Q → F₂) →ₗ[F₂] (E → F₂) :=
  LinearMap.funLeft F₂ F₂ Subtype.val

@[simp] theorem restrictMap_apply (E : Set Q) (v : Q → F₂) (q : E) :
    restrictMap E v q = v q := rfl

@[simp] theorem ker_restrictMap_compl (E : Set Q) :
    LinearMap.ker (restrictMap Eᶜ) = supportSpace E := by
  ext v
  simp only [LinearMap.mem_ker, mem_supportSpace, funext_iff, restrictMap_apply,
    Pi.zero_apply, Set.mem_compl_iff]
  constructor
  · intro h q hq; exact h ⟨q, hq⟩
  · intro h q; exact h q q.2

theorem finrank_boundaries (D : Matrix RZ Q F₂) :
    finrank F₂ ↥(boundaries D) = D.rank := by
  rw [← Matrix.rank_transpose]
  rfl

/-- Boundary vectors vanishing outside E are the kernel of complementary
    coordinate restriction on the boundary space. -/
theorem finrank_boundaries_inf_support_add_rank
    (D : Matrix RZ Q F₂) (E : Set Q) [Fintype ↥(Eᶜ)] :
    finrank F₂ ↥(boundaries D ⊓ supportSpace E) +
      (restrictColumns D Eᶜ).rank = D.rank := by
  classical
  have h := finrank_map_add_finrank_inf_ker (restrictMap Eᶜ) (boundaries D)
  rw [ker_restrictMap_compl, finrank_boundaries] at h
  have hr : (boundaries D).map (restrictMap Eᶜ) =
      LinearMap.range (Matrix.toLin' (restrictColumns D Eᶜ).transpose) := by
    rw [boundaries, ← LinearMap.range_comp]
    congr 1
    ext v q
  rw [hr] at h
  have hd : finrank F₂ ↥(LinearMap.range
      (Matrix.toLin' (restrictColumns D Eᶜ).transpose)) = (restrictColumns D Eᶜ).rank := by
    rw [← Matrix.rank_transpose]
    rfl
  rw [hd] at h
  omega

/-- Restriction of the check operator to the support space is exactly the
    check matrix with only the erased columns. -/
theorem check_domRestrict_support (P : Matrix RX Q F₂) (E : Set Q)
    [Fintype E] :
    (Matrix.toLin' P).domRestrict (supportSpace E) =
      (Matrix.toLin' (restrictColumns P E)).comp (supportEquiv E).toLinearMap := by
  classical
  ext v r
  change (∑ q : Q, P r q * v.1 q) = ∑ q : E, P r q * v.1 q
  have h := Fintype.sum_subtype_add_sum_subtype (fun q : Q => q ∈ E)
    (fun q => P r q * v.1 q)
  have hz : (∑ q : Eᶜ, P r q * v.1 q) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [v.2 q q.2, mul_zero]
  simpa only [hz, add_zero] using h.symm

/-- Rank-nullity on supported words. -/
theorem finrank_cycles_inf_support_add_rank (P : Matrix RX Q F₂)
    (E : Set Q) [Fintype E] :
    finrank F₂ ↥(cycles P ⊓ supportSpace E) + (restrictColumns P E).rank =
      Fintype.card E := by
  classical
  have h := finrank_map_add_finrank_inf_ker (Matrix.toLin' P) (supportSpace E)
  have hr : (supportSpace E).map (Matrix.toLin' P) =
      LinearMap.range (Matrix.toLin' (restrictColumns P E)) := by
    rw [← LinearMap.range_domRestrict, check_domRestrict_support,
      LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [hr, finrank_supportSpace] at h
  have hc : supportSpace E ⊓ LinearMap.ker (Matrix.toLin' P) =
      cycles P ⊓ supportSpace E := inf_comm _ _
  rw [hc] at h
  change (restrictColumns P E).rank + _ = _ at h
  omega

/-- The Z-sector supported logical rank identity for arbitrary binary CSS checks. -/
theorem logicalDimension_rank_identity (P : Matrix RX Q F₂)
    (D : Matrix RZ Q F₂) (hcomm : P * D.transpose = 0) (E : Set Q)
    [Fintype E] [Fintype ↥(Eᶜ)] :
    logicalDimension P D E + (restrictColumns P E).rank + D.rank =
      Fintype.card E + (restrictColumns D Eᶜ).rank := by
  have h₁ := logicalDimension_add_finrank_boundaries_inf_support P D hcomm E
  have h₂ := finrank_cycles_inf_support_add_rank P E
  have h₃ := finrank_boundaries_inf_support_add_rank D E
  omega

end HGPExperiment
