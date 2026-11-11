import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod


namespace HGPExperiment

abbrev F := ZMod 2

variable {Q : Type*}

/-- Words vanishing outside the erased set. -/
def supportedSpace (E : Set Q) : Submodule F (Q → F) where
  carrier := {v | ∀ q, q ∉ E → v q = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb q hq; simp [ha q hq, hb q hq]
  smul_mem' := by intro a b hb q hq; simp [hb q hq]

@[simp] theorem mem_supportedSpace (E : Set Q) (v : Q → F) :
    v ∈ supportedSpace E ↔ ∀ q, q ∉ E → v q = 0 := Iff.rfl

/-- The actual image of supported cycles in the quotient by boundaries. -/
def supportedLogical (cycles boundaries : Submodule F (Q → F)) (E : Set Q) :
    Submodule F ((Q → F) ⧸ boundaries) :=
  (cycles ⊓ supportedSpace E).map boundaries.mkQ

noncomputable def supportedDim (cycles boundaries : Submodule F (Q → F)) (E : Set Q) : ℕ :=
  Module.finrank F (supportedLogical cycles boundaries E)

variable [Fintype Q]

/-- Rank-nullity on a subspace, in ambient-space notation. -/
theorem finrank_map_add_inf_ker {V W : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] [AddCommGroup W] [Module F W]
    (U : Submodule F V) (f : V →ₗ[F] W) :
    Module.finrank F (U.map f) + Module.finrank F ↥(U ⊓ f.ker) = Module.finrank F U := by
  have h := (f.comp U.subtype).finrank_range_add_finrank_ker
  have hr : LinearMap.range (f.comp U.subtype) = U.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : (LinearMap.ker (f.comp U.subtype)).map U.subtype = U ⊓ f.ker := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply,
      Submodule.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u.property, hu⟩
    · rintro ⟨hu, hv⟩; exact ⟨⟨v, hu⟩, hv, rfl⟩
  rw [hr] at h
  rw [← hk, Submodule.finrank_map_subtype_eq]
  exact h

/-- Supported logical dimension is the quotient dimension of supported cycles
by supported boundaries. -/
theorem supportedDim_add_finrank (cycles boundaries : Submodule F (Q → F))
    (h : boundaries ≤ cycles) (E : Set Q) :
    supportedDim cycles boundaries E + Module.finrank F ↥(boundaries ⊓ supportedSpace E) =
      Module.finrank F ↥(cycles ⊓ supportedSpace E) := by
  have hi : (cycles ⊓ supportedSpace E) ⊓ LinearMap.ker boundaries.mkQ =
      boundaries ⊓ supportedSpace E := by
    rw [Submodule.ker_mkQ]
    ext v
    exact ⟨fun hv => ⟨hv.2, hv.1.2⟩, fun hv => ⟨⟨h hv.1, hv.2⟩, hv.1⟩⟩
  have hh := finrank_map_add_inf_ker (cycles ⊓ supportedSpace E) boundaries.mkQ
  rw [hi] at hh
  exact hh

/-- Restriction to a set of coordinates. -/
def restrictMap (E : Set Q) : (Q → F) →ₗ[F] (E → F) where
  toFun v q := v q
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem restrictMap_apply (E : Set Q) (v : Q → F) (q : E) :
    restrictMap E v q = v q := rfl

@[simp] theorem ker_restrictMap (E : Set Q) :
    (restrictMap E).ker = supportedSpace Eᶜ := by
  ext v
  simp only [LinearMap.mem_ker, mem_supportedSpace, Set.mem_compl_iff, not_not]
  constructor
  · intro h q hq
    exact congrFun h ⟨q, hq⟩
  · intro h
    funext q
    exact h q q.property

/-- Restricting a supported word is a linear equivalence. -/
noncomputable def supportedEquiv (E : Set Q) : supportedSpace E ≃ₗ[F] (E → F) := by
  classical
  exact
    { toFun := fun v q => v.val q
      invFun := fun v => ⟨fun q => if h : q ∈ E then v ⟨q,h⟩ else 0,
        by intro q hq; simp [hq]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext q
        by_cases hq : q ∈ E
        · simp [hq]
        · simp [hq, v.property q hq]
      right_inv := by intro v; funext q; simp [q.property]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem supportedSpace_finrank (E : Set Q) :
    Module.finrank F (supportedSpace E) = Nat.card E := by
  classical
  simpa [Module.finrank_pi, Nat.card_eq_fintype_card] using
    (supportedEquiv E).finrank_eq

variable {X Z : Type*} [Fintype X] [Fintype Z]

def cycles (P : Matrix X Q F) : Submodule F (Q → F) := P.mulVecLin.ker

def boundaries (D : Matrix Z Q F) : Submodule F (Q → F) := D.transpose.mulVecLin.range

noncomputable def zDim (P : Matrix X Q F) (D : Matrix Z Q F) (E : Set Q) : ℕ :=
  supportedDim (cycles P) (boundaries D) E

noncomputable def xDim (P : Matrix X Q F) (D : Matrix Z Q F) (E : Set Q) : ℕ :=
  zDim D P E

/-- A binary CSS pair with no row independence assumptions. -/
structure CSS (X Z Q : Type*) [Fintype X] [Fintype Z] [Fintype Q] where
  P : Matrix X Q F
  D : Matrix Z Q F
  orthogonal : P * D.transpose = 0

end HGPExperiment
