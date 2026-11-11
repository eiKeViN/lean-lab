import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Coordinate support and actual images in a quotient, for source.md B–D. -/

noncomputable section
namespace Paper
open Module
universe u v w
variable {F : Type u} [Field F] {Q : Type v} [Fintype Q] [DecidableEq Q]

/-- Words vanishing outside the selected finite set (source.md B). -/
def supportSpace (E : Finset Q) : Submodule F (Q → F) where
  carrier := {v | ∀ q, q ∉ E → v q = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy q hq
    simp [hx q hq, hy q hq]
  smul_mem' := by
    intro a x hx q hq
    simp [hx q hq]

/-- Coordinate characterization of support, exactly the source zero condition. -/
theorem mem_supportSpace (E : Finset Q) (v : Q → F) :
    v ∈ supportSpace E ↔ ∀ q, q ∉ E → v q = 0 := Iff.rfl

/-- Restriction is a linear equivalence between supported words and words on E. -/
def supportEquiv (E : Finset Q) : supportSpace (F := F) E ≃ₗ[F] ({q // q ∈ E} → F) where
  toFun v q := v.1 q.1
  invFun v := ⟨fun q ↦ if hq : q ∈ E then v ⟨q, hq⟩ else 0, by
    intro q hq
    simp [hq]⟩
  left_inv v := by
    apply Subtype.ext
    funext q
    by_cases hq : q ∈ E
    · simp [hq]
    · simpa [hq] using (v.2 q hq).symm
  right_inv v := by
    funext q
    simp [q.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate space has one dimension per selected coordinate. -/
theorem finrank_supportSpace (E : Finset Q) :
    finrank F (supportSpace (F := F) E) = E.card := by
  rw [(supportEquiv E).finrank_eq]
  simp

/-- Source.md B: the actual image of supported cycles in the ambient boundary quotient. -/
def supportedLogical (C B : Submodule F (Q → F)) (E : Finset Q) :
    Submodule F ((Q → F) ⧸ B) :=
  (C ⊓ supportSpace E).map B.mkQ

/-- The supported logical dimension, defined from the quotient image. -/
def supportedDim (C B : Submodule F (Q → F)) (E : Finset Q) : ℕ :=
  finrank F (supportedLogical C B E)

/-- The ordinary cycle quotient injects into the ambient quotient. Source.md B:
its kernel is precisely the boundary subspace comapped to the cycles. -/
def cycleQuotientEmbedding (C B : Submodule F (Q → F)) :
    (C ⧸ B.comap C.subtype) →ₗ[F] ((Q → F) ⧸ B) :=
  (B.comap C.subtype).liftQ (B.mkQ.comp C.subtype) (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero B).2 hx)

/-- The quotient embedding is injective by its exact kernel. -/
theorem cycleQuotientEmbedding_injective (C B : Submodule F (Q → F)) :
    Function.Injective (cycleQuotientEmbedding C B) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero B).1 hx

/-- Transporting the source's supported image along the injective quotient embedding
is exactly `supportedLogical`; thus the ambient presentation preserves its semantics. -/
theorem supportedLogical_eq_actual_image (C B : Submodule F (Q → F)) (E : Finset Q) :
    (((supportSpace E).comap C.subtype).map (B.comap C.subtype).mkQ).map
      (cycleQuotientEmbedding C B) = supportedLogical C B E := by
  have hf : (cycleQuotientEmbedding C B).comp (B.comap C.subtype).mkQ =
      B.mkQ.comp C.subtype := by
    ext x
    rfl
  rw [← Submodule.map_comp, hf, Submodule.map_comp, Submodule.map_comap_subtype]
  rfl

/-- Rank-nullity for the image of any finite-dimensional subspace under a map.
Identify the domain-restricted kernel with the intersection through subtype inclusion. -/
theorem finrank_image_add_inf_ker {V : Type v} {W : Type w}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W]
    (S : Submodule F V) (f : V →ₗ[F] W) :
    finrank F (S.map f) + finrank F ↥(S ⊓ LinearMap.ker f) = finrank F S := by
  have h := (f.comp S.subtype).finrank_range_add_finrank_ker
  have hr : LinearMap.range (f.comp S.subtype) = S.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hr] at h
  have hk : (LinearMap.ker (f.comp S.subtype)).map S.subtype =
      S ⊓ LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hf⟩
      exact ⟨⟨x, hx⟩, hf, rfl⟩
  rw [← hk, Submodule.finrank_map_subtype_eq]
  exact h

/-- The image dimension plus the supported boundaries equals the supported cycles. -/
theorem supportedDim_add_boundary (C B : Submodule F (Q → F)) (E : Finset Q)
    (hBC : B ≤ C) :
    supportedDim C B E + finrank F ↥(B ⊓ supportSpace E) =
      finrank F ↥(C ⊓ supportSpace E) := by
  have h := finrank_image_add_inf_ker (C ⊓ supportSpace E) B.mkQ
  rw [Submodule.ker_mkQ] at h
  have heq : (C ⊓ supportSpace E) ⊓ B = B ⊓ supportSpace E := by
    ext v
    constructor
    · exact fun h ↦ ⟨h.2, h.1.2⟩
    · exact fun h ↦ ⟨⟨hBC h.1, h.2⟩, h.1⟩
  rw [heq] at h
  exact h

end Paper
