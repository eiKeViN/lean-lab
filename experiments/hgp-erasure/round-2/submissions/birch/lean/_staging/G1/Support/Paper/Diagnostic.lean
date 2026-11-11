import QEC.Coding.HypergraphProduct.Distance.Support
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Coordinate support and actual images in a quotient, for source.md B–D. -/

noncomputable section
namespace Paper
open QEC QEC.Coding QEC.Coding.HypergraphProduct
open Module
universe u v w
variable {F : Type u} [Field F] {Q : Type v} [Fintype Q] [DecidableEq Q]

/-- Words vanishing outside the selected finite set (source.md B). -/
def supportSpace (E : Finset Q) : Submodule F (Q → F) :=
  LinearMap.range (zeroExtend (F := F) E)

/-- Coordinate characterization of support; expand zero extension in either direction. -/
theorem mem_supportSpace (E : Finset Q) (v : Q → F) :
    v ∈ supportSpace E ↔ ∀ q, q ∉ E → v q = 0 := by
  constructor
  · rintro ⟨v, rfl⟩ q hq
    simp [zeroExtend, hq]
  · intro hv
    refine ⟨fun q ↦ v q, ?_⟩
    funext q
    by_cases hq : q ∈ E
    · simp [zeroExtend, hq]
    · simp [zeroExtend, hq, hv q hq]

/-- The coordinate space has one dimension per selected coordinate. -/
theorem finrank_supportSpace (E : Finset Q) :
    finrank F (supportSpace (F := F) E) = E.card := by
  rw [supportSpace, LinearMap.finrank_range_of_inj (zeroExtend_injective E)]
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
    exact (Submodule.Quotient.eq_zero_iff_mem).2 hx)

/-- The quotient embedding is injective by its exact kernel. -/
theorem cycleQuotientEmbedding_injective (C B : Submodule F (Q → F)) :
    Function.Injective (cycleQuotientEmbedding C B) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro x hx
  exact (Submodule.Quotient.eq_zero_iff_mem).1 hx

/-- Transporting the source's supported image along the injective quotient embedding
is exactly `supportedLogical`; thus the ambient presentation preserves its semantics. -/
theorem supportedLogical_eq_actual_image (C B : Submodule F (Q → F)) (E : Finset Q) :
    (((supportSpace E).comap C.subtype).map (B.comap C.subtype).mkQ).map
      (cycleQuotientEmbedding C B) = supportedLogical C B E := by
  rw [Submodule.map_map]
  change ((supportSpace E).comap C.subtype).map
    ((B.comap C.subtype).liftQ (B.mkQ.comp C.subtype) _ |>.comp
      (B.comap C.subtype).mkQ) = _
  rw [Submodule.liftQ_mkQ, ← Submodule.map_map]
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, hc⟩
  · rintro ⟨hc, hv⟩
    exact ⟨⟨v, hc⟩, hv, rfl⟩


end Paper
