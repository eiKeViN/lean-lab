import HGPExperiment.Erasure

noncomputable section
namespace HGPExperiment
variable {F Q : Type*} [Field F] [Fintype Q]

/-- The logical quotient formed inside the cycle space. For CSS checks its
submodule of denominators is the boundary space, viewed inside the cycles. -/
abbrev LogicalQuotient (C B : Submodule F (Q → F)) :=
  C ⧸ B.comap C.subtype

/-- The supported logical image using the quotient of the cycles themselves. -/
def supportedWithin (C B : Submodule F (Q → F)) (E : Set Q) :
    Submodule F (LogicalQuotient C B) :=
  ((coordinateSpace E).comap C.subtype).map (B.comap C.subtype).mkQ

/-- The canonical embedding into the ambient quotient by boundaries. -/
def quotientEmbedding (C B : Submodule F (Q → F)) :
    LogicalQuotient C B →ₗ[F] ((Q → F) ⧸ B) :=
  (B.comap C.subtype).liftQ (B.mkQ.comp C.subtype) (by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ])

theorem quotientEmbedding_injective (C B : Submodule F (Q → F)) :
    Function.Injective (quotientEmbedding C B) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]

theorem supportedWithin_map (C B : Submodule F (Q → F)) (E : Set Q) :
    (supportedWithin C B E).map (quotientEmbedding C B) = supportedLogical C B E := by
  unfold supportedWithin supportedLogical quotientEmbedding
  rw [← Submodule.map_comp, Submodule.liftQ_mkQ, Submodule.map_comp,
    Submodule.map_comap_subtype]

/-- The ambient-quotient and cycle-quotient supported images are canonically
isomorphic, so the supported dimensions have exactly the requested semantics. -/
def supportedLogicalEquiv (C B : Submodule F (Q → F)) (E : Set Q) :
    supportedWithin C B E ≃ₗ[F] supportedLogical C B E :=
  ((supportedWithin C B E).equivMapOfInjective (quotientEmbedding C B)
    (quotientEmbedding_injective C B)).trans
    (LinearEquiv.ofEq _ _ (supportedWithin_map C B E))

theorem supportedDim_eq_finrank_within (C B : Submodule F (Q → F)) (E : Set Q) :
    supportedDim C B E = Module.finrank F (supportedWithin C B E) :=
  (supportedLogicalEquiv C B E).finrank_eq.symm

@[simp] theorem supportedWithin_univ (C B : Submodule F (Q → F)) :
    supportedWithin C B Set.univ = ⊤ := by
  unfold supportedWithin
  have he : coordinateSpace (F := F) (Set.univ : Set Q) = ⊤ := by
    ext v
    simp [mem_coordinateSpace]
  rw [he, Submodule.comap_top, Submodule.map_top, Submodule.range_mkQ]

theorem supportedDim_univ_eq (C B : Submodule F (Q → F)) :
    supportedDim C B Set.univ = Module.finrank F (LogicalQuotient C B) := by
  rw [supportedDim_eq_finrank_within, supportedWithin_univ, finrank_top]

end HGPExperiment
