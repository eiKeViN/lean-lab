module
public import Mathlib
public import ForMathlib.LinearAlgebra.Dual.Summand

public section

/-! Semantic home: ForMathlib.LinearAlgebra.Dual.Adjoint. Source spans: IntegralPairings:30, BalancedPairings:29, BalancedPairings:18, BalancedPairings:19.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  (d : M ≃ₗ[R] Dual R M)
noncomputable section

 @[expose] def adjoint (f : End R M) : End R M :=
  d.symm.toLinearMap.comp (f.dualMap.comp d.toLinearMap)

 theorem pairing (f : End R M) (m n : M) : d (adjoint d f m) n=d m (f n) := by
  change d (d.symm (f.dualMap (d m))) n=d m (f n)
  rw [LinearEquiv.apply_symm_apply]
  rfl

 theorem adjoint_comp (f g : End R M) : adjoint d (f.comp g)=(adjoint d g).comp (adjoint d f) := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing]
  change d m (f (g n))=d (adjoint d g (adjoint d f m)) n
  rw [pairing,pairing]

 theorem adjoint_idempotent (f : End R M) (hf : ∀ m, f (f m)=f m) (m : M) :
    adjoint d f (adjoint d f m)=adjoint d f m := by
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,pairing,hf,pairing]

 theorem commutes_of_balanced (f t : End R M)
    (ht : ∀ m n, d (t m) n=d m (t n)) (hf : ∀ m, f (t m)=t (f m)) (m : M) :
    adjoint d f (t m)=t (adjoint d f m) := by
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,ht,ht,pairing,hf]

 theorem symmetric_pairing (hsym : ∀ m n, d m n=d n m)
    (f : End R M) (m n : M) : d m (adjoint d f n)=d (f m) n := by
  rw [hsym,pairing,hsym]

 theorem adjoint_adjoint (hsym : ∀ m n, d m n=d n m) (f : End R M) :
    adjoint d (adjoint d f)=f := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,symmetric_pairing d hsym]

end
end PerfectAdjoint
end


section
namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R] {N : Type um} [AddCommGroup N] [Module R N]
 theorem adjoint_zero (d : N ≃ₗ[R] Dual R N) : adjoint d (0 : End R N)=0 := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing]
  simp
end PerfectAdjoint
end


section
namespace PerfectAdjoint
open Module
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (d : M ≃ₗ[R] Dual R M) (i : N →ₗ[R] M) (p : M →ₗ[R] N)
  (hpi : ∀ n, p (i n)=n)
noncomputable section

 theorem adjoint_projector_eq : adjoint d (i.comp p)=
    AdjointSummandDuality.adjointProjector d i p := by
  apply LinearMap.ext
  intro m
  rfl

 @[expose] def rangeAdjointEquivDual : LinearMap.range (adjoint d (i.comp p)) ≃ₗ[R] Dual R N :=
  (LinearEquiv.ofEq _ _ (by
    rw [adjoint_projector_eq,AdjointSummandDuality.adjointProjector_range d i p hpi])).trans
    (AdjointSummandDuality.adjointEquivDual d i p hpi)

 theorem rangeAdjointEquivDual_apply (m : LinearMap.range (adjoint d (i.comp p))) (n : N) :
    rangeAdjointEquivDual d i p hpi m n=d m.val (i n) := rfl

end
end PerfectAdjoint
end


section
namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  (d : M ≃ₗ[R] Dual R M) (f : End R M) (hf : ∀ m, f (f m)=f m)
noncomputable section

include hf in
 theorem range_projector_split (m : f.range) : f.rangeRestrict (f.range.subtype m)=m := by
  apply Subtype.ext
  obtain ⟨n,hn⟩ := m.property
  change f m.val=m.val
  rw [← hn,hf]

 @[expose] def rangeAdjointEquivDualRange : LinearMap.range (adjoint d f) ≃ₗ[R] Dual R f.range :=
  rangeAdjointEquivDual d f.range.subtype f.rangeRestrict (range_projector_split f hf)

 theorem rangeAdjointEquivDualRange_apply (m : LinearMap.range (adjoint d f)) (n : f.range) :
    rangeAdjointEquivDualRange d f hf m n=d m.val n.val := rfl

end
end PerfectAdjoint
end

end OAI
