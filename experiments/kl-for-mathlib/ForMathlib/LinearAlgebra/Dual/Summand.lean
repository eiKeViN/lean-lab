module
public import Mathlib

public section

/-! Semantic home: ForMathlib.LinearAlgebra.Dual.Summand. Source spans: BalancedPairings:17.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace AdjointSummandDuality
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (d : M ≃ₗ[R] Module.Dual R M) (i : N →ₗ[R] M) (p : M →ₗ[R] N)
  (hpi : ∀ n, p (i n)=n)
noncomputable section

 @[expose] def dualSection : Module.Dual R N →ₗ[R] M :=
  d.symm.toLinearMap.comp p.dualMap

 @[expose] def dualProjection : M →ₗ[R] Module.Dual R N := i.dualMap.comp d.toLinearMap

include hpi in
 theorem projection_section (lam : Module.Dual R N) :
    dualProjection d i (dualSection d p lam)=lam := by
  apply LinearMap.ext
  intro n
  change d (d.symm (p.dualMap lam)) (i n)=lam n
  rw [LinearEquiv.apply_symm_apply]
  change lam (p (i n))=lam n
  rw [hpi]

 @[expose] def adjointProjector : Module.End R M := (dualSection d p).comp (dualProjection d i)

include hpi in
 theorem adjointProjector_idempotent (m : M) :
    adjointProjector d i p (adjointProjector d i p m)=adjointProjector d i p m := by
  change dualSection d p (dualProjection d i (dualSection d p (dualProjection d i m))) = _
  rw [projection_section d i p hpi]
  rfl

 @[expose] def adjointSummand : Submodule R M := LinearMap.range (dualSection d p)

include hpi in
 theorem dualProjection_injective_on_adjoint :
    Function.Injective ((dualProjection d i).domRestrict (adjointSummand d p)) := by
  rintro ⟨m,lam,rfl⟩ ⟨n,mu,rfl⟩ h
  apply Subtype.ext
  change dualSection d p lam=dualSection d p mu
  change dualProjection d i (dualSection d p lam)=dualProjection d i (dualSection d p mu) at h
  rw [projection_section d i p hpi,projection_section d i p hpi] at h
  rw [h]

include hpi in
 theorem dualProjection_surjective_on_adjoint :
    Function.Surjective ((dualProjection d i).domRestrict (adjointSummand d p)) := by
  intro lam
  exact ⟨⟨dualSection d p lam,lam,rfl⟩,projection_section d i p hpi lam⟩

 @[expose] def adjointEquivDual : adjointSummand d p ≃ₗ[R] Module.Dual R N :=
  LinearEquiv.ofBijective ((dualProjection d i).domRestrict (adjointSummand d p))
    ⟨dualProjection_injective_on_adjoint d i p hpi,dualProjection_surjective_on_adjoint d i p hpi⟩

 theorem adjointEquivDual_apply (m : adjointSummand d p) (n : N) :
    adjointEquivDual d i p hpi m n=d m.val (i n) := rfl

include hpi in
 theorem adjointProjector_range :
    LinearMap.range (adjointProjector d i p)=adjointSummand d p := by
  apply le_antisymm
  · rintro m ⟨n,rfl⟩
    exact ⟨dualProjection d i n,rfl⟩
  · rintro m ⟨lam,rfl⟩
    refine ⟨dualSection d p lam,?_⟩
    change dualSection d p (dualProjection d i (dualSection d p lam))=dualSection d p lam
    rw [projection_section d i p hpi]

variable (f : Module.End R M) (g : Module.End R N)
  (hbal : ∀ m n, d (f m) n=d m (f n))
  (hi : ∀ n, f (i n)=i (g n)) (hp : ∀ m, p (f m)=g (p m))

include hbal hi in
 theorem projection_intertwines (m : M) :
    dualProjection d i (f m)=g.dualMap (dualProjection d i m) := by
  apply LinearMap.ext
  intro n
  change d (f m) (i n)=d m (i (g n))
  rw [hbal,hi]

include hbal hp in
 theorem section_intertwines (lam : Module.Dual R N) :
    f (dualSection d p lam)=dualSection d p (g.dualMap lam) := by
  apply d.injective
  apply LinearMap.ext
  intro n
  change d (f (d.symm (p.dualMap lam))) n=
    d (d.symm (p.dualMap (g.dualMap lam))) n
  rw [hbal,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change lam (p (f n))=lam (g (p n))
  rw [hp]

include hbal hi hp in
 theorem adjointProjector_commutes (m : M) :
    f (adjointProjector d i p m)=adjointProjector d i p (f m) := by
  change f (dualSection d p (dualProjection d i m)) =
    dualSection d p (dualProjection d i (f m))
  rw [section_intertwines d p f g hbal hp,projection_intertwines d i f g hbal hi]

end
end AdjointSummandDuality
end

end OAI
