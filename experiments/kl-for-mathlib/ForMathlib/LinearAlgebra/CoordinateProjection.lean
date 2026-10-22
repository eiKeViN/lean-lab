module
public import Mathlib.LinearAlgebra.Pi

public section

/-! Semantic home: ForMathlib.LinearAlgebra.CoordinateProjection. Source spans: IntegralPairings:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.CoordinateProjection
universe ur un uv ux
variable {R : Type ur} [CommRing R] {N : Type un} [AddCommGroup N] [Module R N]
  {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, N →ₗ[R] X x)
noncomputable section

 @[expose] def eval (U : Set V) : N →ₗ[R] (∀ x : U, X x.val) := LinearMap.pi (fun x => f x.val)
 @[expose] def image (U : Set V) : Submodule R (∀ x : U, X x.val) := LinearMap.range (eval f U)
 @[expose] def project (U : Set V) : N →ₗ[R] image f U := (eval f U).rangeRestrict

 theorem project_surjective (U : Set V) : Function.Surjective (project f U) :=
by
  rintro ⟨z,n,hn⟩
  exact ⟨n,Subtype.ext hn⟩

 @[simp] theorem project_apply (U : Set V) (n : N) (x : U) : (project f U n).val x=f x.val n := rfl

 theorem project_zero_iff (U : Set V) (n : N) : project f U n=0 ↔ ∀ x∈U, f x n=0 := by
  constructor
  · intro h x hx
    exact congrArg (fun z : image f U => z.val ⟨x,hx⟩) h
  · intro h
    apply Subtype.ext
    funext x
    exact h x.val x.property

 @[expose] def restrict {U K : Set V} (h : U⊆K) : image f K →ₗ[R] image f U where
  toFun z := ⟨fun x => z.val ⟨x.val,h x.property⟩,by
    obtain ⟨n,hn⟩ := z.property
    refine ⟨n,?_⟩
    funext x
    exact congrFun hn ⟨x.val,h x.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 @[simp] theorem restrict_project {U K : Set V} (h : U⊆K) (n : N) :
    restrict f h (project f K n)=project f U n := rfl

 theorem restrict_surjective {U K : Set V} (h : U⊆K) : Function.Surjective (restrict f h) := by
  intro z
  obtain ⟨n,rfl⟩ := project_surjective f U z
  exact ⟨project f K n,rfl⟩

 theorem restrict_zero_iff {U K : Set V} (h : U⊆K) (z : image f K) :
    restrict f h z=0 ↔ ∀ x hx, x∈U → z.val ⟨x,hx⟩=0 := by
  constructor
  · intro hz x hx hu
    exact congrArg (fun q : image f U => q.val ⟨x,hu⟩) hz
  · intro hz
    apply Subtype.ext
    funext x
    exact hz x.val (h x.property) x.property

end
end KLInvariance.CoordinateProjection
end

end OAI
