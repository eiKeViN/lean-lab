import Mathlib

/-! Semantic home: OAI.LinearAlgebra.PairProjection.Basic. Source spans: Decomposition:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : M →ₗ[R] X) (g : M →ₗ[R] Y)
noncomputable section

def relation : Submodule R (X × Y) := LinearMap.range (f.prod g)
abbrev Edge := (X × Y) ⧸ relation f g

def lower : X →ₗ[R] Edge f g := (relation f g).mkQ.comp (LinearMap.inl R X Y)
def upper : Y →ₗ[R] Edge f g := -((relation f g).mkQ.comp (LinearMap.inr R X Y))

theorem diagonal_zero (m : M) : (relation f g).mkQ (f m,g m)=0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m,rfl⟩

theorem compatible (m : M) : lower f g (f m)=upper f g (g m) := by
  have h := diagonal_zero f g m
  have hp : (f m,g m)=(f m,0)+(0,g m) := by simp
  rw [hp,map_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem compatible_iff (x : X) (y : Y) :
    lower f g x=upper f g y ↔ ∃ m : M, f m=x ∧ g m=y := by
  change (relation f g).mkQ (x,0) = -((relation f g).mkQ (0,y)) ↔ _
  rw [eq_neg_iff_add_eq_zero,← map_add]
  rw [show ((x,0)+(0,y) : X × Y)=(x,y) by simp]
  change (Submodule.Quotient.mk (x,y) : Edge f g)=0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,congrArg Prod.fst hm,congrArg Prod.snd hm⟩
  · rintro ⟨m,hm,hn⟩
    exact ⟨m,Prod.ext hm hn⟩

theorem kernel_lower (x : X) : lower f g x=0 ↔ ∃ m : M, f m=x ∧ g m=0 := by
  change (relation f g).mkQ (x,0)=0 ↔ _
  change Submodule.Quotient.mk (x,0) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,congrArg Prod.fst hm,congrArg Prod.snd hm⟩
  · rintro ⟨m,hm,hn⟩
    exact ⟨m,Prod.ext hm hn⟩

theorem lower_surjective (hg : Function.Surjective g) :
    Function.Surjective (lower f g) := by
  intro v
  obtain ⟨⟨x,y⟩,rfl⟩ := (relation f g).mkQ_surjective v
  obtain ⟨m,rfl⟩ := hg y
  refine ⟨x-f m,?_⟩
  change (relation f g).mkQ (x-f m,0) = (relation f g).mkQ (x,g m)
  have hp : (x-f m,0)=(x,g m)-(f m,g m) := by simp
  rw [hp,map_sub,diagonal_zero,sub_zero]

theorem upper_surjective (hf : Function.Surjective f) :
    Function.Surjective (upper f g) := by
  intro v
  obtain ⟨⟨x,y⟩,rfl⟩ := (relation f g).mkQ_surjective v
  obtain ⟨m,rfl⟩ := hf x
  refine ⟨g m-y,?_⟩
  change -((relation f g).mkQ (0,g m-y)) = (relation f g).mkQ (f m,y)
  have hp : (0,g m-y)=(f m,g m)-(f m,y) := by simp
  rw [hp,map_sub,diagonal_zero,zero_sub,neg_neg]

/-- A genuine right-action eigenvalue difference annihilates the edge
quotient. This uses only the integral module, not a fraction-field equality. -/
theorem difference_annihilates (hf : Function.Surjective f)
    (hg : Function.Surjective g) (T : M →ₗ[R] M) (r s : R)
    (hr : ∀ m, f (T m)=r • f m) (hs : ∀ m, g (T m)=s • g m)
    (v : Edge f g) : (r-s) • v=0 := by
  obtain ⟨x,rfl⟩ := lower_surjective f g hg v
  rw [← map_smul]
  apply (kernel_lower f g _).mpr
  obtain ⟨m,rfl⟩ := hf x
  refine ⟨T m-s • m,?_,?_⟩
  · rw [map_sub,map_smul,hr,sub_smul]
  · rw [map_sub,map_smul,hs,sub_self]

end
end KLInvariance.PairProjection
end

end OAI
