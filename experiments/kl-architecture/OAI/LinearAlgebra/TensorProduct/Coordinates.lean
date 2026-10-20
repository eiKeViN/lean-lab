import Mathlib

/-! Semantic home: OAI.LinearAlgebra.TensorProduct.Coordinates. Source spans: BottSamelson:1, BottSamelson:12.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
open TensorProduct
universe uc ua un uv up
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module C N]
  {V : Type uv} [AddCommGroup V] [Module A V]
  {P : Type up} [AddCommGroup P] [Module A P]
 theorem tensor_range_le_of_one_tmul (F : (A ⊗[C] N) →ₗ[A] V) (G : P →ₗ[A] V)
    (h : ∀ n : N, F ((1 : A) ⊗ₜ[C] n) ∈ LinearMap.range G) :
    LinearMap.range F ≤ LinearMap.range G := by
  rintro _ ⟨m,rfl⟩
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => rw [map_add]; exact (LinearMap.range G).add_mem hm hn
  | tmul a n =>
    have he : a ⊗ₜ[C] n = a • ((1 : A) ⊗ₜ[C] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul,mul_one]
    rw [he,map_smul]
    exact (LinearMap.range G).smul_mem a (h n)
 theorem tensor_maps_eq_of_one_tmul (F G : (A ⊗[C] N) →ₗ[A] V)
    (h : ∀ n : N, F ((1 : A) ⊗ₜ[C] n)=G ((1 : A) ⊗ₜ[C] n)) : F=G := by
  apply LinearMap.ext
  intro m
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => rw [map_add,map_add,hm,hn]
  | tmul a n =>
    have he : a ⊗ₜ[C] n = a • ((1 : A) ⊗ₜ[C] n) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [he,map_smul,map_smul,h n]

 theorem codRestrict_surjective_of_range_le (G : P →ₗ[A] V) (S : Submodule A V)
    (hG : ∀ p, G p ∈ S) (hS : S ≤ LinearMap.range G) :
    Function.Surjective (LinearMap.codRestrict S G hG) := by
  intro z
  obtain ⟨p,hp⟩ := hS z.property
  exact ⟨p,Subtype.ext hp⟩
end KLInvariance
end


section
namespace KLInvariance
universe ua up uv un
variable {A : Type ua} [CommRing A]
  {P : Type up} [AddCommGroup P] [Module A P]
  {V : Type uv} [AddCommGroup V] [Module A V]
  {N : Type un} [AddCommGroup N] [Module A N]
 theorem linearMap_mem_of_coordinates (S : Submodule A P)
    (F : P →ₗ[A] V) (G : N →ₗ[A] P) (E : N →ₗ[A] V)
    (hF : Function.Injective F) (heq : F.comp G = E)
    (hrange : LinearMap.range E ≤ LinearMap.range (F.comp S.subtype)) (n : N) : G n ∈ S := by
  obtain ⟨p,hp⟩ := hrange (show E n ∈ LinearMap.range E from ⟨n,rfl⟩)
  have he : (p : P) = G n := hF (hp.trans (LinearMap.congr_fun heq n).symm)
  exact he ▸ p.property
end KLInvariance
end

end OAI
