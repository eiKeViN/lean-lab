module
public import Mathlib
public import ForMathlib.Algebra.Module.Projective.Transport
public import ForMathlib.Algebra.Module.ReflectionPair.TensorKernel
public import ForMathlib.LinearAlgebra.CoordinateProjection

public section

/-! Semantic home: ForMathlib.LinearAlgebra.KernelCoordinates. Source spans: IntegralPairings:9, IntegralPairings:16.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe ur un up uq
variable {R : Type ur} [CommRing R]
  {N : Type un} [klPreservedInstance12 : AddCommGroup N] [Module R N]
  {P : Type up} [klPreservedInstance13 : AddCommGroup P] [Module R P]
  {Q : Type uq} [klPreservedInstance14 : AddCommGroup Q] [Module R Q]
 theorem injective_of_zero_lift (f : N →ₗ[R] P) (hf : Function.Surjective f) (g : P →ₗ[R] Q)
    (h : ∀ n, g (f n)=0 → f n=0) : Function.Injective g := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  obtain ⟨n,rfl⟩ := hf p
  exact h n hp
 theorem maps_eq_iff_of_zero_iff (f : N →ₗ[R] P) (g : N →ₗ[R] Q)
    (h : ∀ n, f n=0 ↔ g n=0) (m n : N) : f m=f n ↔ g m=g n := by
  rw [← sub_eq_zero,← map_sub,h,map_sub,sub_eq_zero]
include klPreservedInstance12 klPreservedInstance13 klPreservedInstance14 in
 theorem functions_eq_of_surjective (f : N → P) (hf : Function.Surjective f)
    (g h : P → Q) (he : ∀ n, g (f n)=h (f n)) (p : P) : g p=h p := by
  have _ := klPreservedInstance12
  have _ := klPreservedInstance13
  have _ := klPreservedInstance14
  obtain ⟨n,rfl⟩ := hf p
  exact he n
end KLInvariance
end


section
namespace KLInvariance
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]

 theorem kernel_coordinate_injective (f : M →ₗ[R] P) (g : M →ₗ[R] S)
    (h : Function.Injective (f.prod g)) :
    Function.Injective (g.comp (LinearMap.ker f).subtype) := by
  intro m n he
  apply Subtype.ext
  apply h
  exact Prod.ext (m.property.trans n.property.symm) he

 theorem common_kernel_coordinate_injective (r : M →ₗ[R] H) (f : M →ₗ[R] P) (g : M →ₗ[R] S)
    (h : Function.Injective (f.prod g)) :
    Function.Injective (g.comp (LinearMap.ker r ⊓ LinearMap.ker f).subtype) := by
  intro m n he
  apply Subtype.ext
  apply h
  exact Prod.ext (m.property.2.trans n.property.2.symm) he

 theorem projective_of_coordinates (f : M →ₗ[R] P) (hf : Function.Injective f)
    (g : H →ₗ[R] P) (hg : Function.Injective g)
    (hfg : ∀ m, ∃ n, f m=g n) (hgf : ∀ n, ∃ m, f m=g n)
    [Module.Projective R H] : Module.Projective R M := by
  apply projective_of_same_range f hf g hg
  ext p
  constructor
  · rintro ⟨m,rfl⟩
    obtain ⟨n,hn⟩ := hfg m
    exact ⟨n,hn.symm⟩
  · rintro ⟨n,rfl⟩
    exact hgf n

namespace ReflectionPairTranslation
 theorem twistMap_injective (τ : R ≃+* R) (f : M →ₗ[R] P) (hf : Function.Injective f) :
    Function.Injective (twistMap τ f) := by
  intro m n h
  exact Twist.ext (hf (congrArg Twist.val h))
end ReflectionPairTranslation

namespace CoordinateProjection
universe uv ux
variable {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, M →ₗ[R] X x)
 theorem restrict_joint_injective {U V' K : Set V} (hU : U⊆K) (hV : V'⊆K)
    (hc : ∀ x∈K, x∈U ∨ x∈V') :
    Function.Injective ((restrict f hU).prod (restrict f hV)) := by
  intro p q h
  apply Subtype.ext
  funext x
  rcases hc x.val x.property with hx|hx
  · exact congrArg (fun z : image f U => z.val ⟨x.val,hx⟩) (congrArg Prod.fst h)
  · exact congrArg (fun z : image f V' => z.val ⟨x.val,hx⟩) (congrArg Prod.snd h)
end CoordinateProjection
end KLInvariance
end

end OAI
