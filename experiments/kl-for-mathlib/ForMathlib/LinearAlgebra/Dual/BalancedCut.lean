import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.Dual.BalancedCut. Source spans: CharacterReciprocity:2, Support:10.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace BalancedCuts
universe ur um ua
variable {R : Type ur} [CommRing R] [IsDomain R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {A : Type ua} [AddCommGroup A] [Module R A]
  (d : M →ₗ[R] Module.Dual R M) (π : M →ₗ[R] A) (c : M →ₗ[R] M)
  (p : R) (hp : p≠0) (hπ : ∀ m, π (c m)=p • π m)
  (hleft : ∀ m n, π n=0 → d (c m) n=0)
  (hright : ∀ m n, π m=0 → d m (c n)=0)

include hp hπ hleft hright in
 theorem balanced_two (m n : M) : d (c m) n=d m (c n) := by
  have hn : π (p • n-c n)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have hm : π (p • m-c m)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have en := hleft m _ hn
  have em := hright _ n hm
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,sub_eq_zero] at en em
  exact mul_left_cancel₀ hp (en.trans em.symm)

end BalancedCuts
end


section
namespace BalancedCuts
universe ur um ua
variable {R : Type ur} [CommRing R] [IsDomain R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {A : Type ua} [AddCommGroup A] [Module R A]
  (d : M →ₗ[R] Module.Dual R M) (hsym : ∀ m n, d m n=d n m)
  (π : M →ₗ[R] A) (c : M →ₗ[R] M) (p : R) (hp : p ≠ 0)
  (hπ : ∀ m, π (c m)=p • π m)
  (horth : ∀ m n, π n=0 → d (c m) n=0)

include hsym hp hπ horth in
 theorem balanced (m n : M) : d (c m) n=d m (c n) := by
  have hn : π (p • n-c n)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have hm : π (p • m-c m)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have en := horth m _ hn
  have em := horth n _ hm
  simp only [map_sub,map_smul,smul_eq_mul,sub_eq_zero] at en em
  rw [hsym (c n) m,hsym (c n) (c m)] at em
  exact mul_left_cancel₀ hp (en.trans em.symm)

end BalancedCuts
end

end OAI
