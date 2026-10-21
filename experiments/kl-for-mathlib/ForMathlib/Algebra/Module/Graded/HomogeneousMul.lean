import Mathlib
import ForMathlib.Algebra.Module.Graded.Generators

/-! Semantic home: ForMathlib.Algebra.Module.Graded.HomogeneousMul. Source spans: Frobenius:7.
See migration.json and MIGRATION.md for exact provenance.
Recovering homogeneity of a factor after multiplication by a nonzero homogeneous scalar. -/

namespace OAI

section
namespace KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [IsDomain A]
  [Algebra k A] (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedSMul 𝓐 𝓐]

 theorem homogeneous_of_mul {a b : A} {d n : ℤ}
    (ha : a ∈ 𝓐 d) (hne : a ≠ 0) (hab : a*b ∈ 𝓐 n) : b ∈ 𝓐 (n-d) := by
  have hc := component_homogeneous_smul 𝓐 𝓐 d a ha n b
  have he : component 𝓐 n (a*b)=a*b :=
    DirectSum.decompose_of_mem_same 𝓐 hab
  rw [smul_eq_mul,he,smul_eq_mul] at hc
  have hb : b=component 𝓐 (n-d) b := mul_left_cancel₀ hne hc
  rw [hb]
  exact (DirectSum.decompose 𝓐 b (n-d)).property

end KLInvariance.Graded
end

end OAI
