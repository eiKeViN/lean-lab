module
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs

public section

/-! Semantic home: ForMathlib.LinearAlgebra.PlaneReduction. Source spans: PlaneLocalization:23.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.PlaneReduction
universe uk uv ua
variable {k : Type uk} [Field k] {V : Type uv} [AddCommGroup V] [Module k V]
  {A : Type ua} [CommRing A] [Algebra k A]

 theorem scalar_reduction (l : V →ₗ[k] A) {a b c : V} (ha : l a = 0)
    (hc : c ∈ Submodule.span k ({a,b} : Set V))
    (hca : c ∉ Submodule.span k ({a} : Set V)) :
    ∃ r : k, r ≠ 0 ∧ l c = r • l b := by
  obtain ⟨s,r,hr⟩ := Submodule.mem_span_pair.mp hc
  have hr0 : r ≠ 0 := by
    intro hz
    apply hca
    rw [← hr,hz,zero_smul,add_zero]
    exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_singleton a))
  refine ⟨r,hr0,?_⟩
  rw [← hr,map_add,map_smul,map_smul,ha,smul_zero,zero_add]

 theorem associated_reduction (l : V →ₗ[k] A) {a b c : V} (ha : l a = 0)
    (hc : c ∈ Submodule.span k ({a,b} : Set V))
    (hca : c ∉ Submodule.span k ({a} : Set V)) : Associated (l c) (l b) := by
  obtain ⟨r,hr,he⟩ := scalar_reduction l ha hc hca
  rw [he,Algebra.smul_def]
  exact associated_unit_mul_left _ _ ((hr.isUnit).map (algebraMap k A))

end KLInvariance.PlaneReduction
end

end OAI
