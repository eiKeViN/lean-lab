import Mathlib

/-! Semantic home: ForMathlib.Algebra.BigOperators.FiniteCharacterCancellation. Source spans: DyerPaths:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe u v
variable {V : Type u} [Fintype V] {C : Type v} [CommRing C]

 theorem finite_character_cancellation (t : V) (m : V → C) (r : V → C)
    (p : V → V → C) (q : V → C) (hm : m t=1)
    (hword : (∑ y, m y*q y)=∑ z, r z*(∑ y, m y*p y z))
    (hlower : ∀ y, y≠t → q y=∑ z, r z*p y z) : q t=∑ z, r z*p t z := by
  classical
  have hexpand : (∑ z, r z*(∑ y, m y*p y z))=∑ y, m y*(∑ z, r z*p y z) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hexpand] at hword
  have hzero : (∑ y, m y*(q y-∑ z, r z*p y z))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,hword,sub_self]
  have hsingle : (∑ y, m y*(q y-∑ z, r z*p y z))=q t-∑ z, r z*p t z := by
    rw [Finset.sum_eq_single t]
    · rw [hm,one_mul]
    · intro y _ hy
      rw [hlower y hy,sub_self,mul_zero]
    · simp
  rw [hsingle] at hzero
  exact sub_eq_zero.mp hzero

end KLInvariance
end

end OAI
