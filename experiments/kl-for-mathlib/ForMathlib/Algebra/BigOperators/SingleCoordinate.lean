import Mathlib

/-! Semantic home: ForMathlib.Algebra.BigOperators.SingleCoordinate. Source spans: DyerPaths:1, SimultaneousInvariance:5/weighted-difference.
See migration.json and MIGRATION.md for exact provenance.
Cancellation and difference of finite weighted sums at one distinguished coordinate. The existing character/matrix names are retained for compatibility; no character theory or matrix representation is assumed. -/

namespace OAI

section
namespace KLInvariance
universe u v
variable {V : Type u} [Fintype V] {C : Type v} [CommRing C]

/-- Exchange two finite weighted sums by distributivity and commutativity.
This isolates bilinear reindexing from the cancellation argument. -/
theorem weighted_sum_exchange (m r : V → C) (p : V → V → C) :
    (∑ z, r z * (∑ y, m y * p y z)) = ∑ y, m y * (∑ z, r z * p y z) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- A finite weighted sum supported at a single coordinate equals its surviving
value when that weight is one. Apply after the other coordinate errors vanish. -/
theorem weighted_sum_single (t : V) (m f : V → C) (hm : m t = 1)
    (hf : ∀ y, y ≠ t → f y = 0) : (∑ y, m y * f y) = f t := by
  classical
  rw [Finset.sum_eq_single t]
  · rw [hm, one_mul]
  · intro y _ hy
    rw [hf y hy, mul_zero]
  · simp

 theorem finite_character_cancellation (t : V) (m : V → C) (r : V → C)
    (p : V → V → C) (q : V → C) (hm : m t=1)
    (hword : (∑ y, m y*q y)=∑ z, r z*(∑ y, m y*p y z))
    (hlower : ∀ y, y≠t → q y=∑ z, r z*p y z) : q t=∑ z, r z*p t z := by
  classical
  rw [weighted_sum_exchange m r p] at hword
  have hzero : (∑ y, m y*(q y-∑ z, r z*p y z))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,hword,sub_self]
  have hsingle : (∑ y, m y*(q y-∑ z, r z*p y z))=q t-∑ z, r z*p t z := by
    apply weighted_sum_single t m _ hm
    intro y hy
    rw [hlower y hy, sub_self]
  rw [hsingle] at hzero
  exact sub_eq_zero.mp hzero

end KLInvariance
end


section
namespace KLInvariance.Comparison
open Polynomial
noncomputable section

 theorem matrix_difference_single {V : Type*} [Fintype V] (a : V → ℝ)
    (v w : V → ℝ) (x : V) (hdiag : a x=1)
    (hvw : ∀ y, y ≠ x → v y=w y) :
    (∑ y, a y*v y)-(∑ y, a y*w y)=v x-w x := by
  classical
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  exact weighted_sum_single x a (fun y => v y - w y) hdiag
    (fun y hy => sub_eq_zero.mpr (hvw y hy))

 theorem matrix_difference_le {V : Type*} [Fintype V]
    (a : V → ℝ) (v w : V → ℝ) (x : V) (p p' : ℝ)
    (hdiag : a x=1) (hvw : ∀ y, y ≠ x → v y=w y)
    (hp : p ≤ ∑ y, a y*v y) (hp' : p'=∑ y, a y*w y) :
    p-p' ≤ v x-w x := by
  rw [← matrix_difference_single a v w x hdiag hvw]
  exact sub_le_sub hp hp'.ge

end
end KLInvariance.Comparison
end

end OAI
