module
public import Mathlib
public import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization

public section

/-! Semantic home: ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity. Source spans: EdgeLocalization:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem scaledKL_reciprocity_upper {C : Type*} [Field C]
    (t : C) (ht : t ≠ 0) (u b : W) (x : Interval cs u b) :
    scaledKL cs t x.val b = ∑ᶠ z : Interval cs u b,
      Polynomial.eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val) *
        scaledKL cs t⁻¹ z.val b := by
  classical
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  let := interval_finite cs x.val b
  let := Fintype.ofFinite (Interval cs x.val b)
  rw [scaledKL_reciprocity cs t ht x.val b x.property.2,
    finsum_eq_sum_of_fintype,finsum_eq_sum_of_fintype]
  let f : W → C := fun z => Polynomial.eval₂ (Int.castRingHom C) (t⁻¹-t)
    (Hecke.rTilde cs x.val z) * scaledKL cs t⁻¹ z b
  have hs (a : W) [Fintype (Interval cs a b)] :
      (∑ z : Interval cs a b, f z.val) =
        ∑ z ∈ (lowerFinset cs b).filter (fun z => BruhatLE cs a z), f z := by
    exact (Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs a b)))
      ((lowerFinset cs b).filter (fun z => BruhatLE cs a z))
      (fun z => by simp only [Finset.mem_filter,mem_lowerFinset]; exact and_comm) f).symm
  change (∑ z : Interval cs x.val b, f z.val) = ∑ z : Interval cs u b, f z.val
  rw [hs,hs]
  apply Finset.sum_subset
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hz,hxz⟩
    exact Finset.mem_filter.mpr ⟨hz,x.property.1.trans hxz⟩
  · intro z hz hn
    have hxz : ¬ BruhatLE cs x.val z := by
      intro h
      exact hn (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,h⟩)
    dsimp [f]
    rw [Hecke.rTilde_zero cs _ _ hxz,Polynomial.eval₂_zero,zero_mul]

end
end KLInvariance
end

end OAI
