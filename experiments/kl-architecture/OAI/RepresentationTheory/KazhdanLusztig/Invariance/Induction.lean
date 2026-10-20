import Mathlib
import OAI.Data.Polynomial.ScaledComparison
import OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization

/-! Semantic home: OAI.RepresentationTheory.KazhdanLusztig.Invariance.Induction. Source spans: Invariance:1, Invariance:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'}
noncomputable section

 theorem rankDifference_subinterval_lt (x z : Interval cs a b) (hxz : x≤z)
    (hne : x.val≠a ∨ z.val≠b) :
    rankDifference cs x.val z.val<rankDifference cs a b := by
  have ha := length_le_of_bruhat cs x.property.1
  have hb := length_le_of_bruhat cs z.property.2
  have hm := length_le_of_bruhat cs hxz
  dsimp only [rankDifference]
  rcases hne with h|h
  · have := length_lt_of_bruhat_ne cs x.property.1 h.symm
    omega
  · have := length_lt_of_bruhat_ne cs z.property.2 h
    omega

 theorem rTilde_transport_all (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b')
    (hr : Hecke.rTilde cs a b=Hecke.rTilde cs' a' b')
    (hsmall : ∀ (x z : Interval cs a b), x≤z →
      rankDifference cs x.val z.val<rankDifference cs a b →
      Hecke.rTilde cs x.val z.val=Hecke.rTilde cs' (φ x).val (φ z).val) :
    ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val := by
  intro x z
  by_cases hxz : x≤z
  · by_cases hxa : x.val=a
    · by_cases hzb : z.val=b
      · have hx : x=intervalBottom cs hab := Subtype.ext hxa
        have hz : z=intervalTop cs hab := Subtype.ext hzb
        rw [hx,hz,intervalIso_bottom cs cs' hab hab' φ,intervalIso_top cs cs' hab hab' φ]
        exact hr
      · exact hsmall x z hxz (rankDifference_subinterval_lt x z hxz (Or.inr hzb))
    · exact hsmall x z hxz (rankDifference_subinterval_lt x z hxz (Or.inl hxa))
  · have hnot : ¬BruhatLE cs' (φ x).val (φ z).val := fun h => hxz (φ.le_iff_le.mp h)
    rw [Hecke.rTilde_zero cs x.val z.val hxz,Hecke.rTilde_zero cs' _ _ hnot]

end
end KLInvariance
end


section
namespace KLInvariance
open Polynomial
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem scaledKL_eq_scaledPolynomial (t : ℝ) {x b : W} (hxb : BruhatLE cs x b) :
    scaledKL cs t x b = Comparison.scaledPolynomial t (rankDifference cs x b)
      (klPolynomial cs x b) := by
  have hh := length_le_of_bruhat cs hxb
  have he : (cs.length x : ℤ)-cs.length b = -(rankDifference cs x b : ℤ) := by
    unfold rankDifference
    omega
  simp only [scaledKL,Comparison.scaledPolynomial,he]

variable {I' : Type u'} {M' : CoxeterMatrix I'} {W' : Type v'} [Group W']
  (cs' : CoxeterSystem M' W') {u b : W} {u' b' : W'}
  (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
  (φ : Interval cs u b ≃o Interval cs' u' b')

include hub hub'

 theorem intervalIso_upper_rankDifference (x : Interval cs u b) :
    rankDifference cs x.val b = rankDifference cs' (φ x).val b' := by
  have h := intervalIso_rankDifference cs cs' φ
    (show x ≤ intervalTop cs hub from x.property.2)
  rw [intervalIso_top cs cs' hub hub' φ] at h
  exact h

 theorem scaledKL_transport (t : ℝ) (x : Interval cs u b)
    (hx : klPolynomial cs x.val b=klPolynomial cs' (φ x).val b') :
    scaledKL cs t x.val b=scaledKL cs' t (φ x).val b' := by
  rw [scaledKL_eq_scaledPolynomial cs t x.property.2,
    scaledKL_eq_scaledPolynomial cs' t (φ x).property.2,
    intervalIso_upper_rankDifference cs cs' hub hub' φ x,hx]

end
end KLInvariance
end

end OAI
