import Mathlib

/-! Semantic home: ForMathlib.Algebra.Polynomial.TransferEvaluation. Source spans: SimultaneousInvariance:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Comparison
open Polynomial
 theorem polynomial_eq_of_transfer_eval_eq (p q : ℤ[X])
    (h : ∀ t : ℝ, 0<t → t<1 →
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) p=eval₂ (Int.castRingHom ℝ) (t⁻¹-t) q) : p=q := by
  apply Polynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Set.InjOn (fun t : ℝ => t⁻¹-t) (Set.Ioo 0 1) := by
    apply StrictAntiOn.injOn
    intro x hx y _ hxy
    exact sub_lt_sub (inv_lt_inv₀ (lt_trans hx.1 hxy) hx.1 |>.mpr hxy) hxy
  apply (Set.Ioo_infinite (show (0:ℝ)<1 by norm_num)).image hinj |>.mono
  rintro _ ⟨t,ht,rfl⟩
  simpa only [eval_map,Set.mem_ofPred_eq] using h t ht.1 ht.2
end KLInvariance.Comparison
end

end OAI
