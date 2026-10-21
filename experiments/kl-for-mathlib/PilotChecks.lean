import OAI.KL
import Lean

open OAI.KLInvariance OAI.KLInvariance.Comparison Polynomial

-- Applicability, not additional production reuse: other weights need not vanish.
example : (∑ y : Fin 3, (if y = 0 then (1 : ℤ) else 17) *
    (if y = 0 then (5 : ℤ) else 0)) = 5 := by
  exact weighted_sum_single (V := Fin 3) (C := ℤ) 0
    (fun y => if y = 0 then 1 else 17) (fun y => if y = 0 then 5 else 0)
    (by simp) (by intro y hy; simp [hy])

example : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t ^ 2 = (1 / 4 : ℝ) :=
  exists_pos_sq_eq_of_mem_Ioo (1 / 4) (by norm_num) (by norm_num)

-- A negative evaluation point shows that the clearing lemma needs nonzero,
-- not positivity. The polynomial X+1 with d=1 has reciprocal scaled evaluation.
example : (X + 1 : ℤ[X]).eval₂ (Int.castRingHom ℝ) 4 =
    4 * (X + 1 : ℤ[X]).eval₂ (Int.castRingHom ℝ) (1 / 4) := by
  have h : scaledPolynomial (-2) 1 (X + 1) - scaledPolynomial (-2) 1 0 =
      scaledPolynomial (-2 : ℝ)⁻¹ 1 (X + 1) - scaledPolynomial (-2 : ℝ)⁻¹ 1 0 := by
    norm_num [scaledPolynomial]
  have hclear := eval_difference_of_scaled_reciprocal (X + 1) 0 1 (-2) (by norm_num) h
  convert hclear using 1 <;> norm_num

-- Interface smoke check in a genuine identity interval-isomorphism context.
example {I W : Type} [Fintype I] {M : CoxeterMatrix I} [Group W]
    (cs : CoxeterSystem M W) (u b : W) (hub : BruhatLE cs u b)
    (y : Interval cs u b) (hy : y ≠ intervalBottom cs hub) :
    klPolynomial cs y.val b =
      klPolynomial cs ((OrderIso.refl (Interval cs u b)).symm y).val b := by
  exact BruhatGraph.upper_polynomial_eq_symm hub hub (OrderIso.refl _)
    (fun _ _ => rfl) y hy

run_elab do
  let env ← Lean.getEnv
  for name in #[`OAI.KLInvariance.weighted_sum_exchange,
      `OAI.KLInvariance.weighted_sum_single,
      `OAI.KLInvariance.Comparison.exists_pos_sq_eq_of_mem_Ioo,
      `OAI.KLInvariance.Comparison.eval_difference_of_scaled_reciprocal,
      `OAI.KLInvariance.BruhatGraph.upper_polynomial_eq_symm] do
    let some doc ← Lean.findDocString? env name | throwError "Missing lemma documentation: {name}"
    if doc.trimAscii.toString.isEmpty then throwError "Empty lemma documentation: {name}"
