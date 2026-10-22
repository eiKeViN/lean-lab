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

-- Actual kernel proof references: five original-site calls plus the second
-- weighted-sum consumer. Both weighted consumers are inside the four-sample set.
run_elab do
  let env ← Lean.getEnv
  for (parent, child) in #[
      (`OAI.KLInvariance.finite_character_cancellation, `OAI.KLInvariance.weighted_sum_exchange),
      (`OAI.KLInvariance.finite_character_cancellation, `OAI.KLInvariance.weighted_sum_single),
      (`OAI.KLInvariance.Comparison.matrix_difference_single, `OAI.KLInvariance.weighted_sum_single),
      (`OAI.KLInvariance.Comparison.eq_of_scaled_difference_reciprocal,
        `OAI.KLInvariance.Comparison.exists_pos_sq_eq_of_mem_Ioo),
      (`OAI.KLInvariance.Comparison.eq_of_scaled_difference_reciprocal,
        `OAI.KLInvariance.Comparison.eval_difference_of_scaled_reciprocal),
      (`OAI.KLInvariance.BruhatGraph.bottom_eq_of_comparisons,
        `OAI.KLInvariance.BruhatGraph.upper_polynomial_eq_symm)] do
    let some (.thmInfo info) := env.find? parent | throwError "Missing parent theorem: {parent}"
    unless info.value.getUsedConstants.contains child do
      throwError "Expected direct proof dependency missing: {parent} → {child}"
  Lean.logInfo "Six production proof references verified; second use is within the four samples."

-- Expansion applicability checks: these are independent of the original sites,
-- but are tests, not additional production consumers.
open OAI.KLInvariance.ReflectionPlane

example (v : ℚ) :
    ((Module.preReflection (1 : ℚ) (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).comp
      (Module.preReflection (2 : ℚ) (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) -
        (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) v = -v := by
  rw [preReflection_product_sub_id_apply]
  simp
  ring

example {V : Type} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (a : V) (ha : B a a = 2) :
    B ((1 : ℝ) • a + (0 : ℝ) • a) ((1 : ℝ) • a + (0 : ℝ) • a) = 2 := by
  apply (plane_combination_norm_two_iff B hB a a ha ha 1 0).mpr
  norm_num

example {V : Type} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (a : V) (ha : B a a = 2) :
    B ((1 : ℝ) • a - (B a a * 1 + 0) • a)
      ((1 : ℝ) • a - (B a a * 1 + 0) • a) = 2 := by
  exact triple_root_norm_two B hB a a ha ha 1 0 (by norm_num)

section ExpansionIntegral
open OAI.KLInvariance.IntegralSupport
variable {R V : Type} [CommRing R] [IsDomain R] [DecidableEq V]
  {A : V → Type} [∀ x, AddCommGroup (A x)] [∀ x, Module R (A x)]
  [∀ x, Module.IsTorsionFree R (A x)] (M : Submodule R (∀ x, A x))
  (p : R) (hcut : ∀ x (m : M), p • Pi.single x (m.val x) ∈ M) (hp : p ≠ 0)
  (d : M ≃ₗ[R] Module.Dual R M)
  (hb : ∀ x m n, d (cut M p hcut x m) n = d m (cut M p hcut x n))
example (x : V) (m n : M) (hm : m ∈ supported M x) (hn : projection M x n = 0) :
    d m n = 0 := annihilates_of_supported M p hcut hp d hb x m hm n hn
example (x : V) (m : M) (hm : ∀ n : M, projection M x n = 0 → d m n = 0) :
    ∀ y, y ≠ x → m.val y = 0 := supported_of_annihilates M p hcut hp d hb x m hm
end ExpansionIntegral

section ExpansionImages
open OAI.KLInvariance.MomentGraph OAI.KLInvariance.MomentGraph.Sheaf
variable {R V E : Type} [CommRing R] [PartialOrder V] {G : OrderedGraph V E}
  {B C : Sheaf (R := R) G} (j : B.Iso C)
example (e : E) (F : Set (Outgoing (G := G) (G.source e))) (v : B.edge e) :
    (j.edge e) v ∈ (C.upwardKernel (G.source e) F).map (C.lower e) ↔
      v ∈ (B.upwardKernel (G.source e) F).map (B.lower e) := by
  simpa only [LinearEquiv.symm_apply_apply] using j.mem_lowerImage_iff_symm e F (j.edge e v)
example (e : E) (H : Set (Outgoing (G := G) (G.target e))) (z : C.edge e) :
    (∃ w ∈ C.upwardKernel (G.target e) H, (0 : R) • C.upper e w = z) ↔
      ∃ w ∈ B.upwardKernel (G.target e) H, (0 : R) • B.upper e w = (j.edge e).symm z :=
  j.mem_scaledUpperImage_iff_symm e H 0 z
end ExpansionImages

section ExpansionRoots
open OAI.KLInvariance OAI.KLInvariance.TitsSpace
example {I W : Type} [Fintype I] {M : CoxeterMatrix I} [Group W] {cs : CoxeterSystem M W}
    {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P) :
    ∃ β : PositiveRoot M cs, B.left ≠ β ∧ rootPlane B.left β = P :=
  B.exists_root_plane_complement B.left B.left_mem
end ExpansionRoots

run_elab do
  let env ← Lean.getEnv
  for name in #[`OAI.KLInvariance.ReflectionPlane.preReflection_product_sub_id_apply,
      `OAI.KLInvariance.ReflectionPlane.plane_combination_norm_two_iff,
      `OAI.KLInvariance.ReflectionPlane.triple_root_norm_two,
      `OAI.KLInvariance.IntegralSupport.annihilates_of_supported,
      `OAI.KLInvariance.IntegralSupport.supported_of_annihilates,
      `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mem_lowerImage_iff_symm,
      `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mem_scaledUpperImage_iff_symm,
      `OAI.KLInvariance.TitsSpace.PlaneBasis.exists_root_plane_complement] do
    let some doc ← Lean.findDocString? env name | throwError "Missing expansion docstring: {name}"
    if doc.trimAscii.toString.isEmpty then throwError "Empty expansion docstring: {name}"

run_elab do
  let env ← Lean.getEnv
  for (parent, child) in #[
      (`OAI.KLInvariance.ReflectionPlane.range_preReflection_product_sub_id, `OAI.KLInvariance.ReflectionPlane.preReflection_product_sub_id_apply),
      (`OAI.KLInvariance.ReflectionPlane.reflection_triple_in_plane, `OAI.KLInvariance.ReflectionPlane.plane_combination_norm_two_iff),
      (`OAI.KLInvariance.ReflectionPlane.reflection_triple_in_plane, `OAI.KLInvariance.ReflectionPlane.triple_root_norm_two),
      (`OAI.KLInvariance.IntegralSupport.supported_iff_annihilates, `OAI.KLInvariance.IntegralSupport.annihilates_of_supported),
      (`OAI.KLInvariance.IntegralSupport.supported_iff_annihilates, `OAI.KLInvariance.IntegralSupport.supported_of_annihilates),
      (`OAI.KLInvariance.MomentGraph.Sheaf.Iso.scaledImages, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mem_lowerImage_iff_symm),
      (`OAI.KLInvariance.MomentGraph.Sheaf.Iso.scaledImages, `OAI.KLInvariance.MomentGraph.Sheaf.Iso.mem_scaledUpperImage_iff_symm),
      (`OAI.KLInvariance.TitsSpace.PlaneBasis.coset_structure_scaledImages, `OAI.KLInvariance.TitsSpace.PlaneBasis.exists_root_plane_complement)] do
    let some (.thmInfo info) := env.find? parent | throwError "Missing expansion parent: {parent}"
    unless info.value.getUsedConstants.contains child do
      throwError "Missing expansion proof dependency: {parent} → {child}"
  Lean.logInfo "Eight expansion original-site references verified; no second production use claimed."
