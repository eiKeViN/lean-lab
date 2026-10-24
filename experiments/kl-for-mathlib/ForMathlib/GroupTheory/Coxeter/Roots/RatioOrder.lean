module
public import Mathlib
public import ForMathlib.Combinatorics.DirectedPaths.Subpaths
public import ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport
public import ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder. Source spans: DyerPaths:15, DyerPaths:12, DyerPaths:14, DyerPaths:18, DyerPaths:21.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_8 (p : Prop) : Decidable p := Classical.propDecidable p

@[expose] def simplePositive (i : I) : PositiveRoot M cs :=
  ⟨root i, ⟨1,i,by simp⟩, root_nonneg i⟩

@[simp] theorem simplePositive_val (i : I) :
    (simplePositive (M := M) (cs := cs) i).val = root i := rfl

@[simp] theorem rootRef_simplePositive (i : I) :
    rootRef (simplePositive (M := M) (cs := cs) i) = cs.simple i := by
  exact (rootReflection_represents M cs _).reflection_unique ⟨1,i,by simp,by simp⟩

theorem simplePositive_injective : Function.Injective (simplePositive (M := M) (cs := cs)) := by
  intro i j hij
  have he := congrArg (fun a : PositiveRoot M cs => a.val i) hij
  by_contra hne
  simp [simplePositive, root, hne] at he

theorem coordinate_sum (a : I → ℝ) : ∑ i, a i • root i = a := by
  ext j
  simp [root, Pi.single_apply, Finset.sum_apply]

theorem dual_coordinate_sum (h : Module.Dual ℝ (I → ℝ)) (a : I → ℝ) :
    h a = ∑ i, a i * h (root i) := by
  conv_lhs => rw [← coordinate_sum a]
  simp only [map_sum,map_smul,smul_eq_mul]

@[expose] def PositiveFunctional (h : Module.Dual ℝ (I → ℝ)) : Prop := ∀ i, 0 < h (root i)

theorem PositiveFunctional.root_pos {h : Module.Dual ℝ (I → ℝ)}
    (hh : PositiveFunctional h) (a : PositiveRoot M cs) : 0 < h a.val := by
  rw [dual_coordinate_sum]
  obtain ⟨i,hi⟩ : ∃ i, a.val i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact a.property.1.ne_zero (funext hn)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (a.property.2 j) (hh j).le)
    ⟨i,Finset.mem_univ _,mul_pos (lt_of_le_of_ne' (a.property.2 i) hi) (hh i)⟩

theorem height_positive : PositiveFunctional (height (I := I)) := by
  intro i
  simp [height,root]

/-- Both functionals are actual dual vectors; the root order is not a
label-carrying addition to the interval isomorphism. -/
structure RatioOrder where
  denominator : Module.Dual ℝ (I → ℝ)
  numerator : Module.Dual ℝ (I → ℝ)
  positive : PositiveFunctional denominator
  generic : Function.Injective (fun a : PositiveRoot M cs => numerator a.val / denominator a.val)

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

@[expose] def slope (a : PositiveRoot M cs) : ℝ := O.numerator a.val / O.denominator a.val

theorem denominator_pos (a : PositiveRoot M cs) : 0 < O.denominator a.val :=
  O.positive.root_pos a

theorem slope_injective : Function.Injective O.slope := O.generic

/-- The cut at zero is the genuine inversion set of the upper vertex. -/
@[expose] def Adapted (y : W) : Prop := ∀ a : PositiveRoot M cs,
  (O.slope a < 0 ↔ rootInverted y a) ∧ O.slope a ≠ 0

theorem simple_lower_bound (i : I)
    (hi : ∀ j, O.slope (simplePositive i) ≤ O.slope (simplePositive j))
    (a : PositiveRoot M cs) : O.slope (simplePositive i) ≤ O.slope a := by
  change O.slope (simplePositive i) ≤ O.numerator a.val / O.denominator a.val
  rw [le_div_iff₀ (O.denominator_pos a)]
  rw [dual_coordinate_sum O.numerator a.val, dual_coordinate_sum O.denominator a.val,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj := (le_div_iff₀ (O.positive j)).mp (hi j)
  change O.slope (simplePositive i) * O.denominator (root j) ≤ O.numerator (root j) at hj
  nlinarith [mul_nonneg (a.property.2 j) (sub_nonneg.mpr hj)]

theorem exists_least_simple [Nonempty I] : ∃ i : I,
    ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image (Finset.univ : Finset I)
    (fun i => O.slope (simplePositive i)) Finset.univ_nonempty
  exact ⟨i, O.simple_lower_bound i (fun j => hi j (Finset.mem_univ j))⟩

theorem least_simple_descent {y : W} (hy : y ≠ 1) (ha : O.Adapted y) :
    ∃ i : I, cs.IsLeftDescent y i ∧
      O.slope (simplePositive i) < 0 ∧
      ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨j,hj⟩ := cs.exists_leftDescent_of_ne_one hy
  let : Nonempty I := ⟨j⟩
  obtain ⟨i,hi⟩ := O.exists_least_simple
  have hjr : rootInverted y (simplePositive (M := M) (cs := cs) j) := by
    apply ((rootReflection_represents M cs _).inversion_iff (simplePositive j).property.2 y).mpr
    simpa only [rootRef_simplePositive] using (show cs.IsLeftInversion y (cs.simple j) from
      ⟨cs.isReflection_simple j,hj⟩)
  have hi0 := lt_of_le_of_lt (hi (simplePositive j)) ((ha _).1.mpr hjr)
  refine ⟨i,?_,hi0,hi⟩
  have hir := ((rootReflection_represents M cs _).inversion_iff
    (simplePositive i).property.2 y).mp ((ha _).1.mp hi0)
  simpa only [rootRef_simplePositive, CoxeterSystem.IsLeftDescent] using hir.2


/-- A functional in the chamber indexed by y has exactly Inv(y) as its
negative roots. This is stronger data used only to construct the order. -/
@[expose] def Chamber (y : W) : Prop := ∀ i, 0 < O.numerator (action M cs y (root i))

theorem adapted_of_chamber {y : W} (hc : O.Chamber y) : O.Adapted y := by
  let f : Module.Dual ℝ (I → ℝ) := O.numerator.comp (action M cs y).toLinearMap
  have hf : PositiveFunctional f := hc
  intro a
  have he (v : I → ℝ) : f (action M cs y⁻¹ v) = O.numerator v := by
    change O.numerator (action M cs y (action M cs y⁻¹ v)) = _
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  by_cases ha : rootInverted y a
  · have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonpos _ _ ha, map_neg, he] at hv
    have hn : O.slope a < 0 := div_neg_of_neg_of_pos (by linarith) (O.denominator_pos a)
    exact ⟨iff_of_true hn ha, hn.ne⟩
  · have hp := (not_rootInverted_iff y a).mp ha
    have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonneg _ _ hp, he] at hv
    have hn : 0 < O.slope a := div_pos hv (O.denominator_pos a)
    exact ⟨iff_of_false (not_lt.mpr hn.le) ha, hn.ne'⟩

end RatioOrder

/-- The generic functional can be chosen in any prescribed Coxeter chamber,
not just outside the countably many equality hyperplanes. The explicit
polynomial perturbation makes both requirements simultaneous. -/
theorem exists_ratioOrder_chamber_height (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y ∧ O.denominator=height := by
  classical
  let := countable_Positiveroot M cs
  let f₀ : Module.Dual ℝ (I → ℝ) := height.comp (action M cs y⁻¹).toLinearMap
  let f : ℝ → Module.Dual ℝ (I → ℝ) := fun t =>
    f₀ + t • ReflectionSchedules.momentFunctional t
  have hf (t : ℝ) (v : I → ℝ) : f t v = f₀ v +
      t * (ReflectionSchedules.coordinatePolynomial v).eval t := by
    simp [f,ReflectionSchedules.coordinatePolynomial_eval]
  let U : Set ℝ := {t | ∀ i, 0 < f t (action M cs y (root i))}
  have hu : IsOpen U := by
    change IsOpen {t | ∀ i, 0 < f t (action M cs y (root i))}
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt continuous_const
    simp only [hf]
    exact continuous_const.add (continuous_id.mul (Polynomial.continuous _))
  have h0 : 0 ∈ U := by
    intro i
    simp only [f,zero_smul,add_zero]
    change 0 < height (action M cs y⁻¹ (action M cs y (root i)))
    rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
    exact height_positive i
  let P := {p : PositiveRoot M cs × PositiveRoot M cs // p.1 ≠ p.2}
  let v : P → (I → ℝ) := fun p => normalizedRoot p.val.1 - normalizedRoot p.val.2
  let d : P → Polynomial ℝ := fun p => Polynomial.C (f₀ (v p)) +
    Polynomial.X * ReflectionSchedules.coordinatePolynomial (v p)
  have hd : ∀ p, d p ≠ 0 := by
    intro p hp
    have hz := congrArg (fun q : Polynomial ℝ => q.eval 0) hp
    have hz' : f₀ (v p) = 0 := by simpa [d] using hz
    have hq : ReflectionSchedules.coordinatePolynomial (v p) = 0 := by
      simpa only [d,hz',Polynomial.C_0,zero_add,mul_eq_zero,Polynomial.X_ne_zero,false_or] using hp
    have hv : v p = 0 := ReflectionSchedules.coordinatePolynomial_injective (by simpa [ReflectionSchedules.coordinatePolynomial] using hq)
    exact p.property (normalizedRoot_injective (sub_eq_zero.mp hv))
  let bad : Set ℝ := ⋃ p : P, {t | (d p).IsRoot t}
  have hbad : bad.Countable := Set.countable_iUnion
    (fun p => (Polynomial.finite_setOfPred_isRoot (hd p)).countable)
  obtain ⟨t,htU,ht⟩ := (hbad.dense_compl ℝ).inter_open_nonempty U hu ⟨0,h0⟩
  have hinj : Function.Injective (fun a : PositiveRoot M cs => f t a.val / height a.val) := by
    intro a b heq
    by_contra hab
    apply ht
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(a,b),hab⟩,?_⟩
    change (d ⟨(a,b),hab⟩).eval t = 0
    dsimp only [d]
    rw [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,← hf]
    change f t (normalizedRoot a - normalizedRoot b) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    simpa only [normalizedRoot,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using heq
  exact ⟨⟨height,f t,height_positive,hinj⟩,htU,rfl⟩

theorem exists_ratioOrder_chamber (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y := by
  obtain ⟨O,hO,_⟩ := exists_ratioOrder_chamber_height (M := M) (cs := cs) y
  exact ⟨O,hO⟩

@[simp] theorem positiveAction_simplePositive (i : I) :
    positiveAction (cs.simple i) (simplePositive (M := M) (cs := cs) i) = simplePositive i := by
  apply Subtype.ext
  rw [positiveAction_eq_of_nonpos]
  · simp only [simplePositive_val,action_simple_root,neg_neg]
  · simpa only [simplePositive_val,action_simple_root,Pi.neg_apply,neg_nonpos] using root_nonneg i

theorem simple_action_nonneg (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : ∀ k, 0 ≤ action M cs (cs.simple i) a.val k := by
  apply a.property.1.act (cs.simple i) |>.sign.resolve_right
  intro hn
  exact ha (Subtype.ext (a.property.1.eq_simple_of_nonpos a.property.2 i hn))

theorem simple_positiveAction_val (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (positiveAction (cs.simple i) a).val = action M cs (cs.simple i) a.val :=
  positiveAction_eq_of_nonneg _ _ (simple_action_nonneg i a ha)

theorem simple_positiveAction_ne (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : positiveAction (cs.simple i) a ≠ simplePositive i := by
  intro he
  apply ha
  exact (positiveActionEquiv (cs.simple i)).injective (he.trans (positiveAction_simplePositive i).symm)

theorem exists_uniform_pos_lt (v : I → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < v i := by
  have aux (s : Finset I) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε < v i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε,hε,hlt⟩ := ih
      refine ⟨min ε (v a / 2),lt_min hε (half_pos (hv a)),?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (hv i))
      · exact lt_of_le_of_lt (min_le_left _ _) (hlt i hi)
  obtain ⟨ε,hε,hlt⟩ := aux Finset.univ
  exact ⟨ε,hε,fun i => hlt i (Finset.mem_univ i)⟩

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

@[expose] def turnNumerator (i : I) : Module.Dual ℝ (I → ℝ) :=
  O.numerator.comp (action M cs (cs.simple i)).toLinearMap

@[expose] def turnDenominator (i : I) (k : ℝ) : Module.Dual ℝ (I → ℝ) :=
  (O.numerator - k • O.denominator).comp (action M cs (cs.simple i)).toLinearMap

theorem exists_turn_parameter (i : I) (hi0 : O.slope (simplePositive i) < 0)
    (hi : ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a) :
    ∃ k : ℝ, k < 0 ∧ O.slope (simplePositive i) < k ∧
      PositiveFunctional (O.turnDenominator i k) := by
  let c := O.slope (simplePositive i)
  let v : I → ℝ := fun j => if j=i then -c else
    O.slope (positiveAction (cs.simple i) (simplePositive j)) - c
  have hv : ∀ j, 0 < v j := by
    intro j
    by_cases hj : j=i
    · simp only [v,ite_eq_left hj]
      exact neg_pos.mpr hi0
    · simp only [v,ite_eq_right hj]
      apply sub_pos.mpr
      apply lt_of_le_of_ne (hi _)
      intro he
      exact simple_positiveAction_ne i (simplePositive j)
        (fun hh => hj (simplePositive_injective hh)) (O.slope_injective he.symm)
  obtain ⟨ε,hε,hεv⟩ := exists_uniform_pos_lt v hv
  have hεc : ε < -c := by simpa only [v,ite_eq_left rfl] using hεv i
  refine ⟨c+ε,by linarith,by dsimp [c]; linarith,?_⟩
  intro j
  change 0 < O.numerator (action M cs (cs.simple i) (root j)) -
    (c+ε)*O.denominator (action M cs (cs.simple i) (root j))
  by_cases hj : j=i
  · subst j
    rw [action_simple_root,map_neg,map_neg]
    have hc : c * O.denominator (root i) = O.numerator (root i) := by
      exact div_mul_cancel₀ _ (O.positive i).ne'
    nlinarith [mul_pos hε (O.positive i)]
  · let a := positiveAction (cs.simple i) (simplePositive (M := M) (cs := cs) j)
    have ha : a.val = action M cs (cs.simple i) (root j) :=
      simple_positiveAction_val i (simplePositive j) (fun hh => hj (simplePositive_injective hh))
    rw [← ha]
    have hvj : ε < O.slope a - c := by simpa only [v,ite_eq_right hj] using hεv j
    have hlt : c+ε < O.slope a := by linarith
    exact sub_pos.mpr ((lt_div_iff₀ (O.denominator_pos a)).mp hlt)

theorem turn_ratio_injective (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) :
    Function.Injective (fun a : PositiveRoot M cs =>
      O.turnNumerator i a.val / O.turnDenominator i k a.val) := by
  intro a b hab
  have hh (a : PositiveRoot M cs) : O.denominator (action M cs (cs.simple i) a.val) ≠ 0 := by
    rcases (a.property.1.act (cs.simple i)).sign with hpos|hneg
    · have h := O.denominator_pos (positiveAction (cs.simple i) a)
      rw [positiveAction_eq_of_nonneg _ _ hpos] at h
      exact h.ne'
    · have h := O.denominator_pos (positiveAction (cs.simple i) a)
      rw [positiveAction_eq_of_nonpos _ _ hneg,map_neg] at h
      exact (neg_pos.mp h).ne
  have hc := (div_eq_div_iff (hp.root_pos a).ne' (hp.root_pos b).ne').mp hab
  change O.numerator (action M cs (cs.simple i) a.val) *
      (O.numerator (action M cs (cs.simple i) b.val) -
        k*O.denominator (action M cs (cs.simple i) b.val)) =
    O.numerator (action M cs (cs.simple i) b.val) *
      (O.numerator (action M cs (cs.simple i) a.val) -
        k*O.denominator (action M cs (cs.simple i) a.val)) at hc
  have hcross : O.numerator (action M cs (cs.simple i) a.val) *
      O.denominator (action M cs (cs.simple i) b.val) =
    O.numerator (action M cs (cs.simple i) b.val) *
      O.denominator (action M cs (cs.simple i) a.val) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show k * (O.numerator (action M cs (cs.simple i) a.val) *
      O.denominator (action M cs (cs.simple i) b.val) -
        O.numerator (action M cs (cs.simple i) b.val) *
      O.denominator (action M cs (cs.simple i) a.val)) = 0 by nlinarith [hc])).resolve_left hk
  have he := (div_eq_div_iff (hh a) (hh b)).mpr hcross
  have hval (a : PositiveRoot M cs) :
      O.numerator (action M cs (cs.simple i) a.val) /
          O.denominator (action M cs (cs.simple i) a.val) =
        O.slope (positiveAction (cs.simple i) a) := by
    unfold slope
    rcases (a.property.1.act (cs.simple i)).sign with hpos|hneg
    · rw [positiveAction_eq_of_nonneg _ _ hpos]
    · rw [positiveAction_eq_of_nonpos _ _ hneg,map_neg,map_neg,neg_div_neg_eq]
  rw [hval a,hval b] at he
  exact (positiveActionEquiv (cs.simple i)).injective (O.slope_injective he)

@[expose] def turn (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) : RatioOrder (M := M) (cs := cs) :=
  ⟨O.turnDenominator i k,O.turnNumerator i,hp,O.turn_ratio_injective i k hk hp⟩


theorem turn_chamber (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) {y : W} (hy : O.Chamber y) :
    (O.turn i k hk hp).Chamber (cs.simple i * y) := by
  intro j
  change 0 < O.numerator (action M cs (cs.simple i)
    (action M cs (cs.simple i * y) (root j)))
  rw [← LinearEquiv.mul_apply,← map_mul,cs.simple_mul_simple_cancel_left]
  exact hy j

theorem turn_simple_greatest (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope a < (O.turn i k hk.ne hp).slope (simplePositive i) := by
  have hlt : (O.turn i k hk.ne hp).slope a < 1 := by
    apply (div_lt_iff₀ (hp.root_pos a)).mpr
    change O.numerator (action M cs (cs.simple i) a.val) <
      1 * (O.numerator (action M cs (cs.simple i) a.val) -
        k * O.denominator (action M cs (cs.simple i) a.val))
    have hap := O.denominator_pos (positiveAction (cs.simple i) a)
    rw [simple_positiveAction_val i a ha] at hap
    nlinarith [mul_neg_of_neg_of_pos hk hap]
  have hgt : 1 < (O.turn i k hk.ne hp).slope (simplePositive i) := by
    apply (lt_div_iff₀ (hp.root_pos (simplePositive i))).mpr
    change 1 * (O.numerator (action M cs (cs.simple i) (root i)) -
       k * O.denominator (action M cs (cs.simple i) (root i))) <
      O.numerator (action M cs (cs.simple i) (root i))
    rw [action_simple_root,map_neg,map_neg]
    nlinarith [mul_neg_of_neg_of_pos hk (O.positive i)]
  exact hlt.trans hgt

theorem turn_slope_lt_iff (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k))
    (a b : PositiveRoot M cs) (ha : a ≠ simplePositive i) (hb : b ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) a) <
      (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) b) ↔ O.slope a < O.slope b := by
  have hact (a : PositiveRoot M cs) (ha : a ≠ simplePositive i) :
      action M cs (cs.simple i) (positiveAction (cs.simple i) a).val = a.val := by
    rw [simple_positiveAction_val i a ha,← LinearEquiv.mul_apply,← map_mul,
      (cs.isReflection_simple i).mul_self,map_one]
    rfl
  have haD := hp.root_pos (positiveAction (cs.simple i) a)
  have hbD := hp.root_pos (positiveAction (cs.simple i) b)
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) at haD
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) at hbD
  rw [hact a ha] at haD
  rw [hact b hb] at hbD
  change O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val)) <
    O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val)) ↔
    O.numerator a.val / O.denominator a.val < O.numerator b.val / O.denominator b.val
  rw [hact a ha,hact b hb,div_lt_div_iff₀ haD hbD,
    div_lt_div_iff₀ (O.denominator_pos a) (O.denominator_pos b)]
  constructor
  · intro h
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg hk.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  · intro h
    have := mul_neg_of_neg_of_pos hk (sub_pos.mpr h)
    nlinarith

/-- The actual geometric rotation needed for the Hecke recursion. It moves
the least simple root to last and preserves all other root comparisons. -/
theorem exists_rotation {y : W} (hy : y ≠ 1) (hc : O.Chamber y) :
    ∃ (i : I) (O' : RatioOrder (M := M) (cs := cs)),
      cs.IsLeftDescent y i ∧ O'.Chamber (cs.simple i * y) ∧
      (∀ a : PositiveRoot M cs, a ≠ simplePositive i →
        O.slope (simplePositive i) < O.slope a ∧ O'.slope a < O'.slope (simplePositive i)) ∧
      (∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
        (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
          O.slope a < O.slope b)) := by
  obtain ⟨i,hi,hi0,hmin⟩ := O.least_simple_descent hy (O.adapted_of_chamber hc)
  obtain ⟨k,hk,_,hpos⟩ := O.exists_turn_parameter i hi0 hmin
  refine ⟨i,O.turn i k hk.ne hpos,hi,O.turn_chamber i k hk.ne hpos hc,?_,?_⟩
  · intro a ha
    exact ⟨lt_of_le_of_ne (hmin a) (fun he => ha (O.slope_injective he).symm),
      O.turn_simple_greatest i k hk hpos a ha⟩
  · exact O.turn_slope_lt_iff i k hk hpos

end RatioOrder

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem inverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : rootInverted w a) (hb : rootInverted w b) :
    rootInverted w c := by
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr (ha i))
    (mul_nonpos_of_nonneg_of_nonpos hs (hb i))

/-- Incoming graph labels are actual inversions at their upper vertex. -/
theorem graphRoot_inverted_target {x y : W} (h : BruhatStep cs x y) :
    rootInverted y (graphRoot h) := by
  apply ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 y).mpr
  refine ⟨h.label_reflection, ?_⟩
  have he : (y*x⁻¹)*y=x := by
    calc
      (y*x⁻¹)*y = (y*x⁻¹)*((y*x⁻¹)*x) := by group
      _ = x := by rw [← mul_assoc,h.label_reflection.mul_self,one_mul]
  simpa only [he] using h.1

/-- Outgoing graph labels are actual noninversions at their lower vertex. -/
theorem graphRoot_not_inverted_source {x y : W} (h : BruhatStep cs x y) :
    ¬ rootInverted x (graphRoot h) := by
  intro hi
  have hh := ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 x).mp hi
  have he : (y*x⁻¹)*x=y := by group
  have hh' := hh.2
  rw [he] at hh'
  exact lt_asymm h.1 hh'

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- In a plane with its first simple root inverted, every noninverted root
is later than every inverted root. This uses convexity, not a signed-index
formula for a particular realization. -/
theorem slope_lt_of_inverted_left (w : W) (hl : rootInverted w B.left)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b := by
  by_contra h
  have hba : geometricSlope b < geometricSlope a :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hlb : geometricSlope B.left < geometricSlope b :=
    lt_of_le_of_ne (B.left_min b hbP) (fun he => hb (geometricSlope_injective he ▸ hl))
  have heq : rootPlane B.left a = P :=
    rootPlane_eq_of_mem B.left B.right B.left a B.distinct
      (Submodule.subset_span (Set.mem_insert _ _))
      (B.plane_eq.ge haP) (fun he => by rw [he] at hlb; exact (lt_asymm hlb hba)) |>.trans B.plane_eq
  obtain ⟨r,s,hr,hs,hc⟩ := positive_combination_of_slope_between B.left a b
    (heq.symm ▸ hbP) hlb hba
  exact hb (inverted_of_positive_combination w B.left a b hr.le hs.le hc hl ha)

/-- The other angular cut, when the last simple root is inverted. -/
theorem slope_lt_of_inverted_right (w : W) (hr : rootInverted w B.right)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope b < geometricSlope a := by
  by_contra h
  have hab : geometricSlope a < geometricSlope b :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hbr : geometricSlope b < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max b hbP) (fun he => hb (geometricSlope_injective he ▸ hr))
  have har : a ≠ B.right := by
    intro he
    rw [he] at hab
    exact lt_asymm hbr hab
  have heq : rootPlane a B.right = P :=
    (rootPlane_eq_of_mem B.left B.right a B.right B.distinct
      (B.plane_eq.ge haP) (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      har).trans B.plane_eq
  obtain ⟨r,s,hrr,hss,hc⟩ := positive_combination_of_slope_between a B.right b
    (heq.symm ▸ hbP) hab hbr
  exact hb (inverted_of_positive_combination w a B.right b hrr.le hss.le hc ha hr)

/-- In the mixed-sign case the angular cut is determined by the first
canonical simple root. In particular the comparison of consecutive path
labels depends only on their middle vertex. -/
theorem slope_lt_iff_inverted_left (w : W)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b ↔ rootInverted w B.left := by
  constructor
  · intro hab
    by_contra hl
    have hr : rootInverted w B.right := by
      by_contra hr
      obtain ⟨r,s,hrr,hss,he⟩ := B.positive_cone a haP
      exact noninverted_of_positive_combination w B.left B.right a hrr hss he hl hr ha
    exact lt_asymm hab (B.slope_lt_of_inverted_right w hr a b haP hbP ha hb)
  · intro hl
    exact B.slope_lt_of_inverted_left w hl a b haP hbP ha hb

/-- The exact middle-vertex test for two ascending graph arrows with both
labels in this root plane. -/
theorem consecutive_slopes_iff {x y z : W}
    (hxy : BruhatStep cs x y) (hyz : BruhatStep cs y z)
    (ha : (graphRoot hxy).val ∈ P) (hb : (graphRoot hyz).val ∈ P) :
    geometricSlope (graphRoot hxy) < geometricSlope (graphRoot hyz) ↔
      rootInverted y B.left :=
  B.slope_lt_iff_inverted_left y _ _ ha hb
    (graphRoot_inverted_target hxy) (graphRoot_not_inverted_source hyz)

end PlaneBasis
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The ambient sign of a canonical plane root in a minimal coset is the
intrinsic simple-descent sign, with the original left labels. -/
theorem simpleRoot_inverted_coset_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) (i : Bool) :
    rootInverted ((w : W)*a₀) (B.simpleRoot i) ↔ B.system.IsLeftDescent w i := by
  change (∀ k, action M cs ((w : W)*a₀)⁻¹ (B.simpleRoot i).val k ≤ 0) ↔ _
  rw [root_inversion_coset_iff hmin w.property (B.simpleRoot i).property.1
    (B.simpleRoot_mem i)]
  have hr : Represents M cs (B.system.simple i : W) (B.simpleRoot i).val := by
    rw [B.system_simple]
    exact rootReflection_represents M cs _
  rw [B.inversion_iff hr (B.simpleRoot_mem i) (B.simpleRoot i).property.2 w]
  exact B.system.isLeftInversion_simple_iff_isLeftDescent w i

/-- Geometric label of an intrinsic graph edge, taken in the actual ambient
root plane rather than an abstract alternate representation. -/
@[expose] def edgeRoot {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    PositiveRoot M cs := graphRoot ((B.bruhatStep_iff x y).mpr h)

theorem edgeRoot_plane {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    (B.edgeRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents
    ((B.bruhatStep_iff x y).mpr h))).mp
  exact (planeSubgroup M cs P).mul_mem y.property
    ((planeSubgroup M cs P).inv_mem x.property)

/-- In the intrinsic system, the middle-vertex test uses its actual left
simple generator; it therefore applies to any induced dihedral realization. -/
theorem edgeRoot_slopes_iff {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      B.system.IsLeftDescent y false := by
  unfold edgeRoot
  rw [B.consecutive_slopes_iff ((B.bruhatStep_iff x y).mpr hxy)
    ((B.bruhatStep_iff y z).mpr hyz) (B.edgeRoot_plane hxy) (B.edgeRoot_plane hyz)]
  have hmin : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  simpa only [mul_one, simpleRoot, Bool.false_eq_true, ↓reduceIte] using
    B.simpleRoot_inverted_coset_iff hmin y false

end PlaneBasis
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph
local instance _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem edgeRoot_ne_of_path {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    B.edgeRoot hxy ≠ B.edgeRoot hyz :=
  graphRoot_ne_of_path ((B.bruhatStep_iff x y).mpr hxy) ((B.bruhatStep_iff y z).mpr hyz)

/-- At every internal vertex, the cut switches side under the path involution.
This is the local relation behind rank-two path-product reversal. -/
theorem edgeRoot_slopes_rankFlip {x y z top : planeSubgroup M cs P} {L : ℕ}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z)
    (hL : L < B.system.length y) (hH : B.system.length y < B.system.length top) :
    let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
    let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      geometricSlope (B.edgeRoot hz) < geometricSlope (B.edgeRoot hx) := by
  dsimp only
  let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
  let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
  have hsign : B.system.IsLeftDescent
      (rankFlip B.system L (B.system.length top) y) false ↔
      ¬ B.system.IsLeftDescent y false := by
    rw [rankFlip,ite_eq_left ⟨hL,hH⟩]
    exact descent_swap_false_iff_not B.system (by omega) hH
  have hne : geometricSlope (B.edgeRoot hx) ≠ geometricSlope (B.edgeRoot hz) :=
    fun he => B.edgeRoot_ne_of_path hx hz (geometricSlope_injective he)
  rw [B.edgeRoot_slopes_iff]
  constructor
  · intro hi
    have hn : ¬ geometricSlope (B.edgeRoot hx) < geometricSlope (B.edgeRoot hz) := by
      rw [B.edgeRoot_slopes_iff,hsign]
      exact not_not.mpr hi
    exact lt_of_le_of_ne (le_of_not_gt hn) hne.symm
  · intro hi
    by_contra hn
    have hlt := (B.edgeRoot_slopes_iff hx hz).mpr (hsign.mpr hn)
    exact lt_asymm hlt hi

/-- Restriction of the actual geometric root slope to a full plane interval. -/
@[expose] def intervalEdgeSlope (lo hi : planeSubgroup M cs P) (e : Edge B.system lo hi) : ℝ :=
  geometricSlope (B.edgeRoot e.property)

/-- The global edge map reverses the comparison for every composable pair.
No statement is asserted for disjoint edge labels, which can share ties. -/
theorem intervalEdgeSlope_flip {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi e < B.intervalEdgeSlope lo hi f ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) := by
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  have hl : B.system.length lo < B.system.length ey.val :=
    lt_of_le_of_lt (length_le_of_bruhat B.system ex.property.1) he.1
  have hh : B.system.length ey.val < B.system.length hi :=
    lt_of_lt_of_le hf.1 (length_le_of_bruhat B.system fy.property.2)
  exact B.edgeRoot_slopes_rankFlip he hf hl hh

end PlaneBasis
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph SchedulePaths
local instance _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_1 (p : Prop) : Decidable p := Classical.propDecidable p

theorem intervalEdgeSlope_ties {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi) (heq : B.intervalEdgeSlope lo hi e = B.intervalEdgeSlope lo hi f) :
    target B.system lo hi e ≠ source B.system lo hi f := by
  intro hjoin
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  exact B.edgeRoot_ne_of_path he hf (geometricSlope_injective heq)

theorem intervalEdgeSlope_flip_reverse {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi f < B.intervalEdgeSlope lo hi e ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) := by
  have hj : target B.system lo hi (edgeFlip B.system lo hi e) =
      source B.system lo hi (edgeFlip B.system lo hi f) := by
    simpa only [edgeFlip_source,edgeFlip_target] using congrArg (intervalFlip B.system lo hi) hjoin
  simpa only [edgeFlip_involutive B.system lo hi e, edgeFlip_involutive B.system lo hi f] using
    (B.intervalEdgeSlope_flip (edgeFlip B.system lo hi e) (edgeFlip B.system lo hi f) hj).symm

/-- Rank-two reversal of the genuine path-product entry between the two
ends of any full interval. The order is the actual induced angular order. -/
theorem dispatch_reverse_endpoints {R : Type*} [Semiring R]
    {lo hi : planeSubgroup M cs P} (hlohi : BruhatLE B.system lo hi)
    (schedule : List (Edge B.system lo hi)) (hnd : schedule.Nodup)
    (hfull : ∀ e, e ∈ schedule)
    (hs : schedule.Pairwise (fun e f => B.intervalEdgeSlope lo hi f ≤ B.intervalEdgeSlope lo hi e))
    (T : R) :
    let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
    let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule x =
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule.reverse x := by
  dsimp only
  let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
  let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
  have hx : intervalFlip B.system lo hi x=x := Subtype.ext (rankFlip_lower B.system lo hi)
  have hy : intervalFlip B.system lo hi y=y := Subtype.ext (rankFlip_upper B.system lo hi)
  have hrs : schedule.reverse.Pairwise
      (fun e f => -B.intervalEdgeSlope lo hi f ≤ -B.intervalEdgeSlope lo hi e) := by
    rw [List.pairwise_reverse]
    exact hs.imp (fun h => neg_le_neg h)
  have hrfull : ∀ e, e ∈ schedule.reverse := fun e => List.mem_reverse.mpr (hfull e)
  apply dispatch_eq_of_path_involution _ _ T schedule schedule.reverse hnd (List.nodup_reverse.mpr hnd) x y
    (edgeFlip B.system lo hi) (edgeFlip_involutive B.system lo hi)
  · apply subpaths_map_of_sorted _ _ (B.intervalEdgeSlope lo hi)
      (fun e => -B.intervalEdgeSlope lo hi e) schedule schedule.reverse x y hs hrs hrfull
      (B.intervalEdgeSlope_ties) (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact neg_lt_neg ((B.intervalEdgeSlope_flip_reverse e f hj).mp hlt)
  · apply subpaths_map_of_sorted _ _ (fun e => -B.intervalEdgeSlope lo hi e)
      (B.intervalEdgeSlope lo hi) schedule.reverse schedule x y hrs hs hfull
      (fun e f he => B.intervalEdgeSlope_ties e f (neg_injective he))
      (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact (B.intervalEdgeSlope_flip e f hj).mp (neg_lt_neg_iff.mp hlt)

end PlaneBasis
end
end KLInvariance.TitsSpace
end

end OAI
