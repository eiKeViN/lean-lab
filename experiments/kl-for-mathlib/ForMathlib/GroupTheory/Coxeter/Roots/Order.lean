import Mathlib
import ForMathlib.GroupTheory.Coxeter.Roots.Basic
import ForMathlib.LinearAlgebra.Avoidance

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.Order. Source spans: ReflectionSchedules:2, ReflectionSchedules:3, ReflectionSchedules:4, ReflectionSchedules:5, ReflectionSchedules:7, ReflectionSchedules:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

def height : Module.Dual ℝ (I → ℝ) where
  toFun a := ∑ i, a i
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.mul_sum]

variable {M cs}

theorem PositiveRoot.height_pos (a : PositiveRoot M cs) : 0 < height a.val := by
  classical
  have hex : ∃ i, a.val i ≠ 0 := by
    by_contra h
    push Not at h
    exact a.property.1.ne_zero (funext h)
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => a.property.2 j)
    ⟨i,Finset.mem_univ _,lt_of_le_of_ne' (a.property.2 i) hi⟩

def normalizedRoot (a : PositiveRoot M cs) : I → ℝ := (height a.val)⁻¹ • a.val

theorem normalizedRoot_injective : Function.Injective (normalizedRoot (M := M) (cs := cs)) := by
  intro a b hab
  have ha : 0 < (height a.val)⁻¹ := inv_pos.mpr a.height_pos
  have hb : 0 < (height b.val)⁻¹ := inv_pos.mpr b.height_pos
  have hn := congrArg (fun v => form M v v) hab
  change form M ((height a.val)⁻¹ • a.val) ((height a.val)⁻¹ • a.val) =
    form M ((height b.val)⁻¹ • b.val) ((height b.val)⁻¹ • b.val) at hn
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,a.property.1.norm,b.property.1.norm] at hn
  have hh : (height a.val)⁻¹ = (height b.val)⁻¹ := by nlinarith
  apply Subtype.ext
  change (height a.val)⁻¹ • a.val = (height b.val)⁻¹ • b.val at hab
  rw [← hh] at hab
  exact (smul_right_injective _ ha.ne').eq_iff.mp hab

variable (M cs)

theorem countable_Positiveroot : Countable (PositiveRoot M cs) := by
  let : Countable W := cs.wordProd_surjective.countable
  exact Countable.of_equiv {t : W // cs.IsReflection t} (positiveRootEquiv M cs)


theorem exists_geometric_functional : ∃ f : Module.Dual ℝ (I → ℝ),
    Function.Injective (fun a : PositiveRoot M cs => f a.val / height a.val) := by
  let := countable_Positiveroot M cs
  obtain ⟨f,hf⟩ := ReflectionSchedules.exists_generic_functional
    (normalizedRoot (M := M) (cs := cs)) normalizedRoot_injective
  refine ⟨f,?_⟩
  convert hf using 1
  funext a
  simp [normalizedRoot,div_eq_mul_inv,mul_comm]

/-- Betweenness of all positive combinations is the angular-order condition
on every root plane. This is the genuine geometric reflection-order property. -/
theorem functionalRatio_between (f : Module.Dual ℝ (I → ℝ))
    (a b c : PositiveRoot M cs) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hc : c.val = r • a.val + s • b.val)
    (hab : f a.val / height a.val < f b.val / height b.val) :
    f a.val / height a.val < f c.val / height c.val ∧
      f c.val / height c.val < f b.val / height b.val := by
  have ha := a.height_pos
  have hb := b.height_pos
  have hh := c.height_pos
  have hfc : f c.val = r*f a.val+s*f b.val := by rw [hc]; simp
  have hhc : height c.val = r*height a.val+s*height b.val := by rw [hc]; simp
  rw [div_lt_div_iff₀ ha hb] at hab
  constructor
  · rw [div_lt_div_iff₀ ha hh,hfc,hhc]
    nlinarith [mul_pos hs (sub_pos.mpr hab)]
  · rw [div_lt_div_iff₀ hh hb,hfc,hhc]
    nlinarith [mul_pos hr (sub_pos.mpr hab)]

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

/-- Conjugation on the actual root lines, represented by positive roots. -/
def positiveAction (w : W) (a : PositiveRoot M cs) : PositiveRoot M cs :=
  positiveRoot M cs ⟨w * (rootReflection M cs a).val * w⁻¹,
    (rootReflection M cs a).property.conj w⟩

theorem positiveAction_represents (w : W) (a : PositiveRoot M cs) :
    Represents M cs (w * (rootReflection M cs a).val * w⁻¹) (positiveAction w a).val :=
  positiveRoot_represents M cs ⟨w * (rootReflection M cs a).val * w⁻¹,
    (rootReflection M cs a).property.conj w⟩

theorem positiveAction_eq_of_nonneg (w : W) (a : PositiveRoot M cs)
    (hp : ∀ i, 0 ≤ action M cs w a.val i) :
    (positiveAction w a).val = action M cs w a.val :=
  (positiveAction_represents w a).unique_positive
    ((rootReflection_represents M cs a).act w) (positiveAction w a).property.2 hp

theorem positiveAction_eq_of_nonpos (w : W) (a : PositiveRoot M cs)
    (hn : ∀ i, action M cs w a.val i ≤ 0) :
    (positiveAction w a).val = -action M cs w a.val :=
  (positiveAction_represents w a).unique_positive
    ((rootReflection_represents M cs a).act w).neg (positiveAction w a).property.2
    (fun i => neg_nonneg.mpr (hn i))

@[simp] theorem rootReflection_positiveAction (w : W) (a : PositiveRoot M cs) :
    (rootReflection M cs (positiveAction w a)).val = w*(rootReflection M cs a).val*w⁻¹ :=
  (rootReflection_represents M cs _).reflection_unique (positiveAction_represents w a)

@[simp] theorem positiveAction_one (a : PositiveRoot M cs) : positiveAction 1 a = a := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction 1 a)).val = (rootReflection M cs a).val
  simp

theorem positiveAction_mul (w z : W) (a : PositiveRoot M cs) :
    positiveAction (w*z) a = positiveAction w (positiveAction z a) := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction (w*z) a)).val =
    (rootReflection M cs (positiveAction w (positiveAction z a))).val
  simp only [rootReflection_positiveAction]
  group

def positiveActionEquiv (w : W) : Equiv.Perm (PositiveRoot M cs) where
  toFun := positiveAction w
  invFun := positiveAction w⁻¹
  left_inv a := by rw [← positiveAction_mul, inv_mul_cancel, positiveAction_one]
  right_inv a := by rw [← positiveAction_mul, mul_inv_cancel, positiveAction_one]

abbrev rootRef (a : PositiveRoot M cs) : W := (rootReflection M cs a).val

theorem positiveAction_involutive (a : PositiveRoot M cs) :
    Function.Involutive (positiveAction (M := M) (cs := cs) (rootRef a)) := by
  intro b
  rw [← positiveAction_mul, (rootReflection M cs a).property.mul_self, positiveAction_one]

def rootInverted (w : W) (a : PositiveRoot M cs) : Prop :=
  ∀ i, action M cs w⁻¹ a.val i ≤ 0

theorem not_rootInverted_iff (w : W) (a : PositiveRoot M cs) :
    ¬ rootInverted w a ↔ ∀ i, 0 ≤ action M cs w⁻¹ a.val i := by
  constructor
  · intro hn
    exact (a.property.1.act w⁻¹).sign.resolve_right hn
  · intro hp hn
    exact (a.property.1.act w⁻¹).not_both hp hn

theorem rootInverted_mul_of_nonneg (x : W) (a b : PositiveRoot M cs)
    (hp : ∀ i, 0 ≤ action M cs (rootRef a) b.val i) :
    rootInverted (rootRef a*x) b ↔ rootInverted x (positiveAction (rootRef a) b) := by
  unfold rootInverted
  rw [positiveAction_eq_of_nonneg _ _ hp, mul_inv_rev, (rootReflection M cs a).property.inv,
    map_mul]
  rfl

theorem rootInverted_mul_of_nonpos (x : W) (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    rootInverted (rootRef a*x) b ↔ ¬ rootInverted x (positiveAction (rootRef a) b) := by
  rw [not_rootInverted_iff]
  unfold rootInverted
  rw [positiveAction_eq_of_nonpos _ _ hn, mul_inv_rev, (rootReflection M cs a).property.inv,
    map_mul, map_neg]
  simp only [LinearEquiv.mul_apply, Pi.neg_apply, neg_nonneg]

theorem negative_pair_sum (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    b.val + (positiveAction (rootRef a) b).val = form M a.val b.val • a.val := by
  rw [positiveAction_eq_of_nonpos _ _ hn, (rootReflection_represents M cs a).action_formula]
  module

theorem negative_pair_coefficient_pos (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) : 0 < form M a.val b.val := by
  have h := congrArg (fun z => height z) (negative_pair_sum a b hn)
  simp only [map_add,map_smul,smul_eq_mul] at h
  have hp := b.height_pos
  have hq := (positiveAction (rootRef a) b).height_pos
  have ha := a.height_pos
  nlinarith

/-- The crucial direct positivity argument: over an ascent in alpha, the
negative root-pair for its reflection cannot both already be inversions.
This works in degenerate planes and does not assume a dihedral presentation. -/
theorem negative_pair_not_both (x : W) (a b : PositiveRoot M cs)
    (hx : ¬ rootInverted x a)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    ¬ (rootInverted x b ∧ rootInverted x (positiveAction (rootRef a) b)) := by
  rintro ⟨hb,hc⟩
  have hp := (not_rootInverted_iff x a).mp hx
  have hs := congrArg (action M cs x⁻¹) (negative_pair_sum a b hn)
  simp only [map_add,map_smul] at hs
  have hcoef := negative_pair_coefficient_pos a b hn
  have hna : ∀ i, action M cs x⁻¹ a.val i ≤ 0 := by
    intro i
    have hi := congrFun hs i
    change action M cs x⁻¹ b.val i +
      action M cs x⁻¹ (positiveAction (rootRef a) b).val i =
        form M a.val b.val * action M cs x⁻¹ a.val i at hi
    have hb' := hb i
    have hc' := hc i
    nlinarith
  exact (a.property.1.act x⁻¹).not_both hp hna

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
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_rootInverted (w : W) : {a : PositiveRoot M cs | rootInverted w a}.Finite := by
  exact Set.finite_coe_iff.mp (rootInversions_finite M cs w)

def inversionVector (w : W) : PositiveRoot M cs →₀ ℤ := by
  classical
  refine Finsupp.ofSupportFinite (fun a => if rootInverted w a then 1 else 0) ?_
  simpa only [Function.support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] using finite_rootInverted (M := M) (cs := cs) w

@[simp] theorem inversionVector_apply (w : W) (a : PositiveRoot M cs) :
    inversionVector w a = if rootInverted w a then 1 else 0 := by
  classical
  rfl

theorem inversionVector_sum (w : W) : (inversionVector (M := M) (cs := cs) w).sum
    (fun _ n => n) = (cs.length w : ℤ) := by
  classical
  let f := inversionVector (M := M) (cs := cs) w
  have hh : f.support.card = cs.length w := by
    have heq : (f.support : Set (PositiveRoot M cs)) = {a | rootInverted w a} := by
      ext a
      simp [f]
    rw [← Set.ncard_coe_finset, heq, ← Nat.card_coe_set_eq]
    exact card_rootInversions M cs w
  rw [Finsupp.sum]
  calc
    ∑ a ∈ f.support, f a = ∑ _a ∈ f.support, (1:ℤ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hm := Finsupp.mem_support_iff.mp ha
      by_cases hi : rootInverted w a
      · simp [f,hi]
      · simp [f,hi] at hm
    _ = _ := by simp [hh]

def rootChange (x y : W) : PositiveRoot M cs →₀ ℤ := inversionVector y - inversionVector x

def rootPlane (a b : PositiveRoot M cs) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ {a.val,b.val}

/-- The finitely supported change in root inversions, with the distinguished
root removed, grouped by actual root planes. -/
def planeDefect (x y : W) (a : PositiveRoot M cs) : Submodule ℝ (I → ℝ) →₀ ℤ :=
  Finsupp.mapDomain (rootPlane a) ((rootChange x y).erase a)

theorem rootInverted_mul_self (x : W) (a : PositiveRoot M cs) :
    rootInverted (rootRef a*x) a ↔ ¬ rootInverted x a := by
  have h := (rootReflection M cs a).property.isLeftInversion_mul_right_iff (w := x)
  simpa only [rootInverted, ← (rootReflection_represents M cs a).inversion_iff a.property.2] using h

theorem rootChange_distinguished (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a) : rootChange x (rootRef a*x) a = 1 := by
  classical
  simp only [rootChange, Finsupp.sub_apply, inversionVector_apply,
    (rootInverted_mul_self x a).mpr hx, hx, ite_true, ite_false, sub_zero]


theorem planeDefect_sum (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    (planeDefect x (rootRef a*x) a).sum (fun _ n => n) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  classical
  rw [planeDefect, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.erase_eq_sub_single, Finsupp.sum_sub_index (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, rootChange_distinguished x a hx,
    rootChange, Finsupp.sum_sub_index (fun _ _ _ => rfl),
    inversionVector_sum, inversionVector_sum]

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
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_1 (p : Prop) : Decidable p := Classical.propDecidable p

abbrev partner (a b : PositiveRoot M cs) := positiveAction (rootRef a) b

theorem partner_self (a : PositiveRoot M cs) : partner a a = a := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction (rootRef a) a)).val = rootRef a
  rw [rootReflection_positiveAction, (rootReflection M cs a).property.mul_self, one_mul,
    (rootReflection M cs a).property.inv]

theorem partner_involutive (a : PositiveRoot M cs) : Function.Involutive (partner a) :=
  positiveAction_involutive a

theorem partner_eq_self_of_eq (a b : PositiveRoot M cs) : partner a b = a ↔ b = a := by
  constructor
  · intro h
    have hh := congrArg (partner a) h
    rwa [partner_involutive a b,partner_self] at hh
  · rintro rfl
    exact partner_self _

abbrev flipped (a b : PositiveRoot M cs) : Prop :=
  ∀ i, action M cs (rootRef a) b.val i ≤ 0

theorem flipped_partner_iff (a b : PositiveRoot M cs) : flipped a (partner a b) ↔ flipped a b := by
  have hact : action M cs (rootRef a) * action M cs (rootRef a) = 1 := by
    rw [← map_mul, (rootReflection M cs a).property.mul_self, map_one]
  by_cases hb : flipped a b
  · have heq := positiveAction_eq_of_nonpos (rootRef a) b hb
    have hp : flipped a (partner a b) := by
      intro i
      change action M cs (rootRef a) (positiveAction (rootRef a) b).val i ≤ 0
      rw [heq,map_neg, ← LinearEquiv.mul_apply,hact]
      exact neg_nonpos.mpr (b.property.2 i)
    exact iff_of_true hp hb
  · have hpos := (b.property.1.act (rootRef a)).sign.resolve_right hb
    have heq := positiveAction_eq_of_nonneg (rootRef a) b hpos
    have hp : ¬ flipped a (partner a b) := by
      intro hh
      have hneg : ∀ i, b.val i ≤ 0 := by
        intro i
        have hi := hh i
        change action M cs (rootRef a) (positiveAction (rootRef a) b).val i ≤ 0 at hi
        rwa [heq, ← LinearEquiv.mul_apply, hact] at hi
      exact b.property.1.not_both b.property.2 hneg
    exact iff_of_false hp hb

theorem partner_mem {P : Submodule ℝ (I → ℝ)} (a b : PositiveRoot M cs)
    (ha : a.val ∈ P) (hb : b.val ∈ P) : (partner a b).val ∈ P := by
  have hm : action M cs (rootRef a) b.val ∈ P := by
    rw [(rootReflection_represents M cs a).action_formula]
    exact P.sub_mem hb (P.smul_mem _ ha)
  rcases (b.property.1.act (rootRef a)).sign with hp|hn
  · exact (positiveAction_eq_of_nonneg (rootRef a) b hp).symm ▸ hm
  · exact (positiveAction_eq_of_nonpos (rootRef a) b hn).symm ▸ P.neg_mem hm

theorem rootPlane_partner (a b : PositiveRoot M cs) : rootPlane a (partner a b) = rootPlane a b := by
  have hle (b : PositiveRoot M cs) : rootPlane a (partner a b) ≤ rootPlane a b := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|hz
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · rcases Set.mem_singleton_iff.mp hz with rfl
      exact partner_mem a b (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  exact le_antisymm (hle b) (by simpa only [partner_involutive a b] using hle (partner a b))

theorem negative_partner_fixed (a b : PositiveRoot M cs) (hn : flipped a b)
    (heq : partner a b = b) : b = a := by
  have hs := negative_pair_sum a b hn
  change b.val + (partner a b).val = form M a.val b.val • a.val at hs
  rw [heq] at hs
  have hc := negative_pair_coefficient_pos a b hn
  have hb : b.val = (form M a.val b.val / 2) • a.val := by
    calc
      b.val = (1/2:ℝ) • (b.val+b.val) := by module
      _ = _ := by rw [hs]; module
  have hnorm := b.property.1.norm
  rw [hb] at hnorm
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,a.property.1.norm] at hnorm
  have hc2 : form M a.val b.val / 2 = 1 := by nlinarith
  apply Subtype.ext
  simpa only [hc2,one_smul] using hb

/-- Roots in a negative pair which are both positive before the ascent. -/
def goodPairRoot (x : W) (a b : PositiveRoot M cs) : Prop :=
  flipped a b ∧ ¬ rootInverted x b ∧ ¬ rootInverted x (partner a b)

theorem goodPairRoot_partner (x : W) (a b : PositiveRoot M cs) :
    goodPairRoot x a (partner a b) ↔ goodPairRoot x a b := by
  simp only [goodPairRoot,flipped_partner_iff,partner_involutive a b]
  tauto

/-- The pairwise change is either zero or two, with no negative case. -/
theorem rootChange_pair (x : W) (a b : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    rootChange x (rootRef a*x) b + rootChange x (rootRef a*x) (partner a b) =
      if goodPairRoot x a b then 2 else 0 := by
  by_cases hn : flipped a b
  · have hn' := (flipped_partner_iff a b).mpr hn
    have hi := rootInverted_mul_of_nonpos x a b hn
    have hi' := rootInverted_mul_of_nonpos x a (partner a b) hn'
    have hpair : positiveAction (rootRef a) (partner a b) = b := partner_involutive a b
    rw [hpair] at hi'
    have hnnb := negative_pair_not_both x a b hx hn
    simp only [rootChange,Finsupp.sub_apply,inversionVector_apply,hi,hi',goodPairRoot,]
    by_cases hb : rootInverted x b <;> by_cases hc : rootInverted x (partner a b) <;>
      simp_all
  · have hp := (b.property.1.act (rootRef a)).sign.resolve_right hn
    have hn' := mt (flipped_partner_iff a b).mp hn
    have hp' := ((partner a b).property.1.act (rootRef a)).sign.resolve_right hn'
    have hi := rootInverted_mul_of_nonneg x a b hp
    have hi' := rootInverted_mul_of_nonneg x a (partner a b) hp'
    have hpair : positiveAction (rootRef a) (partner a b) = b := partner_involutive a b
    rw [hpair] at hi'
    simp only [rootChange,Finsupp.sub_apply,inversionVector_apply,hi,hi',goodPairRoot,hn,false_and,ite_false]
    ring

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
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_3 (p : Prop) : Decidable p := Classical.propDecidable p

theorem positiveRoots_independent (a b : PositiveRoot M cs) (hab : a ≠ b) :
    LinearIndependent ℝ ![a.val,b.val] := by
  apply (rootReflection_represents M cs a).independent_of_ne (rootReflection_represents M cs b)
  intro h
  apply hab
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext h

theorem rootPlane_finrank (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Module.finrank ℝ (rootPlane a b) = 2 := by
  have h := finrank_span_eq_card (positiveRoots_independent a b hab)
  have hrange : Set.range ![a.val,b.val] = {a.val,b.val} := by
    ext z
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  rw [hrange] at h
  exact h

theorem rootPlane_self_finrank (a : PositiveRoot M cs) :
    Module.finrank ℝ (rootPlane a a) = 1 := by
  have hset : ({a.val,a.val} : Set (I → ℝ)) = {a.val} := by ext z; simp
  rw [rootPlane,hset]
  exact finrank_span_singleton (K := ℝ) (a.property.1.ne_zero)

theorem rootPlane_eq_iff (a b c : PositiveRoot M cs) (hab : a ≠ b) :
    rootPlane a c = rootPlane a b ↔ c ≠ a ∧ c.val ∈ rootPlane a b := by
  constructor
  · intro h
    constructor
    · intro hc
      subst c
      have h' := congrArg (fun P : Submodule ℝ (I → ℝ) => Module.finrank ℝ P) h
      rw [rootPlane_self_finrank,rootPlane_finrank a b hab] at h'
      norm_num at h'
    · rw [← h]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro ⟨hc,hcP⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro z hz
      rcases (Set.mem_insert_iff.mp hz) with rfl|hz
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · have hzc := Set.mem_singleton_iff.mp hz
        subst z
        exact hcP
    · rw [rootPlane_finrank a c (Ne.symm hc),rootPlane_finrank a b hab]

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
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_2 (p : Prop) : Decidable p := Classical.propDecidable p

def geometricFunctional : Module.Dual ℝ (I → ℝ) := (exists_geometric_functional M cs).choose

def geometricSlope (a : PositiveRoot M cs) : ℝ := geometricFunctional (M := M) (cs := cs) a.val / height a.val

theorem geometricSlope_injective : Function.Injective (geometricSlope (M := M) (cs := cs)) :=
  (exists_geometric_functional M cs).choose_spec

@[instance_reducible]
def geometricOrder : LinearOrder (PositiveRoot M cs) := LinearOrder.lift' geometricSlope geometricSlope_injective

theorem geometricSlope_between (a b c : PositiveRoot M cs) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hc : c.val = r • a.val+s • b.val)
    (hab : geometricSlope a < geometricSlope b) :
    geometricSlope a < geometricSlope c ∧ geometricSlope c < geometricSlope b :=
  functionalRatio_between M cs (geometricFunctional (M := M) (cs := cs)) a b c hr hs hc hab

def partnerEquiv (a : PositiveRoot M cs) : Equiv.Perm (PositiveRoot M cs) :=
  Function.Involutive.toPerm (partner a) (partner_involutive a)

@[simp] theorem partnerEquiv_apply (a b : PositiveRoot M cs) : partnerEquiv a b = partner a b := rfl
@[simp] theorem partnerEquiv_symm_apply (a b : PositiveRoot M cs) : (partnerEquiv a).symm b = partner a b := rfl

def extraRoot (x : W) (a b : PositiveRoot M cs) : Prop := b ≠ a ∧ goodPairRoot x a b

theorem extraRoot_partner (x : W) (a b : PositiveRoot M cs) :
    extraRoot x a (partner a b) ↔ extraRoot x a b := by
  simp only [extraRoot,ne_eq,partner_eq_self_of_eq,goodPairRoot_partner]

theorem extraRoot_finite (x : W) (a : PositiveRoot M cs) : {b | extraRoot x a b}.Finite := by
  apply (finite_rootInverted (M := M) (cs := cs) (rootRef a*x)).subset
  intro b hb
  exact (rootInverted_mul_of_nonpos x a b hb.2.1).mpr hb.2.2.2

def halfRoot (x : W) (a b : PositiveRoot M cs) : Prop :=
  extraRoot x a b ∧ geometricSlope b < geometricSlope (partner a b)

theorem halfRoot_finite (x : W) (a : PositiveRoot M cs) : {b | halfRoot x a b}.Finite :=
  (extraRoot_finite x a).subset (fun _ h => h.1)

def rootIndicator (p : PositiveRoot M cs → Prop) (hp : {a | p a}.Finite) : PositiveRoot M cs →₀ ℤ :=
  Finsupp.ofSupportFinite (fun a => if p a then 1 else 0) (by
    simpa only [Function.support,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hp)

@[simp] theorem rootIndicator_apply (p : PositiveRoot M cs → Prop) (hp : {a | p a}.Finite)
    (a : PositiveRoot M cs) : rootIndicator p hp a = if p a then 1 else 0 := rfl

def extraVector (x : W) (a : PositiveRoot M cs) := rootIndicator (extraRoot x a) (extraRoot_finite x a)
def halfVector (x : W) (a : PositiveRoot M cs) := rootIndicator (halfRoot x a) (halfRoot_finite x a)

/-- A choice of one root in each actual two-element negative pair. -/
theorem extraVector_eq_half (x : W) (a : PositiveRoot M cs) :
    extraVector x a = halfVector x a + Finsupp.mapDomain (partnerEquiv a) (halfVector x a) := by
  ext b
  simp only [Finsupp.add_apply,Finsupp.mapDomain_equiv_apply,partnerEquiv_symm_apply,
    extraVector,halfVector,rootIndicator_apply,halfRoot,extraRoot_partner,partner_involutive a b]
  by_cases hb : extraRoot x a b
  · have hne : geometricSlope b ≠ geometricSlope (partner a b) := by
      intro h
      exact hb.1 (negative_partner_fixed a b hb.2.1 (geometricSlope_injective h).symm)
    rcases lt_or_gt_of_ne hne with h|h
    · simp [hb,h,not_lt_of_gt h]
    · simp [hb,h,not_lt_of_gt h]
  · simp [hb]

/-- All apparent negative contributions cancel under the actual reflection on
root lines; the remaining pairs are precisely `extraVector`. -/
theorem erasedChange_pair (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    (rootChange x (rootRef a*x)).erase a +
      Finsupp.mapDomain (partnerEquiv a) ((rootChange x (rootRef a*x)).erase a) =
        extraVector x a + extraVector x a := by
  classical
  ext b
  simp only [Finsupp.add_apply,Finsupp.mapDomain_equiv_apply,partnerEquiv_symm_apply]
  by_cases hb : b=a
  · subst b
    simp [partner_self,extraVector,extraRoot]
  · have hpb : partner a b ≠ a := mt (partner_eq_self_of_eq a b).mp hb
    rw [Finsupp.erase_ne hb,Finsupp.erase_ne hpb,rootChange_pair x a b hx]
    simp only [extraVector,rootIndicator_apply,extraRoot,]
    by_cases hg : goodPairRoot x a b <;> simp [hg,hb]

theorem mapDomain_plane_partner (a : PositiveRoot M cs) (f : PositiveRoot M cs →₀ ℤ) :
    Finsupp.mapDomain (rootPlane a) (Finsupp.mapDomain (partnerEquiv a) f) =
      Finsupp.mapDomain (rootPlane a) f := by
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro b _
  exact rootPlane_partner a b

def planeWeight (x : W) (a : PositiveRoot M cs) : Submodule ℝ (I → ℝ) →₀ ℤ :=
  Finsupp.mapDomain (rootPlane a) (halfVector x a)


theorem planeDefect_eq_double_weight (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    planeDefect x (rootRef a*x) a = planeWeight x a + planeWeight x a := by
  have h := congrArg (Finsupp.mapDomain (rootPlane a)) (erasedChange_pair x a hx)
  rw [Finsupp.mapDomain_add,mapDomain_plane_partner,Finsupp.mapDomain_add] at h
  have heq : planeDefect x (rootRef a*x) a = Finsupp.mapDomain (rootPlane a) (extraVector x a) := by
    ext P
    have hh := congrArg (fun f : Submodule ℝ (I → ℝ) →₀ ℤ => f P) h
    simp only [Finsupp.add_apply] at hh
    change planeDefect x (rootRef a*x) a P = _
    dsimp [planeDefect]
    omega
  rw [heq,extraVector_eq_half,Finsupp.mapDomain_add,mapDomain_plane_partner]
  rfl

theorem planeWeight_nonneg (x : W) (a : PositiveRoot M cs) (P : Submodule ℝ (I → ℝ)) :
    0 ≤ planeWeight x a P := by
  classical
  rw [planeWeight,Finsupp.mapDomain,Finsupp.sum_apply]
  apply Finset.sum_nonneg
  intro b _
  simp only [Finsupp.single_apply,halfVector,rootIndicator_apply]
  split_ifs <;> norm_num

/-- Exact ambient degree formula, with actual roots, finite support and
nonnegative integral planar weights; no labeled interval isomorphism enters. -/
theorem sum_planeWeight (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    2 * (planeWeight x a).sum (fun _ n => n) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  have h := planeDefect_sum x a hx
  rw [planeDefect_eq_double_weight x a hx,
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at h
  linarith

end
end KLInvariance.TitsSpace
end

end OAI
