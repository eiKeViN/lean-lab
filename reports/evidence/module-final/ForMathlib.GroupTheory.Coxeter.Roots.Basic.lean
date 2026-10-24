import Lean
import Mathlib
import ForMathlib.GroupTheory.Coxeter.Realization.Faithful
import ForMathlib.LinearAlgebra.Reflection.Plane

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.Basic. Source spans: Tits:18, Tits:19, Tits:20.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- A genuine real root, obtained from a simple root by the Tits action. -/
def IsRoot (a : I → ℝ) : Prop := ∃ w : W, ∃ i : I, a = action M cs w (root i)

/-- A normalized real root representing a genuine Coxeter reflection. -/
def Represents (t : W) (a : I → ℝ) : Prop :=
  ∃ w : W, ∃ i : I, t = w * cs.simple i * w⁻¹ ∧ a = action M cs w (root i)

abbrev embed (a : I → ℝ) : Extended M := (a, 0)

@[simp] theorem form_root_self (i : I) : form M (root i) (root i) = 2 := by
  simp []

variable {M cs}

theorem IsRoot.norm {a : I → ℝ} (ha : IsRoot M cs a) : form M a a = 2 := by
  obtain ⟨w,i,rfl⟩ := ha
  rw [action_preserves, form_root_self]

theorem IsRoot.ne_zero {a : I → ℝ} (ha : IsRoot M cs a) : a ≠ 0 := by
  intro he
  have hn := ha.norm
  simp [he] at hn

theorem IsRoot.sign {a : I → ℝ} (ha : IsRoot M cs a) :
    (∀ i, 0 ≤ a i) ∨ (∀ i, a i ≤ 0) := by
  obtain ⟨w,i,rfl⟩ := ha
  rcases lt_or_gt_of_ne (cs.length_mul_simple_ne w i) with h|h
  · exact Or.inr (action_root_nonpos_of_descent M cs w i h)
  · exact Or.inl (action_root_nonneg_of_ascent M cs w i (by
      rcases cs.length_mul_simple w i with h'|h' <;> omega))

theorem IsRoot.neg {a : I → ℝ} (ha : IsRoot M cs a) : IsRoot M cs (-a) := by
  obtain ⟨w,i,rfl⟩ := ha
  refine ⟨w * cs.simple i, i, ?_⟩
  simp only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg]

theorem IsRoot.act {a : I → ℝ} (ha : IsRoot M cs a) (w : W) :
    IsRoot M cs (action M cs w a) := by
  obtain ⟨z,i,rfl⟩ := ha
  exact ⟨w*z, i, by simp only [map_mul, LinearEquiv.mul_apply]⟩

theorem Represents.isRoot {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    IsRoot M cs a := by
  obtain ⟨w,i,_,h⟩ := ha
  exact ⟨w,i,h⟩

theorem Represents.isReflection {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    cs.IsReflection t := by
  obtain ⟨w,i,h,_⟩ := ha
  exact ⟨w,i,h⟩

theorem Represents.neg {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    Represents M cs t (-a) := by
  obtain ⟨w,i,rfl,rfl⟩ := ha
  refine ⟨w * cs.simple i, i, ?_, ?_⟩
  · simp [mul_assoc]
  · simp only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg]

theorem Represents.act {t : W} {a : I → ℝ} (ha : Represents M cs t a) (w : W) :
    Represents M cs (w*t*w⁻¹) (action M cs w a) := by
  obtain ⟨z,i,rfl,rfl⟩ := ha
  refine ⟨w*z,i,?_,?_⟩
  · group
  · simp only [map_mul, LinearEquiv.mul_apply]

/-- The actual reflection formula for every conjugate root in the minimal
nondegenerate extension, not merely for simple roots. -/
theorem Represents.formula {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (v : Extended M) :
    extendedAction M cs t v = v - extendedForm M (embed M a) v • embed M a := by
  obtain ⟨w,i,rfl,rfl⟩ := ha
  have hv : extendedAction M cs w (extendedAction M cs w⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hp := extendedAction_preserves M cs w (extendedRoot M i)
    (extendedAction M cs w⁻¹ v)
  rw [hv] at hp
  rw [map_mul, map_mul]
  simp only [LinearEquiv.mul_apply, extendedAction_simple, map_sub, map_smul]
  rw [hv, ← hp, extendedRoot, extendedAction_restrict]

theorem Represents.action_formula {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (v : I → ℝ) : action M cs t v = v - form M a v • a := by
  have h := congrArg Prod.fst (ha.formula (embed M v))
  simpa only [extendedAction_restrict, embed, (extendedForm_spec M).2.2,
    Prod.fst_sub, Prod.smul_fst] using h

theorem Represents.unique_up_to_sign {t : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs t b) : a = b ∨ a = -b := by
  have hn := ha.isRoot.norm
  have hm := hb.isRoot.norm
  have hf := ha.action_formula a
  rw [hb.action_formula a, hn] at hf
  have hmul : form M b a • b = (2 : ℝ) • a := by
    have h := congrArg (fun z => a-z) hf
    simpa only [sub_sub_cancel] using h
  have hab : a = (form M b a / 2) • b := by
    calc
      a = (1/2 : ℝ) • ((2 : ℝ) • a) := by module
      _ = (1/2 : ℝ) • (form M b a • b) := by rw [hmul]
      _ = _ := by module
  have hc : (form M b a / 2) ^ 2 = 1 := by
    rw [hab] at hn
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hm] at hn
    nlinarith
  rcases sq_eq_one_iff.mp hc with h|h
  · exact Or.inl (by simpa [h] using hab)
  · exact Or.inr (by simpa [h] using hab)

theorem Represents.reflection_unique {t s : W} {a : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s a) : t = s := by
  apply extendedAction_injective M cs
  apply LinearEquiv.ext
  intro v
  rw [ha.formula, hb.formula]

theorem Represents.unique_positive {t : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs t b)
    (hpa : ∀ i, 0 ≤ a i) (hpb : ∀ i, 0 ≤ b i) : a = b := by
  rcases ha.unique_up_to_sign hb with h|h
  · exact h
  · exfalso
    apply ha.isRoot.ne_zero
    ext i
    have hi := congrFun h i
    simp only [Pi.neg_apply] at hi
    have := hpa i
    have := hpb i
    simp only [Pi.zero_apply]
    linarith

variable (M) (cs)

theorem exists_positive_root {t : W} (ht : cs.IsReflection t) :
    ∃ a : I → ℝ, Represents M cs t a ∧ ∀ i, 0 ≤ a i := by
  obtain ⟨w,i,rfl⟩ := ht
  have hr : Represents M cs (w * cs.simple i * w⁻¹) (action M cs w (root i)) :=
    ⟨w,i,rfl,rfl⟩
  rcases hr.isRoot.sign with h|h
  · exact ⟨_,hr,h⟩
  · exact ⟨_,hr.neg,fun i => by simpa only [Pi.neg_apply, neg_nonneg] using h i⟩

/-- Genuine positive roots, with their actual coordinate sign. -/
def PositiveRoot := {a : I → ℝ // IsRoot M cs a ∧ ∀ i, 0 ≤ a i}

def positiveRoot (t : {t : W // cs.IsReflection t}) : PositiveRoot M cs :=
  ⟨(exists_positive_root M cs t.property).choose,
    (exists_positive_root M cs t.property).choose_spec.1.isRoot,
    (exists_positive_root M cs t.property).choose_spec.2⟩

theorem positiveRoot_represents (t : {t : W // cs.IsReflection t}) :
    Represents M cs t.val (positiveRoot M cs t).val :=
  (exists_positive_root M cs t.property).choose_spec.1

def rootReflection (a : PositiveRoot M cs) : {t : W // cs.IsReflection t} := by
  let w := a.property.1.choose
  let i := a.property.1.choose_spec.choose
  exact ⟨w * cs.simple i * w⁻¹, w,i,rfl⟩

theorem rootReflection_represents (a : PositiveRoot M cs) :
    Represents M cs (rootReflection M cs a).val a.val := by
  refine ⟨a.property.1.choose, a.property.1.choose_spec.choose, rfl, ?_⟩
  exact a.property.1.choose_spec.choose_spec


def positiveRootEquiv : {t : W // cs.IsReflection t} ≃ PositiveRoot M cs where
  toFun := positiveRoot M cs
  invFun := rootReflection M cs
  left_inv t := Subtype.ext ((rootReflection_represents M cs _).reflection_unique
      (positiveRoot_represents M cs t))
  right_inv a := Subtype.ext ((positiveRoot_represents M cs _).unique_positive
      (rootReflection_represents M cs a) (positiveRoot M cs _).property.2 a.property.2)

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

theorem IsRoot.not_both {a : I → ℝ} (ha : IsRoot M cs a)
    (hp : ∀ i, 0 ≤ a i) (hn : ∀ i, a i ≤ 0) : False := by
  apply ha.ne_zero
  ext i
  exact le_antisymm (hn i) (hp i)

/-- A simple reflection can turn a positive real root negative only on its
own root. This uses actual Tits coordinates and normalization. -/
theorem IsRoot.eq_simple_of_nonpos {a : I → ℝ} (ha : IsRoot M cs a)
    (hp : ∀ k, 0 ≤ a k) (i : I)
    (hn : ∀ k, action M cs (cs.simple i) a k ≤ 0) : a = root i := by
  classical
  have ha0 (k : I) (hk : k ≠ i) : a k = 0 := by
    have h := hn k
    simp only [action_simple, Pi.sub_apply, Pi.smul_apply, root,
      Pi.single_apply, hk, ↓reduceIte, smul_eq_mul, mul_zero, sub_zero] at h
    exact le_antisymm h (hp k)
  have heq : a = a i • root i := by
    ext k
    by_cases hki : k = i
    · subst k; simp [root]
    · simp [root, hki, ha0 k hki]
  have hnorm := ha.norm
  rw [heq] at hnorm
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_root_self] at hnorm
  have hai : a i = 1 := by nlinarith [hp i]
  simpa only [hai, one_smul] using heq

theorem Represents.simple_sign {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (hp : ∀ k, 0 ≤ a k) (i : I) :
    ((∀ k, action M cs (cs.simple i) a k ≤ 0) ↔ t = cs.simple i) ∧
    ((∀ k, 0 ≤ action M cs (cs.simple i) a k) ↔ t ≠ cs.simple i) := by
  have hi : Represents M cs (cs.simple i) (root i) := ⟨1,i,by simp,by simp⟩
  have hneg : (∀ k, action M cs (cs.simple i) a k ≤ 0) ↔ t = cs.simple i := by
    constructor
    · intro h
      have heq := ha.isRoot.eq_simple_of_nonpos hp i h
      exact ha.reflection_unique (heq.symm ▸ hi)
    · intro h
      have heq := (h ▸ ha).unique_positive hi hp (root_nonneg i)
      simpa only [heq, action_simple_root, Pi.neg_apply, neg_nonpos] using root_nonneg i
  refine ⟨hneg, ?_⟩
  constructor
  · intro h heq
    exact (ha.isRoot.act (cs.simple i)).not_both h (hneg.mpr heq)
  · intro h
    rcases (ha.isRoot.act (cs.simple i)).sign with hp|hn
    · exact hp
    · exact False.elim (h (hneg.mp hn))

/-- The signed combinatorial reflection action is the actual root sign
under the faithful Tits representation. -/
def SignedRepresents (p : W × ZMod 2) (a : I → ℝ) : Prop :=
  Represents M cs p.1 a ∧
    ((p.2 = 0 ∧ ∀ i, 0 ≤ a i) ∨ (p.2 = 1 ∧ ∀ i, a i ≤ 0))

theorem SignedRepresents.simple {p : W × ZMod 2} {a : I → ℝ}
    (ha : SignedRepresents (M := M) (cs := cs) p a) (i : I) :
    SignedRepresents (M := M) (cs := cs) (CoxeterSupport.simpleAction cs i p)
      (action M cs (cs.simple i) a) := by
  rcases p with ⟨t,z⟩
  rw [CoxeterSupport.simpleAction_apply]
  refine ⟨?_,?_⟩
  · simpa only [cs.inv_simple] using ha.1.act (cs.simple i)
  · rcases ha.2 with ⟨rfl,hp⟩|⟨rfl,hn⟩
    · by_cases heq : t = cs.simple i
      · exact Or.inr ⟨by simp [heq], (ha.1.simple_sign hp i).1.mpr heq⟩
      · exact Or.inl ⟨by simp [heq, ZModModule.add_self], (ha.1.simple_sign hp i).2.mpr heq⟩
    · have hp : ∀ k, 0 ≤ (-a) k := fun k => neg_nonneg.mpr (hn k)
      by_cases heq : t = cs.simple i
      · refine Or.inl ⟨by simp [heq, ZModModule.add_self], ?_⟩
        have h := (ha.1.neg.simple_sign hp i).1.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonpos] using h
      · refine Or.inr ⟨by simp [heq], ?_⟩
        have h := (ha.1.neg.simple_sign hp i).2.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonneg] using h

theorem SignedRepresents.act {p : W × ZMod 2} {a : I → ℝ}
    (ha : SignedRepresents (M := M) (cs := cs) p a) (w : W) :
    SignedRepresents (M := M) (cs := cs) (CoxeterSupport.reflectionAction cs w p)
      (action M cs w a) := by
  obtain ⟨ω,rfl⟩ := cs.wordProd_surjective w
  induction ω with
  | nil => simpa using ha
  | cons i ω ih =>
    simpa only [cs.wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      CoxeterSupport.reflectionAction_simple, LinearEquiv.mul_apply] using ih.simple i


theorem Represents.inversion_iff {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (hp : ∀ i, 0 ≤ a i) (w : W) :
    (∀ i, action M cs w⁻¹ a i ≤ 0) ↔ cs.IsLeftInversion w t := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq]
  let c : ZMod 2 := (cs.leftInvSeq ω).count t
  have hc : c+c=0 := ZModModule.add_self c
  have hrec := CoxeterSupport.wordAction_record cs ω t c
  rw [← CoxeterSupport.reflectionAction_wordProd] at hrec
  have hrec' : CoxeterSupport.reflectionAction cs (cs.wordProd ω)
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω, c) = (t,0) := by
    change CoxeterSupport.reflectionAction cs (cs.wordProd ω)
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω,c) = (t,c+c) at hrec
    rwa [hc] at hrec
  have hinv : CoxeterSupport.reflectionAction cs (cs.wordProd ω)⁻¹ (t,0) =
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω,c) := by
    rw [map_inv, ← hrec']
    exact Equiv.symm_apply_apply _ _
  have hs : SignedRepresents (M := M) (cs := cs) (t,0) a := ⟨ha,Or.inl ⟨rfl,hp⟩⟩
  have hsi := hs.act (cs.wordProd ω)⁻¹
  rw [hinv] at hsi
  have hcount : c = if t ∈ cs.leftInvSeq ω then 1 else 0 := by
    dsimp [c]
    by_cases hm : t ∈ cs.leftInvSeq ω
    · rw [ite_eq_left hm, List.count_eq_one_of_mem hω.nodup_leftInvSeq hm]
      norm_num
    · rw [ite_eq_right hm, List.count_eq_zero.mpr hm]
      rfl
  have hmem : (∀ i, action M cs (cs.wordProd ω)⁻¹ a i ≤ 0) ↔ t ∈ cs.leftInvSeq ω := by
    by_cases hm : t ∈ cs.leftInvSeq ω
    · have hc1 : c=1 := by simpa [hm] using hcount
      simp only [hc1] at hsi
      rcases hsi.2 with ⟨hbad,_⟩|⟨_,hn⟩
      · norm_num at hbad
      · exact iff_of_true hn hm
    · have hc0 : c=0 := by simpa [hm] using hcount
      simp only [hc0] at hsi
      rcases hsi.2 with ⟨_,hpos⟩|⟨hbad,_⟩
      · exact iff_of_false (fun hn => (ha.isRoot.act _).not_both hpos hn) hm
      · norm_num at hbad
  rw [hmem]
  exact ⟨cs.isLeftInversion_of_mem_leftInvSeq hω,
    CoxeterSupport.mem_leftInvSeq_of_inversion cs hω⟩

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

theorem Represents.independent_of_ne {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hts : t ≠ s) :
    LinearIndependent ℝ ![a,b] := by
  apply (LinearIndependent.pair_iff' ha.isRoot.ne_zero).mpr
  intro c heq
  have hn := hb.isRoot.norm
  rw [← heq] at hn
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ha.isRoot.norm] at hn
  have hc : c^2 = 1 := by nlinarith
  rcases sq_eq_one_iff.mp hc with hc|hc
  · have hab : a=b := by simpa only [hc,one_smul] using heq
    exact hts (ha.reflection_unique (hab.symm ▸ hb))
  · have hab : -a=b := by simpa only [hc,neg_one_smul] using heq
    exact hts (ha.neg.reflection_unique (hab.symm ▸ hb))

theorem Represents.extended_independent_of_ne {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hts : t ≠ s) :
    LinearIndependent ℝ ![embed M a,embed M b] := by
  have h := (ha.independent_of_ne hb hts).map'
    (LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
    (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
  have heq : (⇑(LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M)))) ∘
      ![a,b]) = ![embed M a,embed M b] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

theorem Represents.extendedAction_eq {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    extendedAction M cs t = Module.reflection
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  apply LinearEquiv.ext
  intro v
  exact ha.formula v


theorem Represents.plane_eq_of_product_eq {t s r q : W} {a b c d : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b)
    (hc : Represents M cs r c) (hd : Represents M cs q d)
    (hts : t ≠ s) (hrq : r ≠ q) (heq : t*s=r*q) :
    Submodule.span ℝ {embed M a, embed M b} =
      Submodule.span ℝ {embed M c, embed M d} := by
  apply ReflectionPlane.plane_eq_of_reflection_product_eq (extendedForm M)
    (extendedForm_spec M).2.1 (embed M a) (embed M b) (embed M c) (embed M d)
    (by rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hb.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hc.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hd.isRoot.norm)
    (ha.extended_independent_of_ne hb hts) (hc.extended_independent_of_ne hd hrq)
  have h := congrArg (extendedAction M cs) heq
  rw [map_mul, map_mul, ha.extendedAction_eq, hb.extendedAction_eq,
    hc.extendedAction_eq, hd.extendedAction_eq] at h
  exact congrArg LinearEquiv.toLinearMap h

variable (M) (cs)
/-- The actual positive ambient roots inverted by `w`. -/
def RootInversions (w : W) :=
  {a : PositiveRoot M cs // ∀ i, action M cs w⁻¹ a.val i ≤ 0}

def rootInversionEquiv (w : W) : RootInversions M cs w ≃ {t : W // cs.IsLeftInversion w t} where
  toFun a := ⟨(rootReflection M cs a.val).val,
    ((rootReflection_represents M cs a.val).inversion_iff a.val.property.2 w).mp a.property⟩
  invFun t := ⟨positiveRoot M cs ⟨t.val,t.property.1⟩,
    ((positiveRoot_represents M cs ⟨t.val,t.property.1⟩).inversion_iff
      (positiveRoot M cs ⟨t.val,t.property.1⟩).property.2 w).mpr t.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (positiveRootEquiv M cs).apply_symm_apply a.val
  right_inv t := by
    apply Subtype.ext
    change (rootReflection M cs (positiveRoot M cs ⟨t.val,t.property.1⟩)).val = t.val
    exact congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
      ((positiveRootEquiv M cs).symm_apply_apply ⟨t.val,t.property.1⟩)

def leftInversionListEquiv {ω : List I} (hω : cs.IsReduced ω) :
    {t : W // cs.IsLeftInversion (cs.wordProd ω) t} ≃ {t : W // t ∈ cs.leftInvSeq ω} where
  toFun t := ⟨t.val,CoxeterSupport.mem_leftInvSeq_of_inversion cs hω t.property⟩
  invFun t := ⟨t.val,cs.isLeftInversion_of_mem_leftInvSeq hω t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full ambient inversion count, not a cardinality assumption. -/
theorem rootInversions_finite (w : W) : Finite (RootInversions M cs w) := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq]
  exact Finite.of_equiv (Fin (cs.leftInvSeq ω).length)
    ((List.Nodup.getEquiv (cs.leftInvSeq ω) hω.nodup_leftInvSeq).trans
      ((leftInversionListEquiv M cs hω).symm.trans (rootInversionEquiv M cs _).symm))

theorem card_rootInversions (w : W) : Nat.card (RootInversions M cs w) = cs.length w := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq, Nat.card_congr (rootInversionEquiv M cs _),
    Nat.card_congr (leftInversionListEquiv M cs hω),
    ← Nat.card_congr (List.Nodup.getEquiv (cs.leftInvSeq ω) hω.nodup_leftInvSeq),
    Nat.card_fin, cs.length_leftInvSeq, hω.eq]

end
end KLInvariance.TitsSpace
end

end OAI

open Lean
namespace BoundaryCodec
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => toJson (#[nameJson p, toJson s])
  | .num p n => toJson (#[nameJson p, toJson n, Json.null])
partial def levelJson : Level → Json
  | .zero => toJson (#[toJson "zero"])
  | .succ u => toJson (#[toJson "succ", levelJson u])
  | .max u v => toJson (#[toJson "max", levelJson u, levelJson v])
  | .imax u v => toJson (#[toJson "imax", levelJson u, levelJson v])
  | .param n => toJson (#[toJson "param", nameJson n])
  | .mvar _ => panic! "unclosed level"
structure Dump where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def encode (e : Expr) : StateM Dump Nat := do
  if let .mdata _ b := e then return ← encode b
  if let some i := (← get).ids[ExprStructEq.mk e]? then return i
  let node : Array Json ← match e with
    | .bvar n => pure #[toJson "bvar", toJson n]
    | .sort u => pure #[toJson "sort", levelJson u]
    | .const n us => pure #[toJson "const", nameJson n, toJson (us.map levelJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi | .forallE n t b bi => do
      let tag := if e.isLambda then "lam" else "forall"
      let bi := match bi with | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
      pure #[toJson tag, nameJson n, toJson (← encode t), toJson (← encode b), toJson bi]
    | .letE n t v b nondep => do pure #[toJson "let", nameJson n, toJson (← encode t), toJson (← encode v), toJson (← encode b), toJson nondep]
    | .lit (.natVal n) => pure #[toJson "nat", toJson n]
    | .lit (.strVal s) => pure #[toJson "str", toJson s]
    | .proj n i b => do pure #[toJson "proj", nameJson n, toJson i, toJson (← encode b)]
    | _ => panic! "unclosed expression"
  let s ← get
  set ({ids := s.ids.insert (ExprStructEq.mk e) s.nodes.size, nodes := s.nodes.push (toJson node)} : Dump)
  return s.nodes.size
partial def readName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size == 2 then return .str (← readName a[0]!) (← a[1]!.getStr?)
  if a.size == 3 then return .num (← readName a[0]!) (← fromJson? a[1]!)
  throw "bad name"
partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => do pure (.zero)
  | "succ" => do pure (.succ (← readLevel a[1]!))
  | "max" => do pure (.max (← readLevel a[1]!) (← readLevel a[2]!))
  | "imax" => do pure (.imax (← readLevel a[1]!) (← readLevel a[2]!))
  | "param" => do pure (.param (← readName a[1]!))
  | _ => throw "bad level"
def decode (nodes : Array Json) : Except String (Array Expr) := do
  let mut es := #[]
  for j in nodes do
    let a ← j.getArr?
    let child := fun (i : Nat) => (show Except String Expr from do
      let n : Nat ← fromJson? a[i]!
      if n < es.size then return es[n]! else throw "non-topological DAG")
    let e : Expr ← match ← a[0]!.getStr? with
      | "bvar" => do pure (.bvar (← fromJson? a[1]!))
      | "sort" => do pure (.sort (← readLevel a[1]!))
      | "const" => do pure (.const (← readName a[1]!) (← (← a[2]!.getArr?).toList.mapM readLevel))
      | "app" => do pure (.app (← child 1) (← child 2))
      | "lam" | "forall" => do
        let bi : Nat ← fromJson? a[4]!
        let bi ← match bi with | 0 => pure BinderInfo.default | 1 => pure .implicit | 2 => pure .strictImplicit | 3 => pure .instImplicit | _ => throw "bad binder"
        if (← a[0]!.getStr?) == "lam" then pure (.lam (← readName a[1]!) (← child 2) (← child 3) bi)
        else pure (.forallE (← readName a[1]!) (← child 2) (← child 3) bi)
      | "let" => do pure (.letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← fromJson? a[5]!))
      | "nat" => do pure (.lit (.natVal (← fromJson? a[1]!)))
      | "str" => do pure (.lit (.strVal (← fromJson? a[1]!)))
      | "proj" => do pure (.proj (← readName a[1]!) (← fromJson? a[2]!) (← child 3))
      | _ => throw "bad expression"
    es := es.push e
  return es
end BoundaryCodec

open Lean Meta Elab Command BoundaryCodec
run_elab do
  let names : Array Name := #[`OAI.KLInvariance.TitsSpace.Represents.extendedAction_eq]
  let env := (← Lean.getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending : Array Name := names
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.GroupTheory.Coxeter.Roots.Basic.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
