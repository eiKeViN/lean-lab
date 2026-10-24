module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Roots.Basic
public import ForMathlib.GroupTheory.Coxeter.Roots.Order
public import ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis
public import ForMathlib.LinearAlgebra.Avoidance

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder. Source spans: ReflectionOrders:2, ReflectionOrders:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_9 (p : Prop) : Decidable p := Classical.propDecidable p

@[simp] theorem normalizedRoot_height (a : PositiveRoot M cs) :
    height (normalizedRoot a) = 1 := by
  simp [normalizedRoot,a.height_pos.ne']

@[simp] theorem dual_normalizedRoot (f : Module.Dual ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    f (normalizedRoot a) = f a.val / height a.val := by
  simp [normalizedRoot,div_eq_mul_inv,mul_comm]

@[simp] theorem geometricFunctional_normalizedRoot (a : PositiveRoot M cs) :
    geometricFunctional (M := M) (cs := cs) (normalizedRoot a) = geometricSlope a :=
  dual_normalizedRoot _ a

theorem normalizedRoot_mem_iff (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    normalizedRoot a ∈ P ↔ a.val ∈ P := by
  constructor
  · intro h
    have hh := P.smul_mem (height a.val) h
    simpa [normalizedRoot,smul_smul,a.height_pos.ne'] using hh
  · exact fun h => P.smul_mem _ h

theorem rootPlane_eq_normalized_span (a b : PositiveRoot M cs) :
    rootPlane a b = Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mp (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mp (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mpr (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mpr (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The intersection of a root-plane with the height-one hyperplane is the
actual affine line through the two normalized roots. -/
theorem normalizedRoot_affine {a b c : PositiveRoot M cs}
    (hc : c.val ∈ rootPlane a b) :
    ∃ t : ℝ, normalizedRoot c = t • normalizedRoot a + (1-t) • normalizedRoot b := by
  have hcn : normalizedRoot c ∈ Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
    rw [← rootPlane_eq_normalized_span]
    exact (normalizedRoot_mem_iff _ _).mpr hc
  obtain ⟨t,s,he⟩ := Submodule.mem_span_pair.mp hcn
  have hh := congrArg (height (I := I)) he
  simp only [map_add,map_smul,normalizedRoot_height,smul_eq_mul,mul_one] at hh
  refine ⟨t,?_⟩
  have hs : s=1-t := by linarith
  exact hs ▸ he.symm

/-- On each genuine root plane, every height-normalized linear functional
is an affine function of the fixed angular slope. -/
theorem exists_affine_rootPlane (f : Module.Dual ℝ (I → ℝ))
    (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  let A := geometricSlope a
  let B := geometricSlope b
  let fa := f (normalizedRoot a)
  let fb := f (normalizedRoot b)
  have hAB : A-B ≠ 0 := sub_ne_zero.mpr (fun h => hab (geometricSlope_injective h))
  let c := (fa-fb)/(A-B)
  let d := fb-c*B
  have ha : fa=c*A+d := by
    dsimp [d,c]
    field_simp
    ring
  have hb : fb=c*B+d := by dsimp [d]; ring
  refine ⟨c,d,fun r hr => ?_⟩
  obtain ⟨t,ht⟩ := normalizedRoot_affine hr
  have hf : f (normalizedRoot r) = t*fa+(1-t)*fb := by
    rw [ht]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hg : geometricSlope r = t*A+(1-t)*B := by
    rw [← geometricFunctional_normalizedRoot,ht]
    simp only [map_add,map_smul,geometricFunctional_normalizedRoot,smul_eq_mul]
    rfl
  rw [hf,hg,ha,hb]
  ring

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
theorem exists_affine (f : Module.Dual ℝ (I → ℝ)) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ P →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  simpa only [B.plane_eq] using exists_affine_rootPlane f B.left B.right B.distinct

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
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_11 (p : Prop) : Decidable p := Classical.propDecidable p

@[expose] def pencil (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) : Module.Dual ℝ (I → ℝ) :=
  (1-t) • f + t • g

omit [Fintype I] in
@[simp] theorem pencil_zero (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 0=f := by
  simp [pencil]
omit [Fintype I] in
@[simp] theorem pencil_one (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 1=g := by
  simp [pencil]

omit [Fintype I] in
theorem pencil_apply (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) (v : I → ℝ) :
    pencil f g t v=(1-t)*f v+t*g v := rfl

@[expose] def rootDifference (a b : PositiveRoot M cs) : I → ℝ := normalizedRoot b-normalizedRoot a

@[expose] def wallVector (f : Module.Dual ℝ (I → ℝ)) (a b c : PositiveRoot M cs) : I → ℝ :=
  f (rootDifference a b) • rootDifference a c -
    f (rootDifference a c) • rootDifference a b

/-- This is an actual genericity condition on linear functionals, not
an assumed path or Hecke identity. -/
@[expose] def Transverse (f g : Module.Dual ℝ (I → ℝ)) : Prop :=
  ∀ a b c : PositiveRoot M cs, g (wallVector f a b c)=0 → wallVector f a b c=0

theorem pencil_tie_plane (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (t : ℝ)
    (a b : PositiveRoot M cs) (hab : a ≠ b)
    (he : pencil f g t (normalizedRoot a)=pencil f g t (normalizedRoot b)) :
    ∀ c : PositiveRoot M cs,
      pencil f g t (normalizedRoot c)=pencil f g t (normalizedRoot a) ↔
        c.val ∈ rootPlane a b := by
  let v := rootDifference a b
  have hv : f v ≠ 0 := by
    change f (normalizedRoot b-normalizedRoot a) ≠ 0
    rw [map_sub,sub_ne_zero]
    exact fun h => hab (hf h).symm
  have hvt : (1-t)*f v+t*g v=0 := by
    rw [← pencil_apply]
    change pencil f g t (normalizedRoot b-normalizedRoot a)=0
    rw [map_sub,he,sub_self]
  have ht : t ≠ 0 := by
    intro h
    subst t
    simp only [sub_zero,one_mul,zero_mul,add_zero] at hvt
    exact hv hvt
  intro c
  constructor
  · intro hc
    let w := rootDifference a c
    have hwt : (1-t)*f w+t*g w=0 := by
      rw [← pencil_apply]
      change pencil f g t (normalizedRoot c-normalizedRoot a)=0
      rw [map_sub,hc,sub_self]
    have hz : g (wallVector f a b c)=0 := by
      change g (f v • w-f w • v)=0
      rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      apply (mul_eq_zero.mp (show t * (f v*g w-f w*g v)=0 by
        calc
          _ = f v*((1-t)*f w+t*g w)-f w*((1-t)*f v+t*g v) := by ring
          _ = 0 := by rw [hwt,hvt]; ring)).resolve_left ht
    have heq : f v • w=f w • v := sub_eq_zero.mp (hg a b c hz)
    let P := rootPlane a b
    have haP : normalizedRoot a ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert _ _))
    have hbP : normalizedRoot b ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hvP : v ∈ P := P.sub_mem hbP haP
    have hwP : w ∈ P := by
      have hh := P.smul_mem (f v)⁻¹ (heq ▸ P.smul_mem (f w) hvP)
      simpa only [smul_smul,inv_mul_cancel₀ hv,one_smul] using hh
    apply (normalizedRoot_mem_iff P c).mp
    have hh := P.add_mem hwP haP
    simpa only [w,rootDifference,sub_add_cancel] using hh
  · intro hc
    obtain ⟨s,hs⟩ := normalizedRoot_affine hc
    rw [hs,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,← he]
    ring

/-- One intermediate functional is simultaneously transverse to any two
specified generic endpoints, even with infinitely many positive roots. -/
theorem exists_common_transverse (f h : Module.Dual ℝ (I → ℝ)) :
    ∃ g : Module.Dual ℝ (I → ℝ),
      Function.Injective (fun a : PositiveRoot M cs => g (normalizedRoot a)) ∧
      Transverse (M := M) (cs := cs) f g ∧ Transverse (M := M) (cs := cs) h g := by
  let := countable_Positiveroot M cs
  let E := PositiveRoot M cs
  let A := (E × E) ⊕ (Bool × E × E × E)
  let v : A → (I → ℝ) := fun x => match x with
    | .inl (a,b) => rootDifference a b
    | .inr (i,a,b,c) => wallVector (if i then f else h) a b c
  obtain ⟨g,hg⟩ := ReflectionSchedules.exists_avoiding_functional v
  refine ⟨g,?_,?_,?_⟩
  · intro a b he
    by_contra hab
    have hn : rootDifference a b ≠ 0 := by
      exact fun hz => hab (normalizedRoot_injective (sub_eq_zero.mp hz)).symm
    apply hg (.inl (a,b)) hn
    simp only [v,rootDifference,map_sub,he,sub_self]
  · intro a b c he
    by_contra hz
    exact hg (.inr (true,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)
  · intro a b c he
    by_contra hz
    exact hg (.inr (false,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)

end
end KLInvariance.TitsSpace
end

end OAI
