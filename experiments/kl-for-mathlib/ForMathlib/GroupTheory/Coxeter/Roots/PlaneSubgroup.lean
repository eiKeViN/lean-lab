import Mathlib
import ForMathlib.GroupTheory.Coxeter.Roots.Basic

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup. Source spans: Tits:21, Tits:22.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Elements whose actual linear displacement lies in `P`. This is a
subgroup even when the invariant bilinear form restricted to `P` is singular. -/
def movingSubgroup (P : Submodule ℝ (I → ℝ)) : Subgroup W where
  carrier := {w | ∀ v, action M cs w v - v ∈ P}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro w z hw hz v
    have h := P.add_mem (hw (action M cs z v)) (hz v)
    simpa only [map_mul, LinearEquiv.mul_apply, sub_add_sub_cancel] using h
  inv_mem' := by
    intro w hw v
    have h := P.neg_mem (hw (action M cs w⁻¹ v))
    have hv : action M cs w (action M cs w⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    simpa only [hv, neg_sub] using h

/-- The manuscript's maximal plane reflection subgroup, defined using
actual normalized roots, not by assuming a rank-two presentation. -/
def planeSubgroup (P : Submodule ℝ (I → ℝ)) : Subgroup W :=
  Subgroup.closure {t | ∃ a, Represents M cs t a ∧ a ∈ P}

theorem planeSubgroup_le_moving (P : Submodule ℝ (I → ℝ)) :
    planeSubgroup M cs P ≤ movingSubgroup M cs P := by
  apply (Subgroup.closure_le (movingSubgroup M cs P)).mpr
  rintro t ⟨a,ha,haP⟩ v
  rw [ha.action_formula]
  have heq : v - form M a v • a - v = (-form M a v) • a := by module
  rw [heq]
  exact P.smul_mem _ haP

theorem Represents.mem_of_moving {P : Submodule ℝ (I → ℝ)} {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (ht : t ∈ movingSubgroup M cs P) : a ∈ P := by
  have h := ht a
  change action M cs t a - a ∈ P at h
  rw [ha.action_formula,ha.isRoot.norm] at h
  have heq : a - (2 : ℝ) • a - a = (-2 : ℝ) • a := by module
  rw [heq] at h
  have h' := P.smul_mem (-1/2 : ℝ) h
  have heq' : (-1/2 : ℝ) • ((-2 : ℝ) • a) = a := by module
  rwa [heq'] at h'


theorem Represents.planeSubgroup_mem_iff {P : Submodule ℝ (I → ℝ)} {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) : t ∈ planeSubgroup M cs P ↔ a ∈ P := by
  constructor
  · intro ht
    exact Represents.mem_of_moving M cs ha (planeSubgroup_le_moving M cs P ht)
  · intro haP
    exact Subgroup.subset_closure ⟨a,ha,haP⟩

/-- Two ambient vertices in a left coset of this plane subgroup can have
no reflection edge except one whose actual root is in the plane. -/
theorem reflection_between_coset_mem {P : Submodule ℝ (I → ℝ)} {t g h a : W}
    (hg : g ∈ planeSubgroup M cs P) (hh : h ∈ planeSubgroup M cs P)
    (heq : h*a=t*(g*a)) {r : I → ℝ} (ht : Represents M cs t r) : r ∈ P := by
  have htg : t*g=h := by apply mul_right_cancel (b := a); simpa only [mul_assoc] using heq.symm
  have htG : t ∈ planeSubgroup M cs P := by
    have heq' : t=h*g⁻¹ := by rw [← htg]; group
    rw [heq']
    exact (planeSubgroup M cs P).mul_mem hh ((planeSubgroup M cs P).inv_mem hg)
  exact (Represents.planeSubgroup_mem_iff M cs ht).mp htG

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Least ambient length in each actual left plane-subgroup coset. No
uniqueness or rank-two Coxeter presentation is smuggled into this definition. -/
theorem planeCoset_exists_minimal (P : Submodule ℝ (I → ℝ)) (a : W) :
    ∃ a₀ g : W, g ∈ planeSubgroup M cs P ∧ a = g*a₀ ∧
      ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀) := by
  classical
  have hex : ∃ n : ℕ, ∃ a₀ g : W, g ∈ planeSubgroup M cs P ∧
      a = g*a₀ ∧ cs.length a₀ = n :=
    ⟨cs.length a,a,1,(planeSubgroup M cs P).one_mem,by simp,rfl⟩
  obtain ⟨a₀,g,hg,ha,hlen⟩ := Nat.find_spec hex
  refine ⟨a₀,g,hg,ha,fun z hz => ?_⟩
  rw [hlen]
  apply Nat.find_min' hex
  refine ⟨z*a₀,g*z⁻¹,(planeSubgroup M cs P).mul_mem hg
    ((planeSubgroup M cs P).inv_mem hz),?_,rfl⟩
  simpa [mul_assoc] using ha

variable {M cs}

theorem planeSubgroup_preserves {P : Submodule ℝ (I → ℝ)} {g : W}
    (hg : g ∈ planeSubgroup M cs P) {a : I → ℝ} (ha : a ∈ P) :
    action M cs g a ∈ P := by
  have h := (planeSubgroup_le_moving M cs P hg) a
  simpa only [sub_add_cancel] using P.add_mem h ha

/-- A least coset representative sends every positive plane root to a
positive ambient root under its inverse, by the proved inversion criterion. -/
theorem root_nonneg_of_coset_minimal {P : Submodule ℝ (I → ℝ)} {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a : I → ℝ} (ha : IsRoot M cs a) (hp : ∀ i, 0 ≤ a i) (haP : a ∈ P) :
    ∀ i, 0 ≤ action M cs a₀⁻¹ a i := by
  let r : PositiveRoot M cs := ⟨a,ha,hp⟩
  have hr := rootReflection_represents M cs r
  have htP := (Represents.planeSubgroup_mem_iff M cs hr).mpr haP
  rcases (ha.act a₀⁻¹).sign with hpos|hneg
  · exact hpos
  · have hi := (hr.inversion_iff hp a₀).mp hneg
    exact (not_lt_of_ge (hmin _ htP) hi.2).elim


theorem root_nonpos_coset_minimal_iff {P : Submodule ℝ (I → ℝ)} {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a : I → ℝ} (ha : IsRoot M cs a) (haP : a ∈ P) :
    (∀ i, action M cs a₀⁻¹ a i ≤ 0) ↔ ∀ i, a i ≤ 0 := by
  rcases ha.sign with hp|hn
  · have hnew := root_nonneg_of_coset_minimal hmin ha hp haP
    exact iff_of_false ((ha.act _).not_both hnew) (ha.not_both hp)
  · have hnp : ∀ i, 0 ≤ (-a) i := fun i => neg_nonneg.mpr (hn i)
    have hh := root_nonneg_of_coset_minimal hmin ha.neg hnp (P.neg_mem haP)
    have hnew : ∀ i, action M cs a₀⁻¹ a i ≤ 0 := by
      intro i
      simpa only [map_neg, Pi.neg_apply, neg_nonneg] using hh i
    exact iff_of_true hnew hn

theorem root_inversion_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) {a : I → ℝ} (ha : IsRoot M cs a)
    (haP : a ∈ P) :
    (∀ i, action M cs (g*a₀)⁻¹ a i ≤ 0) ↔
      ∀ i, action M cs g⁻¹ a i ≤ 0 := by
  rw [mul_inv_rev, map_mul]
  change (∀ i, action M cs a₀⁻¹ (action M cs g⁻¹ a) i ≤ 0) ↔ _
  exact root_nonpos_coset_minimal_iff hmin (ha.act _)
    (planeSubgroup_preserves ((planeSubgroup M cs P).inv_mem hg) haP)

theorem leftInversion_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g t : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) (ht : t ∈ planeSubgroup M cs P)
    (hr : cs.IsReflection t) :
    cs.IsLeftInversion (g*a₀) t ↔ cs.IsLeftInversion g t := by
  let a := positiveRoot M cs ⟨t,hr⟩
  have ha := positiveRoot_represents M cs ⟨t,hr⟩
  rw [← ha.inversion_iff a.property.2, ← ha.inversion_iff a.property.2]
  exact root_inversion_coset_iff hmin hg a.property.1
    ((Represents.planeSubgroup_mem_iff M cs ha).mp ht)

/-- The directed ambient reflection graph on any plane-subgroup coset is
exactly transported from that on the subgroup by a least coset representative.
Identifying this graph with a *dihedral Coxeter* graph still requires the
canonical rank-two reflection-subgroup theorem. -/
theorem bruhatStep_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g h : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) (hh : h ∈ planeSubgroup M cs P) :
    BruhatStep cs (g*a₀) (h*a₀) ↔ BruhatStep cs g h := by
  have hn : ∀ {t : W}, h=t*g → cs.IsReflection t →
      (cs.length (g*a₀) < cs.length (h*a₀) ↔ cs.length g < cs.length h) := by
    intro t heq ht
    have htP : t ∈ planeSubgroup M cs P := by
      have htgh : t=h*g⁻¹ := by rw [heq]; group
      rw [htgh]
      exact (planeSubgroup M cs P).mul_mem hh ((planeSubgroup M cs P).inv_mem hg)
    have hi := leftInversion_coset_iff hmin hh htP ht
    have hth : t*h=g := by rw [heq,← mul_assoc,ht.mul_self,one_mul]
    simpa only [CoxeterSystem.IsLeftInversion, ht, true_and, ← mul_assoc, hth] using hi
  constructor
  · rintro ⟨hlen,t,ht,heq⟩
    have htg : h=t*g := by apply mul_right_cancel (b := a₀); simpa only [mul_assoc] using heq
    exact ⟨(hn htg ht).mp hlen,t,ht,htg⟩
  · rintro ⟨hlen,t,ht,heq⟩
    exact ⟨(hn heq ht).mpr hlen,t,ht,by rw [heq,mul_assoc]⟩

end
end KLInvariance.TitsSpace
end

end OAI
