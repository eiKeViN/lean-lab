import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.Reflection.Classification. Source spans: IntegralPairings:22.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

 theorem orthogonal_eq_id_or_rootReflection
    (B : LinearMap.BilinForm ℝ V) (a : V) (ha : B a a=2)
    (g : V ≃ₗ[ℝ] V) (hg : ∀ v w, B (g v) (g w)=B v w)
    (hline : ∀ v, g v-v ∈ Submodule.span ℝ {a}) :
    g.toLinearMap=LinearMap.id ∨ ∀ v, g v=Module.preReflection a (B a) v := by
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp (hline a)
  have hga : g a=(1+r) • a := by rw [add_smul,one_smul,hr]; module
  have hn := hg a a
  rw [hga] at hn
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,ha] at hn
  have hr0 : r*(r+2)=0 := by nlinarith
  rcases mul_eq_zero.mp hr0 with hr | hr
  · left
    have hga' : g a=a := by simpa only [hr,add_zero,one_smul] using hga
    ext v
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline v)
    have hgv : g v=v+c • a := by rw [hc]; module
    have h := hg a v
    rw [hga',hgv] at h
    simp only [map_add,map_smul,ha,smul_eq_mul] at h
    have hc0 : c=0 := by linarith
    change g v=v
    simpa only [hc0,zero_smul,add_zero] using hgv
  · right
    have hr' : r= -2 := by linarith
    have hga' : g a= -a := by simpa only [hr',show (1:ℝ)+ -2= -1 by norm_num,neg_one_smul] using hga
    intro v
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline v)
    have hgv : g v=v+c • a := by rw [hc]; module
    have h := hg a v
    rw [hga',hgv] at h
    simp only [map_neg,LinearMap.neg_apply,map_add,map_smul,ha,smul_eq_mul] at h
    have hc' : c= -(B a v) := by linarith
    rw [hgv,hc',Module.preReflection_apply,neg_smul,sub_eq_add_neg]

end KLInvariance.Realization
end

end OAI
