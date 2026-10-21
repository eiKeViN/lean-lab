import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.Reflection.Plane. Source spans: ReflectionPlane:1, ReflectionSchedules:15.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionPlane
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Independent linear forms give a surjection to the coordinate plane. -/
theorem formPair_surjective (f g : Module.Dual k V)
    (hfg : LinearIndependent k ![f, g]) : Function.Surjective (f.prod g) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro l hl
  change l = 0
  have hl' (v : V) : l (f v, g v) = 0 := LinearMap.congr_fun hl v
  have heval (c d : k) : l (c, d) = c * l (1, 0) + d * l (0, 1) := by
    have heq : (c, d) = c • ((1, 0) : k × k) + d • ((0, 1) : k × k) := by
      ext <;> simp
    rw [heq, map_add, map_smul, map_smul]
    rfl
  have hrel : l (1, 0) • f + l (0, 1) • g = 0 := by
    ext v
    change l (1, 0) * f v + l (0, 1) * g v = 0
    have hv := hl' v
    rw [heval] at hv
    simpa only [mul_comm] using hv
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.mp hfg _ _ hrel
  apply LinearMap.ext
  intro x
  obtain ⟨c, d⟩ := x
  change l (c, d) = 0
  rw [heval, h₁, h₂, mul_zero, mul_zero, add_zero]

/-- The range of the difference of a two-reflection product from the
identity is exactly the span of the two roots. -/
theorem range_preReflection_product_sub_id (α β : V) (f g : Module.Dual k V)
    (hfg : LinearIndependent k ![f, g]) :
    LinearMap.range ((Module.preReflection α f).comp (Module.preReflection β g) -
      LinearMap.id) = Submodule.span k {α, β} := by
  have hformula (v : V) :
      ((Module.preReflection α f).comp (Module.preReflection β g) -
        (LinearMap.id : V →ₗ[k] V)) v = (-f v + f β * g v) • α + (-g v) • β := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.preReflection_apply,
      LinearMap.id_apply, map_sub, map_smul]
    module
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    rw [hformula]
    exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
  · intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    obtain ⟨v, hv⟩ := formPair_surjective f g hfg (-a - f β * b, -b)
    have hf : f v = -a - f β * b := congrArg Prod.fst hv
    have hg : g v = -b := congrArg Prod.snd hv
    refine ⟨v, ?_⟩
    rw [hformula, hf, hg]
    module


theorem range_reflection_product_sub_id
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (α β : V) (hα : B α α = 2) (hβ : B β β = 2)
    (hαβ : LinearIndependent k ![α, β]) :
    LinearMap.range (((Module.reflection hα).toLinearMap).comp
      (Module.reflection hβ).toLinearMap - LinearMap.id) = Submodule.span k {α, β} := by
  apply range_preReflection_product_sub_id
  have h := hαβ.map' B hB.ker_eq_bot
  have heq : (⇑B ∘ ![α, β]) = ![B α, B β] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at h
  exact h

/-- Equal products of two normalized reflections recover equal root
planes, the exact local geometric input to `dih:transport`. -/
theorem plane_eq_of_reflection_product_eq
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (α β γ δ : V)
    (hα : B α α = 2) (hβ : B β β = 2) (hγ : B γ γ = 2) (hδ : B δ δ = 2)
    (hαβ : LinearIndependent k ![α, β]) (hγδ : LinearIndependent k ![γ, δ])
    (heq : (Module.reflection hα).toLinearMap.comp (Module.reflection hβ).toLinearMap =
      (Module.reflection hγ).toLinearMap.comp (Module.reflection hδ).toLinearMap) :
    Submodule.span k {α, β} = Submodule.span k {γ, δ} := by
  rw [← range_reflection_product_sub_id B hB α β hα hβ hαβ,
    ← range_reflection_product_sub_id B hB γ δ hγ hδ hγδ, heq]

end KLInvariance.ReflectionPlane
end


section
namespace KLInvariance.ReflectionPlane
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The product of three normalized reflections in a root plane is again
an actual orthogonal reflection. The plane itself need not be nondegenerate. -/
theorem reflection_triple_in_plane
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (a b c : V) (ha : B a a = 2) (hb : B b b = 2) (hc : B c c = 2)
    (hplane : c ∈ Submodule.span ℝ {a,b}) :
    ∃ d : V, ∃ hd : B d d = 2,
      Module.reflection ha * Module.reflection hb * Module.reflection hc =
        Module.reflection hd := by
  obtain ⟨x,y,hxy⟩ := Submodule.mem_span_pair.mp hplane
  subst c
  let p := B a b
  let r := p*x+y
  let d := x • b - r • a
  have hba : B b a = p := hB.eq b a
  have hnorm : x^2+p*x*y+y^2=1 := by
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      smul_eq_mul,ha,hb,hba] at hc
    dsimp [p]
    nlinarith [hc]
  have hd : B d d = 2 := by
    dsimp [d,r]
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,
      smul_eq_mul,ha,hb,hba]
    change x*(x*2-(p*x+y)*p)-(p*x+y)*(x*p-(p*x+y)*2)=2
    nlinarith [hnorm]
  refine ⟨d,hd,?_⟩
  apply LinearEquiv.ext
  intro v
  let A := B a v
  let C := B b v
  have h₁ : -A+p*C+(x-p*r)*(x*A+y*C)= r*(x*C-r*A) := by
    dsimp [r]
    linear_combination (A-p*C)*hnorm
  have h₂ : -C+r*(x*A+y*C)= -x*(x*C-r*A) := by
    dsimp [r]
    linear_combination C*hnorm
  calc
    (Module.reflection ha * Module.reflection hb * Module.reflection hc) v =
        v + (-A+p*C+(x-p*r)*(x*A+y*C)) • a +
          (-C+r*(x*A+y*C)) • b := by
      simp only [LinearEquiv.mul_apply,Module.reflection_apply,map_sub,map_smul,
        map_add,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,ha,hb,hba]
      dsimp [A,C,r,p]
      module
    _ = v + (r*(x*C-r*A)) • a + (-x*(x*C-r*A)) • b := by rw [h₁,h₂]
    _ = Module.reflection hd v := by
      simp only [Module.reflection_apply]
      dsimp [d]
      simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
      dsimp [A,C]
      module

end KLInvariance.ReflectionPlane
end

end OAI
