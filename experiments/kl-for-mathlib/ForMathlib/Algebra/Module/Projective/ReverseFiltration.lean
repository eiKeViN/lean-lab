module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Tactic.Abel

public section

/-! Semantic home: ForMathlib.Algebra.Module.Projective.ReverseFiltration. Source spans: ModuleAlgebra:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReverseFiltration

variable {R F E I : Type*} [CommRing R]
  [AddCommGroup F] [Module R F] [AddCommGroup E] [Module R E]
  [AddCommGroup I] [Module R I]

/-- The kernel of a surjection from a projective module is projective if
the target has an actual length-one projective presentation. -/
theorem kernel_projective_of_presentation
    [Module.Projective R F] [Module.Projective R E]
    (f : F →ₗ[R] I) (g : E →ₗ[R] I)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Projective R (LinearMap.ker g)] :
    Module.Projective R (LinearMap.ker f) := by
  obtain ⟨a, ha⟩ := Module.projective_lifting_property g f hg
  obtain ⟨b, hb⟩ := Module.projective_lifting_property f g hf
  have ha' (x : F) : g (a x) = f x := LinearMap.congr_fun ha x
  have hb' (x : E) : f (b x) = g x := LinearMap.congr_fun hb x
  let a₀ : LinearMap.ker f →ₗ[R] LinearMap.ker g :=
    { toFun := fun x => ⟨a x, by simp [LinearMap.mem_ker, ha']⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun r x => Subtype.ext (by simp) }
  let i : LinearMap.ker f →ₗ[R] F × LinearMap.ker g :=
    (LinearMap.ker f).subtype.prod a₀
  let r : F × LinearMap.ker g →ₗ[R] LinearMap.ker f :=
    { toFun := fun x => ⟨x.1 - b (a x.1) + b x.2, by
        simp [LinearMap.mem_ker, hb', ha']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_add, smul_sub]) }
  apply Module.Projective.of_split i r
  ext x
  change (x : F) - b (a x) + b (a x) = x
  exact sub_add_cancel _ _

end KLInvariance.ReverseFiltration
end

end OAI
