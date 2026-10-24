module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Cover.Local. Source spans: ModuleAlgebra:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.LocalCover

variable {R B P N : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

/-- A lift through a minimal free cover is automatically surjective. This
is the exact Nakayama step of plane-localized BMP decomposition. -/
theorem lift_surjective [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N) (g : B →ₗ[R] P)
    (hφ : Function.Surjective φ) (hg : π.comp g = φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    Function.Surjective g := by
  apply LinearMap.surjective_of_surjective_comp_mkQ g (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro q
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨b, hb⟩ := hφ (π p)
  refine ⟨b, ?_⟩
  change Submodule.Quotient.mk (g b) = Submodule.Quotient.mk p
  apply (Submodule.Quotient.eq _).mpr
  apply hmin
  change π (g b - p) = 0
  rw [map_sub, ← LinearMap.comp_apply, hg, hb, sub_self]

/-- An explicit linear equivalence for a split surjection, with the kernel
as the second summand. It is used below to produce the local sheaf summand. -/
@[expose] noncomputable def splitEquiv (g : B →ₗ[R] P) (s : P →ₗ[R] B)
    (hs : g.comp s = LinearMap.id) : B ≃ₗ[R] P × LinearMap.ker g := by
  have hs' (p : P) : g (s p) = p := LinearMap.congr_fun hs p
  let k : B →ₗ[R] LinearMap.ker g :=
    { toFun := fun b => ⟨b - s (g b), by simp [LinearMap.mem_ker, hs']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_sub]) }
  exact
    { toFun := fun b => (g b, k b)
      invFun := fun p => s p.1 + p.2
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp
      left_inv := fun b => by simp [k]
      right_inv := fun ⟨p, b⟩ => by
        apply Prod.ext
        · simp [hs']
        · apply Subtype.ext
          simp [k, hs'] }

/-- The full minimal-cover splitting required at each descending vertex.
The new kernel is proved finite free over the local ring, not introduced
as a free summand hypothesis. -/
theorem exists_split_minimal_cover [Module.Free R B] [Module.Finite R B]
    [Module.Free R P] [Module.Finite R P]
    (π : P →ₗ[R] N) (φ : B →ₗ[R] N)
    (hπ : Function.Surjective π) (hφ : Function.Surjective φ)
    (hmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) :
    ∃ (g : B →ₗ[R] P) (e : B ≃ₗ[R] P × LinearMap.ker g),
      Function.Surjective g ∧ π.comp g = φ ∧
      Module.Free R (LinearMap.ker g) ∧ Module.Finite R (LinearMap.ker g) ∧
      ∀ b, (e b).1 = g b ∧ π (e b).1 = φ b := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property π φ hπ
  have hsurj := lift_surjective π φ g hφ hg hmin
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let e := splitEquiv g s hs
  let k : B →ₗ[R] LinearMap.ker g := (LinearMap.snd R P (LinearMap.ker g)).comp e.toLinearMap
  have hk : Function.Surjective k := by
    intro b
    exact ⟨e.symm (0, b), by simp [k]⟩
  have hki : k.comp (LinearMap.ker g).subtype = LinearMap.id := by
    ext b
    change ((b : B) - s (g b)) = b
    simp []
  let : Module.Finite R (LinearMap.ker g) := Module.Finite.of_surjective k hk
  let : Module.Projective R (LinearMap.ker g) :=
    Module.Projective.of_split (LinearMap.ker g).subtype k hki
  let : Module.Free R (LinearMap.ker g) := Module.free_of_flat_of_isLocalRing
  refine ⟨g, e, hsurj, hg, inferInstance, inferInstance, ?_⟩
  intro b
  exact ⟨rfl, LinearMap.congr_fun hg b⟩

end KLInvariance.LocalCover
end

end OAI
