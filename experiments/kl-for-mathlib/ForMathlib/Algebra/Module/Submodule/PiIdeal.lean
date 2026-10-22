module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Submodule.PiIdeal. Source spans: GradedSheaves:11.
See migration.json and MIGRATION.md for exact provenance.
Coordinatewise membership in an ideal multiple of a finite dependent product. No cover or local-ring structure is assumed. -/

namespace OAI

section
namespace KLInvariance.LocalCover
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
  (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Coordinatewise membership in the ideal multiple of a finite product. -/
lemma pi_mem_ideal_smul (I : Ideal R) (f : ∀ i, M i)
    (hf : ∀ i, f i ∈ I • (⊤ : Submodule R (M i))) :
    f ∈ I • (⊤ : Submodule R (∀ i, M i)) := by
  classical
  have hs (i : ι) : Pi.single i (f i) ∈ I • (⊤ : Submodule R (∀ i, M i)) := by
    have hmap : (I • (⊤ : Submodule R (M i))).map (LinearMap.single R M i) ≤
        I • (⊤ : Submodule R (∀ i, M i)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap ⟨f i,hf i,rfl⟩
  simpa only [Finset.univ_sum_single] using Submodule.sum_mem (I • (⊤ : Submodule R (∀ i, M i))) (t := Finset.univ) (fun i _ => hs i)

end KLInvariance.LocalCover
end

end OAI
