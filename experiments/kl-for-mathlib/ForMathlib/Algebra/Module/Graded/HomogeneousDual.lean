module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.HomogeneousEquiv

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.HomogeneousDual. Source spans: Support:25, Support:13.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]

/-- Cancellation of an injective homogeneous scalar action includes the
inverse grading shift. It does not require the scalar to be a unit. -/
 theorem mem_of_homogeneous_smul (d : ℤ) (a : A) (ha : a ∈ 𝓐 d)
    (hinj : Function.Injective (fun m : M => a • m))
    (n : ℤ) (m : M) (hm : a • m ∈ 𝓜 n) : m ∈ 𝓜 (n-d) := by
  have hc : component 𝓜 (n-d) m = m := by
    apply hinj
    change a • component 𝓜 (n-d) m = a • m
    rw [← component_homogeneous_smul 𝓐 𝓜 d a ha]
    exact DirectSum.decompose_of_mem_same 𝓜 hm
  rw [← hc]
  exact (DirectSum.decompose 𝓜 m (n-d)).property

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul 𝓐 𝓜]
  {ι : Type ui} [Fintype ι] (b : Basis ι A M) (d : ι → ℤ)
  (hb : ∀ i, b i ∈ 𝓜 (d i))
noncomputable section

include hb in
 theorem homogeneous_basis_repr (n : ℤ) (v : M) (hv : v ∈ 𝓜 n) (i : ι) :
    b.repr v i ∈ 𝓐 (n-d i) := by
  let _ : DirectSum.Decomposition (shiftedPiece 𝓐 d) :=
    (shifted_isInternal 𝓐 d).chooseDecomposition
  have hg : ∀ n f, f ∈ shiftedPiece 𝓐 d n → b.equivFun.symm f ∈ 𝓜 (n+0) := by
    intro n f hf
    rw [add_zero,b.equivFun_symm_apply]
    apply Submodule.sum_mem
    intro j _
    simpa only [vadd_eq_add,sub_add_cancel] using SetLike.GradedSMul.smul_mem (hf j) (hb j)
  have h := equiv_inverse_homogeneous (shiftedPiece 𝓐 d) 𝓜 b.equivFun.symm 0 hg n v hv
  rw [sub_zero] at h
  exact h i

include hb in
 theorem dualBasis_homogeneous [DecidableEq ι] (i : ι) (n : ℤ) (v : M) (hv : v ∈ 𝓜 n) :
    b.dualBasis i v ∈ 𝓐 (n+(-d i)) := by
  simpa only [Basis.coe_dualBasis,Basis.coord_apply,← sub_eq_add_neg] using
    homogeneous_basis_repr 𝓐 𝓜 b d hb n v hv i

end
end KLInvariance.Graded
end

end OAI
