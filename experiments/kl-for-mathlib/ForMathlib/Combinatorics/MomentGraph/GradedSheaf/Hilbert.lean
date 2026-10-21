import Mathlib
import ForMathlib.Algebra.Module.Graded.Hilbert.Increment
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hilbert. Source spans: PositiveTransfer:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe us um
variable {σ : Type us} [Fintype σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  (B : GradedSheaf (𝓐 := polynomialGrading ℝ σ) G)
noncomputable section

 def kernelHilbert (q : ℝ) (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) : ℝ :=
  value (B.vertex x).piece ((B.upwardSubmodule x F).restrictScalars ℝ) q

 def lowerImage (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e))) :
    Submodule (MvPolynomial σ ℝ) (B.edge e) :=
  (B.upwardSubmodule (G.source e) F).map (B.lower e).map

 def upperImage (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.target e))) :
    Submodule (MvPolynomial σ ℝ) (B.edge e) :=
  (B.upwardSubmodule (G.target e) F).map (B.upper e).map

omit [Fintype σ] in
 theorem upperImage_homogeneous (e : E) (H : Set (Sheaf.Outgoing (G := G) (G.target e))) :
    ∀ n v, v ∈ B.upperImage e H → component (B.edge e).piece n v ∈ B.upperImage e H :=
  map_homogeneous (B.vertex (G.target e)).piece (B.edge e).piece
    (B.upwardSubmodule (G.target e) H) (B.upwardKernel_homogeneous (G.target e) H)
    (B.upper e).map (B.upper e).graded

 theorem kernelHilbert_edge (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) =
      value (B.edge e).piece ((B.lowerImage e F).restrictScalars ℝ) q := by
  let : ∀ n, Module.Finite ℝ ((B.vertex (G.source e)).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.vertex (G.source e)).piece
  have h := B.hilbert_edge_increment (G.source e) F ⟨e,rfl⟩ hq
    (summable_term ℝ σ (B.vertex (G.source e)).piece _ hq hq1)
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

 theorem shifted_upperImage_value (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    value (B.edge e).piece (((B.upperImage e H).map φ).restrictScalars ℝ) q =
      q^d * (1-q) * B.kernelHilbert q (G.target e) H := by
  let : ∀ n, Module.Finite ℝ ((B.vertex (G.target e)).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.vertex (G.target e)).piece
  rw [shifted_image_value (B.edge e).piece (B.edge e).piece (B.upperImage e H)
    (B.upperImage_homogeneous e H) φ d hφ hφinj hq.ne'
    (summable_term ℝ σ (B.edge e).piece _ hq hq1)]
  rw [show value (B.edge e).piece ((B.upperImage e H).restrictScalars ℝ) q =
    (1-q) * B.kernelHilbert q (G.target e) H from
      B.upper_image_value α hquot e H ha hreg hinj hq
        (summable_term ℝ σ (B.vertex (G.target e)).piece _ hq hq1)]
  exact (mul_assoc _ _ _).symm


 theorem edge_increment_le (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) (hinc : B.lowerImage e F ≤ (B.upperImage e H).map φ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) ≤
      q^d * (1-q) * B.kernelHilbert q (G.target e) H := by
  let : ∀ n, Module.Finite ℝ ((B.edge e).piece n) :=
    polynomialModule_piece_finite ℝ σ (B.edge e).piece
  rw [B.kernelHilbert_edge e F hq hq1,
    ← B.shifted_upperImage_value α hquot e H ha hreg hinj φ d hφ hφinj hq hq1]
  exact (summable_term ℝ σ (B.edge e).piece _ hq hq1).tsum_le_tsum
    (term_mono (B.edge e).piece hinc hq)
    (summable_term ℝ σ (B.edge e).piece _ hq hq1)

/-- Even a finite-length or higher-codimension embedded defect is detected by
one positive numerical equality. This does not replace the image inclusion. -/
 theorem edge_increment_eq_iff (α : E → MvPolynomial σ ℝ) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.source e)))
    (H : Set (Sheaf.Outgoing (G := G) (G.target e)))
    (ha : α e ∈ polynomialGrading ℝ σ 1)
    (hreg : ∀ f ∈ H, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    (φ : B.edge e →ₗ[MvPolynomial σ ℝ] B.edge e) (d : ℤ)
    (hφ : ∀ n v, v ∈ (B.edge e).piece n → φ v ∈ (B.edge e).piece (n+d))
    (hφinj : Function.Injective φ) (hinc : B.lowerImage e F ≤ (B.upperImage e H).map φ)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    (B.kernelHilbert q (G.source e) F -
      B.kernelHilbert q (G.source e) (insert ⟨e,rfl⟩ F) =
      q^d * (1-q) * B.kernelHilbert q (G.target e) H) ↔
      B.lowerImage e F = (B.upperImage e H).map φ := by
  rw [B.kernelHilbert_edge e F hq hq1,
    ← B.shifted_upperImage_value α hquot e H ha hreg hinj φ d hφ hφinj hq hq1]
  constructor
  · intro heq
    have h := polynomial_eq_of_value_eq ℝ σ (B.edge e).piece hinc
      (shifted_map_homogeneous (B.edge e).piece (B.edge e).piece (B.upperImage e H)
        (B.upperImage_homogeneous e H) φ d hφ) hq hq1 heq
    ext v
    exact SetLike.ext_iff.mp h v
  · intro heq
    rw [heq]

end
end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
