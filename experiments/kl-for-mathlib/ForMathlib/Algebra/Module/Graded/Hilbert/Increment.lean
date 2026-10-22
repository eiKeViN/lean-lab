module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.Hilbert.Series

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.Hilbert.Increment. Source spans: PositiveTransfer:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem shifted_map_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) :
    ∀ n v, v ∈ S.map f → component 𝓝 n v ∈ S.map f := by
  intro n v hv
  obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hv
  exact Submodule.mem_map.mpr ⟨component 𝓜 (n-d) w,hS (n-d) w hw,
    (map_component 𝓜 𝓝 f d hf n w).symm⟩

 @[expose] def shiftedImagePieceMap (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (S : Submodule A M) (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) (n : ℤ) :
    subPiece 𝓜 S (n-d) →ₗ[k] subPiece 𝓝 (S.map f) n where
  toFun v := ⟨⟨f v.val.val,Submodule.mem_map.mpr ⟨_,v.val.property,rfl⟩⟩,
    by
      change f v.val.val ∈ 𝓝 n
      simpa using hf (n-d) v.val.val v.property⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' c v := by ext; exact (f.restrictScalars k).map_smul c v.val.val

 theorem shiftedImagePieceMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d)) (n : ℤ) :
    Function.Surjective (shiftedImagePieceMap 𝓜 𝓝 S f d hf n) := by
  rintro ⟨⟨m,hm⟩,hgrad⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  refine ⟨⟨⟨component 𝓜 (n-d) v,hS (n-d) v hv⟩,
    (DirectSum.decompose 𝓜 v (n-d)).property⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change f (component 𝓜 (n-d) v) = f v
  rw [← map_component 𝓜 𝓝 f d hf n v]
  exact DirectSum.decompose_of_mem_same 𝓝 hgrad

@[expose] noncomputable def shiftedImagePieceEquiv
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d))
    (hinj : Function.Injective f) (n : ℤ) :
    subPiece 𝓜 S (n-d) ≃ₗ[k] subPiece 𝓝 (S.map f) n :=
  LinearEquiv.ofBijective (shiftedImagePieceMap 𝓜 𝓝 S f d hf n) ⟨by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    apply hinj
    exact congrArg (fun z => z.val.val) h,
    shiftedImagePieceMap_surjective 𝓜 𝓝 S hS f d hf n⟩

/-- Hilbert series of the actual embedded image of a homogeneous injection. -/
 theorem shifted_image_value
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (d : ℤ) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 (n+d))
    (hinj : Function.Injective f) {q : ℝ} (hq : q ≠ 0)
    (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓝 ((S.map f).restrictScalars k) q =
      q^d * value 𝓜 (S.restrictScalars k) q := by
  have hb : HasSum
      (fun n : ℤ => (Module.finrank k (piece 𝓜 (S.restrictScalars k) (n-d)) : ℝ)*q^n)
      (q^d * value 𝓜 (S.restrictScalars k) q) :=
    hasSum_shift_coeff hq
      (show HasSum (fun n => (Module.finrank k (piece 𝓜 (S.restrictScalars k) n) : ℝ) * q^n) _ from
        by apply hs.hasSum.congr_fun; intro n; rfl) d
  apply HasSum.tsum_eq
  apply hb.congr_fun
  intro n
  unfold term
  rw [← (subPieceEquiv 𝓝 (S.map f) n).finrank_eq,
    ← (shiftedImagePieceEquiv 𝓜 𝓝 S hS f d hf hinj n).finrank_eq,
    (subPieceEquiv 𝓜 S (n-d)).finrank_eq]

end KLInvariance.Hilbert
end

end OAI
