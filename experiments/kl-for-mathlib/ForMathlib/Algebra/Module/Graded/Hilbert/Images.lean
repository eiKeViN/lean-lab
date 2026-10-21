import Mathlib
import ForMathlib.Algebra.Module.Graded.Hilbert.Series

/-! Semantic home: ForMathlib.Algebra.Module.Graded.Hilbert.Images. Source spans: Support:19, Support:20.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
  (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)

 def scalarDegreeMap (n : ℤ) : 𝓜 (n-d) →ₗ[k]
    subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a)) n :=
  { toFun := fun m => ⟨⟨a • m.val,⟨m.val,rfl⟩⟩,by
      change a • m.val ∈ 𝓜 n
      simpa using SetLike.GradedSMul.smul_mem ha m.property⟩
    map_add' := by intros; ext; exact smul_add _ _ _
    map_smul' := by intros; ext; exact smul_comm _ _ _ }

 theorem scalarDegreeMap_surjective (n : ℤ) :
    Function.Surjective (scalarDegreeMap 𝓐 𝓜 a d ha n) := by
  rintro ⟨⟨m,v,hv⟩,hm⟩
  refine ⟨DirectSum.decompose 𝓜 v (n-d), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change a • component 𝓜 (n-d) v = m
  rw [← component_homogeneous_smul 𝓐 𝓜 d a ha n v]
  change (DirectSum.decompose 𝓜 (a • v) n : M) = m
  change a • v = m at hv
  rw [hv]
  exact DirectSum.decompose_of_mem_same 𝓜 hm

omit [DirectSum.Decomposition 𝓜] in
 theorem scalarDegreeMap_injective (hinj : Function.Injective (fun m : M => a • m)) (n : ℤ) :
    Function.Injective (scalarDegreeMap 𝓐 𝓜 a d ha n) := by
  intro v w h
  apply Subtype.ext
  apply hinj
  exact congrArg (fun t => t.val.val) h

noncomputable def scalarDegreeEquiv
    (hinj : Function.Injective (fun m : M => a • m)) (n : ℤ) :
    𝓜 (n-d) ≃ₗ[k] subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a)) n :=
  LinearEquiv.ofBijective (scalarDegreeMap 𝓐 𝓜 a d ha n)
    ⟨scalarDegreeMap_injective 𝓐 𝓜 a d ha hinj n,
      scalarDegreeMap_surjective 𝓐 𝓜 a d ha n⟩

include ha in
 theorem scalar_value
    (hinj : Function.Injective (fun m : M => a • m)) {q : ℝ} (hq : q ≠ 0)
    (hs : Summable (term 𝓜 ⊤ q)) :
    value (subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a))) ⊤ q =
      q^d * value 𝓜 ⊤ q := by
  have h := (hs.hasSum.mul_left (q^d))
  have hh : HasSum
      (fun n : ℤ => (Module.finrank k (𝓜 (n-d)) : ℝ)*q^n)
      (q^d * value 𝓜 ⊤ q) := by
    apply (Equiv.addRight d).hasSum_iff.mp
    apply h.congr_fun
    intro n
    rw [term_top]
    change (Module.finrank k (𝓜 (n+d-d)) : ℝ)*q^(n+d) =
      q^d * ((Module.finrank k (𝓜 n) : ℝ)*q^n)
    rw [add_sub_cancel_right,zpow_add₀ hq]
    ring
  apply HasSum.tsum_eq
  apply hh.congr_fun
  intro n
  rw [term_top,← LinearEquiv.finrank_eq (scalarDegreeEquiv 𝓐 𝓜 a d ha hinj n)]

include ha in


 theorem scalarQuotient_value [∀ n, Module.Finite k (𝓜 n)]
    (hinj : Function.Injective (fun m : M => a • m)) {q : ℝ} (hq : 0 < q)
    (hs : Summable (term 𝓜 ⊤ q)) :
    value (quotientPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a))) ⊤ q =
      (1-q^d) * value 𝓜 ⊤ q := by
  let S := LinearMap.range (LinearMap.lsmul A M a)
  let : DirectSum.Decomposition (quotientPiece 𝓜 S) :=
    (quotient_isInternal 𝓜 S (scalar_range_homogeneous 𝓐 𝓜 d a ha)).chooseDecomposition
  have h := value_exact_of_summable 𝓜 (quotientPiece 𝓜 S) S.mkQ
    (fun n m hm => Submodule.mem_map.mpr ⟨m,hm,rfl⟩) S.mkQ_surjective hq hs
  rw [Submodule.ker_mkQ] at h
  change value 𝓜 ⊤ q = value (subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a))) ⊤ q + _ at h
  rw [scalar_value 𝓐 𝓜 a d ha hinj hq.ne' hs] at h
  change value (quotientPiece 𝓜 S) ⊤ q = _
  linarith

end KLInvariance.Hilbert
end


section
namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 def imageMap (S : Submodule A M) (f : M →ₗ[A] N) : S →ₗ[A] S.map f where
  toFun v := ⟨f v.val,Submodule.mem_map.mpr ⟨_,v.property,rfl⟩⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' _ _ := by ext; exact map_smul f _ _

 theorem imageMap_surjective (S : Submodule A M) (f : M →ₗ[A] N) :
    Function.Surjective (imageMap S f) := by
  rintro ⟨m,hm⟩
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
  exact ⟨⟨v,hv⟩,rfl⟩

 theorem imageMap_ker (S : Submodule A M) (f : M →ₗ[A] N) (a : A)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = a • w)
    (hS : ∀ v, a • v ∈ S → v ∈ S) :
    LinearMap.ker (imageMap S f) = LinearMap.range (LinearMap.lsmul A S a) := by
  ext v
  constructor
  · intro hv
    have hz : f v.val = 0 := congrArg Subtype.val hv
    obtain ⟨w,hw⟩ := (hf v.val).mp hz
    have hwS : w ∈ S := hS w (hw ▸ v.property)
    exact ⟨⟨w,hwS⟩,Subtype.ext hw.symm⟩
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    exact (hf (a • w.val)).mpr ⟨w.val,rfl⟩

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem map_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) :
    ∀ n v, v ∈ S.map f → component 𝓝 n v ∈ S.map f := by
  intro n v hv
  obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hv
  refine Submodule.mem_map.mpr ⟨component 𝓜 n w,hS n w hw,?_⟩
  simpa using (map_component 𝓜 𝓝 f 0 (by simpa using hf) n w).symm

/-- The actual upper image of a saturated graded submodule has precisely
`(1-q^d)` times its Hilbert series. No choice of edge basis enters this identity. -/
theorem saturated_image_value
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    [SetLike.GradedSMul 𝓐 𝓜] [∀ n, Module.Finite k (𝓜 n)]
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component 𝓜 n m ∈ S)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)
    (hk : ∀ v, f v = 0 ↔ ∃ w, v = a • w)
    (hsat : ∀ v, a • v ∈ S → v ∈ S)
    (hinj : Function.Injective (fun v : M => a • v))
    {q : ℝ} (hq : 0 < q) (hs : Summable (term 𝓜 (S.restrictScalars k) q)) :
    value 𝓝 ((S.map f).restrictScalars k) q =
      (1-q^d) * value 𝓜 (S.restrictScalars k) q := by
  let : DirectSum.Decomposition (subPiece 𝓜 S) := (sub_isInternal 𝓜 S hS).chooseDecomposition
  let : DirectSum.Decomposition (subPiece 𝓝 (S.map f)) :=
    (sub_isInternal 𝓝 (S.map f) (map_homogeneous 𝓜 𝓝 S hS f hf)).chooseDecomposition
  let (n : ℤ) : Module.Finite k (subPiece 𝓜 S n) := Module.Finite.of_surjective
    (subPieceEquiv 𝓜 S n).symm.toLinearMap (subPieceEquiv 𝓜 S n).symm.surjective
  have hs' : Summable (term (subPiece 𝓜 S) ⊤ q) :=
    hs.congr (fun n => (term_subPiece 𝓜 S q n).symm)
  have h := value_exact_of_summable (subPiece 𝓜 S) (subPiece 𝓝 (S.map f))
    (imageMap S f) (fun n v hv => hf n v.val hv) (imageMap_surjective S f) hq hs'
  rw [imageMap_ker S f a hk hsat] at h
  have hinj' : Function.Injective (fun v : S => a • v) := by
    intro v w hv
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hv
  rw [scalar_value 𝓐 (subPiece 𝓜 S) a d ha hinj' hq.ne' hs',
    value_subPiece,value_subPiece] at h
  linarith

end KLInvariance.Hilbert
end

end OAI
