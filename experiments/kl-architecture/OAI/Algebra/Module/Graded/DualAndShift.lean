import Mathlib
import OAI.Algebra.Module.CoefficientChange.Basic
import OAI.Algebra.Module.Graded.AlgebraMap
import OAI.Algebra.Module.Graded.ModuleData.Basic
import OAI.LinearAlgebra.PairProjection.Basic

/-! Semantic home: OAI.Algebra.Module.Graded.DualAndShift. Source spans: BottSamelson:8, BottSamelson:25, BottSamelson:24, BottSamelson:20, BottSamelson:28.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded
open Module
universe uk ua um un ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {P : Type un} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
noncomputable section

omit [Algebra k A] [IsScalarTower k A N] [IsScalarTower k A P] in
 theorem equiv_inverse_homogeneous
    (𝓝 : ℤ → Submodule k N) (𝓟 : ℤ → Submodule k P)
    [DirectSum.Decomposition 𝓝] [DirectSum.Decomposition 𝓟]
    (e : N ≃ₗ[A] P) (d : ℤ)
    (he : ∀ n x, x ∈ 𝓝 n → e x ∈ 𝓟 (n+d))
    (n : ℤ) (y : P) (hy : y ∈ 𝓟 n) : e.symm y ∈ 𝓝 (n-d) := by
  have hc : component 𝓝 (n-d) (e.symm y) = e.symm y := by
    apply e.injective
    change e.toLinearMap (component 𝓝 (n-d) (e.symm y)) = e.toLinearMap (e.symm y)
    rw [← map_component 𝓝 𝓟 e.toLinearMap d he n (e.symm y)]
    simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    exact DirectSum.decompose_of_mem_same 𝓟 hy
  rw [← hc]
  exact (DirectSum.decompose 𝓝 (e.symm y) (n-d)).property

variable (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedMonoid 𝓐] {ι : Type ui} [Fintype ι] [DecidableEq ι]
  (b : Basis ι A N) (d : ι → ℤ)

omit [DirectSum.Decomposition 𝓐] in
 theorem pairing_to_dual_homogeneous (p : N →ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n : ℤ} {x : N} (hx : x ∈ basisPiece 𝓐 b d n) :
    p x ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) (n-l) := by
  rw [mem_basisPiece]
  intro i
  rw [Basis.dualBasis_repr]
  have h := pairing_homogeneous 𝓐 b d p l hp hx (basis_mem_piece 𝓐 b d i)
  convert h using 1
  congr 1
  omega

 theorem perfectPairing_inverse_homogeneous (p : N ≃ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n : ℤ} {y : Dual A N}
    (hy : y ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) n) :
    p.symm y ∈ basisPiece 𝓐 b d (n+l) := by
  have he : ∀ m x, x ∈ basisPiece 𝓐 b d m →
      p x ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) (m+(-l)) := by
    intro m x hx
    exact pairing_to_dual_homogeneous 𝓐 b d p.toLinearMap l hp hx
  simpa only [sub_neg_eq_add] using equiv_inverse_homogeneous
    (basisPiece 𝓐 b d) (basisPiece 𝓐 b.dualBasis (fun i => -d i)) p (-l) he n y hy

end
end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

 instance subPiece_finite (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (n : ℤ)
    [Module.Finite k (𝓜 n)] : Module.Finite k (subPiece 𝓜 S n) := by
  let f : subPiece 𝓜 S n →ₗ[k] 𝓜 n :=
    { toFun := fun v => ⟨v.val.val,v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : 𝓜 n => z.val) h

 variable {ι : Type ui} [Finite ι] {P : ι → Type um}
   [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]

 instance piPiece_finite (𝓟 : ∀ i, ℤ → Submodule k (P i)) (n : ℤ)
    [∀ i, Module.Finite k (𝓟 i n)] : Module.Finite k (piPiece 𝓟 n) := by
  let f : piPiece 𝓟 n →ₗ[k] (∀ i, 𝓟 i n) :=
    { toFun := fun v i => ⟨v.val i,v.property i (Set.mem_univ i)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]
  (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
  (e : M ≃ₗ[k] N) (d : ℤ)
  (he : ∀ n m, m ∈ 𝓜 n → e m ∈ 𝓝 (n+d))
noncomputable section

 def homogeneousPieceEquiv (n : ℤ) : 𝓜 n ≃ₗ[k] 𝓝 (n+d) where
  toFun m := ⟨e m.val,he n m.val m.property⟩
  invFun v := ⟨e.symm v.val,by
    simpa only [add_sub_cancel_right] using
      equiv_inverse_homogeneous 𝓜 𝓝 e d he (n+d) v.val v.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' v w := Subtype.ext (map_add e v.val w.val)
  map_smul' r v := Subtype.ext (map_smul e r v.val)

include e he in
 theorem finrank_homogeneousEquiv (n : ℤ) :
    Module.finrank k (𝓝 n)=Module.finrank k (𝓜 (n-d)) := by
  have h := (homogeneousPieceEquiv 𝓜 𝓝 e d he (n-d)).finrank_eq
  have hn : n-d+d=n := by omega
  rw [hn] at h
  exact h.symm

end
end KLInvariance.Graded
end


section
namespace KLInvariance.Graded.ModuleData
open PairProjection
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (f : Hom M X) (g : Hom M Y)
noncomputable section

 theorem pairLower_kernel_homogeneous (n : ℤ) (z : X)
    (hz : lower f.map g.map z=0) :
    lower f.map g.map (component X.piece n z)=0 := by
  obtain ⟨m,hm,hy⟩ := (kernel_lower f.map g.map z).mp hz
  apply (kernel_lower f.map g.map _).mpr
  refine ⟨component M.piece n m,?_,?_⟩
  · rw [← f.component,hm]
  · rw [← g.component,hy,map_zero]

 def pairEdgePiece (n : ℤ) : Submodule k (Edge f.map g.map) :=
  (X.piece n).map ((lower f.map g.map).restrictScalars k)

 def pairEdge (hg : Function.Surjective g.map) : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (Edge f.map g.map)
  kModule := inferInstance
  tower := inferInstance
  piece := pairEdgePiece f g
  decomposition := (image_isInternal X.piece ((lower f.map g.map).restrictScalars k)
    (lower_surjective f.map g.map hg) (pairLower_kernel_homogeneous f g)).chooseDecomposition
  graded := ⟨by
    rintro i j a z ha ⟨w,hw,rfl⟩
    exact ⟨a • w,SetLike.GradedSMul.smul_mem ha hw,map_smul (lower f.map g.map) a w⟩⟩
  nonneg := by
    intro n hn
    unfold pairEdgePiece
    rw [X.nonneg n hn,Submodule.map_bot]
  finite := Module.Finite.of_surjective (lower f.map g.map) (lower_surjective f.map g.map hg)

 def pairLower (hg : Function.Surjective g.map) : Hom X (pairEdge f g hg) where
  map := lower f.map g.map
  graded := fun _ z hz => ⟨z,hz,rfl⟩

 theorem Hom.homogeneous_lift (hg : Function.Surjective g.map) (n : ℤ)
    (y : Y) (hy : y ∈ Y.piece n) : ∃ m : M, m ∈ M.piece n ∧ g.map m=y := by
  obtain ⟨m,hm⟩ := hg y
  refine ⟨Graded.component M.piece n m,(DirectSum.decompose M.piece m n).property,?_⟩
  rw [← g.component,hm]
  exact DirectSum.decompose_of_mem_same Y.piece hy

 def pairUpper (hg : Function.Surjective g.map) : Hom Y (pairEdge f g hg) where
  map := upper f.map g.map
  graded := by
    intro n y hy
    obtain ⟨m,hm,rfl⟩ := g.homogeneous_lift hg n y hy
    exact ⟨f.map m,f.graded n m hm,compatible f.map g.map m⟩

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 def changePiece (M : ModuleData.{uk,ua,um} 𝓐) : ℤ → Submodule k (CoefficientChange e M) :=
  fun n => (M.piece n).map (CoefficientChange.kEquiv e M).toLinearMap

 theorem mem_changePiece (M : ModuleData.{uk,ua,um} 𝓐) (n : ℤ) (m : CoefficientChange e M) :
    m ∈ changePiece e M n ↔ m.val ∈ M.piece n := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    change CoefficientChange.mk x=m at hxm
    exact (congrArg CoefficientChange.val hxm) ▸ hx
  · intro hm
    exact ⟨m.val,hm,rfl⟩

 def change (M : ModuleData.{uk,ua,um} 𝓐) : ModuleData.{uk,ua,um} 𝓑 where
  obj := ModuleCat.of B (CoefficientChange e M)
  kModule := inferInstance
  tower := inferInstance
  piece := changePiece e M
  decomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    apply image_isInternal M.piece (CoefficientChange.kEquiv e M).toLinearMap
      (CoefficientChange.kEquiv e M).surjective
    intro n m hm
    have hz : m=0 := congrArg CoefficientChange.val hm
    subst m
    simp only [map_zero]
  graded := by
    constructor
    intro i j b m hb hm
    apply (mem_changePiece e M (i+j) _).mpr
    change e.symm b • m.val ∈ M.piece (i+j)
    have ha : e.symm b ∈ 𝓐 i := (he i _).mpr (by simpa using hb)
    exact SetLike.GradedSMul.smul_mem ha ((mem_changePiece e M j m).mp hm)
  nonneg n hn := by simp only [changePiece,M.nonneg n hn,Submodule.map_bot]
  finite := inferInstance

 def changeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) :
    Hom (change e he M) (change e he N) where
  map := CoefficientChange.map e f.map
  graded n m hm := (mem_changePiece e N n _).mpr
    (f.graded n m.val ((mem_changePiece e M n m).mp hm))

 theorem change_free (M : ModuleData.{uk,ua,um} 𝓐) [Module.Free A M] :
    Module.Free B (change e he M) := inferInstanceAs (Module.Free B (CoefficientChange e M))

end
end KLInvariance.Graded.ModuleData
end

end OAI
