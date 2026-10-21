import Mathlib
import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Extension
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Models
import ForMathlib.LinearAlgebra.Dual.BalancedCut

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models. Source spans: CharacterReciprocity:8, CharacterReciprocity:26, CharacterReciprocity:10, CharacterReciprocity:31, CharacterReciprocity:3, CharacterReciprocity:19, CharacterReciprocity:9, CharacterReciprocity:33.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 abbrev kernelData (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :=
  B.upwardKernel x Set.univ

 def kernelProdEquiv (B C : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData (prod B C) x ≃ₗ[A] ((kernelData B x).prod (kernelData C x)) where
  toFun m := ⟨⟨m.val.1,((Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ m.val).mp m.property).1⟩,
    ⟨m.val.2,((Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ m.val).mp m.property).2⟩⟩
  invFun m := ⟨⟨m.1.val,m.2.val⟩,(Sheaf.prod_upwardKernel_iff B.forget C.forget x Set.univ _).mpr
    ⟨m.1.property,m.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem kernelProdEquiv_graded (B C : GradedSheaf (𝓐 := 𝓐) G) (x : V)
    (n : ℤ) (v : kernelData (prod B C) x) (hv : v∈(kernelData (prod B C) x).piece n) :
    kernelProdEquiv B C x v∈((kernelData B x).prod (kernelData C x)).piece n := hv

 def kernelPiEquiv {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData (pi B) x ≃ₗ[A] ModuleData.pi (fun i => kernelData (B i) x) where
  toFun m i := ⟨m.val i,(Sheaf.pi_upwardKernel_iff (fun i => (B i).forget) x Set.univ m.val).mp m.property i⟩
  invFun m := ⟨(fun i => (m i).val),(Sheaf.pi_upwardKernel_iff (fun i => (B i).forget) x Set.univ _).mpr
    (fun i => (m i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem kernelPiEquiv_graded {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) (x : V)
    (n : ℤ) (v : kernelData (pi B) x) (hv : v∈(kernelData (pi B) x).piece n) :
    kernelPiEquiv B x v∈(ModuleData.pi (fun i => kernelData (B i) x)).piece n := hv

 def kernelShiftEquiv (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) (d : ℕ) :
    kernelData (B.shift d) x ≃ₗ[A] (kernelData B x).shift d := LinearEquiv.refl A _

 theorem kernelShiftEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) (d : ℕ)
    (n : ℤ) (v : kernelData (B.shift d) x) (hv : v∈(kernelData (B.shift d) x).piece n) :
    kernelShiftEquiv B x d v∈((kernelData B x).shift d).piece n := hv

 def Iso.kernelEquiv {B C : GradedSheaf (𝓐 := 𝓐) G} (j : Iso B C) (x : V) :
    kernelData B x ≃ₗ[A] kernelData C x where
  toFun m := ⟨j.vertex x m.val,(j.toIso.upwardKernel_iff x Set.univ m.val).mpr m.property⟩
  invFun m := ⟨(j.vertex x).symm m.val,(j.toIso.symm.upwardKernel_iff x Set.univ m.val).mpr m.property⟩
  left_inv m := Subtype.ext ((j.vertex x).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((j.vertex x).apply_symm_apply m.val)
  map_add' m n := Subtype.ext (map_add (j.vertex x) m.val n.val)
  map_smul' a m := Subtype.ext (map_smul (j.vertex x) a m.val)

 theorem Iso.kernelEquiv_graded {B C : GradedSheaf (𝓐 := 𝓐) G} (j : Iso B C) (x : V)
    (n : ℤ) (v : kernelData B x) (hv : v∈(kernelData B x).piece n) :
    j.kernelEquiv x v∈(kernelData C x).piece n := j.vertex_graded x n v.val hv

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def Hom.coefficientUnchange {S T : GradedSheaf (𝓐 := 𝓐) G}
    (g : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he T)) : Hom S T where
  vertex x := ModuleData.unchangeHom e he (g.vertex x)
  edge f := ModuleData.unchangeHom e he (g.edge f)
  lower f m := congrArg CoefficientChange.val (g.lower f (CoefficientChange.mk m))
  upper f m := congrArg CoefficientChange.val (g.upper f (CoefficientChange.mk m))

 theorem coefficientChange_primitive (S : GradedSheaf (𝓐 := 𝓐) G)
    (hS : (Hom.id S).PrimitiveProjector) :
    (Hom.id (GradedSheaf.coefficientChange e he S)).PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    let g : Hom S S := f.coefficientUnchange e he
    have hg : g.comp g=g := by
      apply Hom.eq_of_maps
      · intro x m
        exact congrArg (fun q : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he S) =>
          ((q.vertex x).map (CoefficientChange.mk m)).val) hf
      · intro x m
        exact congrArg (fun q : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he S) =>
          ((q.edge x).map (CoefficientChange.mk m)).val) hf
    have hgL : g.comp (Hom.id S)=g := by apply Hom.eq_of_maps <;> intros <;> rfl
    have hgR : (Hom.id S).comp g=g := by apply Hom.eq_of_maps <;> intros <;> rfl
    rcases hS.2 g hg hgL hgR with hz | hi
    · left
      apply Hom.eq_of_maps
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.vertex x).map m.val) hz
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.edge x).map m.val) hz
    · right
      apply Hom.eq_of_maps
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.vertex x).map m.val) hi
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.edge x).map m.val) hi

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section
 def kernelEquivFull (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData B x ≃ₗ[A] LinearMap.ker (B.forget.stalkMap x) where
  toFun m := ⟨m.val,funext (fun e => m.property e (Set.mem_univ e))⟩
  invFun m := ⟨m.val,fun e _ => congrFun m.property e⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K : Set V} {hK : IsLowerSet K}

omit [IsNoetherianRing A] in
 theorem lowerExtend_kernel_iff (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) (m : B.lowerExtend.vertex x.val) :
    m∈B.lowerExtend.upwardSubmodule x.val Set.univ ↔
      B.lowerExtendVertex x m∈B.upwardSubmodule x Set.univ := by
  constructor
  · intro hm e _
    rcases e with ⟨⟨e,he⟩,hx⟩
    cases hx
    have hh := hm ⟨e,rfl⟩ (Set.mem_univ _)
    exact congrFun hh ⟨⟨he⟩⟩
  · intro hm e _
    rcases x with ⟨x,hx⟩
    rcases e with ⟨e,he⟩
    change G.source e=x at he
    subst x
    apply funext
    intro h
    have hh := hm ⟨⟨e,h.down.down⟩,rfl⟩ (Set.mem_univ _)
    exact hh

 def lowerExtendKernelEquiv (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) : kernelData B.lowerExtend x.val ≃ₗ[A] kernelData B x where
  toFun m := ⟨B.lowerExtendVertex x m.val,(lowerExtend_kernel_iff B x m.val).mp m.property⟩
  invFun m := ⟨(B.lowerExtendVertex x).symm m.val,(lowerExtend_kernel_iff B x _).mpr (by
    simpa only [LinearEquiv.apply_symm_apply] using m.property)⟩
  left_inv m := Subtype.ext ((B.lowerExtendVertex x).symm_apply_apply m.val)
  right_inv m := Subtype.ext ((B.lowerExtendVertex x).apply_symm_apply m.val)
  map_add' m n := Subtype.ext (map_add (B.lowerExtendVertex x) m.val n.val)
  map_smul' a m := Subtype.ext (map_smul (B.lowerExtendVertex x) a m.val)

 theorem lowerExtendKernelEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))
    (x : K) (n : ℤ) (m : kernelData B.lowerExtend x.val)
    (hm : m∈(kernelData B.lowerExtend x.val).piece n) :
    B.lowerExtendKernelEquiv x m∈(kernelData B x).piece n :=
  B.lowerExtendVertex_graded x n m.val hm

omit [IsNoetherianRing A] in
 theorem fullKernel_pullback (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V) :
    (B.pullback f).upwardSubmodule x Set.univ=B.upwardSubmodule (f.vertex x) Set.univ := by
  exact B.forget.pullback_kernel f x Set.univ Set.univ
    (fun e he => (he (Set.mem_univ e)).elim) (fun e _ he => hlift e x he)

 def pullbackKernelEquiv (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V) :
    kernelData (B.pullback f) x ≃ₗ[A] kernelData B (f.vertex x) where
  toFun m := ⟨m.val,fullKernel_pullback B f hlift x ▸ m.property⟩
  invFun m := ⟨m.val,(fullKernel_pullback B f hlift x).symm ▸ m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem pullbackKernelEquiv_graded (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V)
    (n : ℤ) (m : kernelData (B.pullback f) x) (hm : m∈(kernelData (B.pullback f) x).piece n) :
    B.pullbackKernelEquiv f hlift x m∈(kernelData B (f.vertex x)).piece n := hm

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} [IsDomain A] [DecidableEq V]
  {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ} (p : PerfectPairing S d)
  (a : A) (ha : a≠0)
  (hcut : ∀ x (m : S.forget.sections Set.univ), a • Pi.single x (m.val x)∈S.forget.sections Set.univ)
noncomputable section

 include ha in
 theorem PerfectPairing.cut_balanced (x : V) (m n : S.forget.sections Set.univ) :
    p.pairing (IntegralSupport.cut _ a hcut x m) n =
      p.pairing m (IntegralSupport.cut _ a hcut x n) := by
  apply BalancedCuts.balanced_two p.pairing.toLinearMap
    (IntegralSupport.projection (S.forget.sections Set.univ) x)
    (IntegralSupport.cut _ a hcut x) a ha
    (IntegralSupport.cut_self _ a hcut x)
  · intro v w hw
    exact p.left_orthogonal x _ w (fun y hy => IntegralSupport.cut_other _ a hcut x y hy v) hw
  · intro v w hv
    exact p.right_orthogonal x v _ hv (fun y hy => IntegralSupport.cut_other _ a hcut x y hy w)

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 theorem SplitIn.imageSectionEquiv_symm_coordinates (U : Set V)
    (n : B.forget.sections U) (x : V) :
    (((s.imageSectionEquiv U).symm n).val x).val=(s.inclusion.vertex x).map (n.val x) := by
  rw [s.imageSectionEquiv_symm_apply]
  change (s.inclusion.vertex x).map ((s.projection.vertex x).map
    ((s.inclusion.vertex x).map (n.val x)))=(s.inclusion.vertex x).map (n.val x)
  exact congrArg (s.inclusion.vertex x).map (s.vertex_split x (n.val x))

 theorem SplitIn.imageSectionEquiv_symm_inclusion (U : Set V)
    (n : B.forget.sections U) :
    s.projector.imageInclusion.sectionMap U ((s.imageSectionEquiv U).symm n)=
      s.inclusion.sectionMap U n := by
  apply Subtype.ext
  funext x
  exact s.imageSectionEquiv_symm_coordinates U n x

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 instance kernelShiftFree (B : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V) (d : ℕ)
    [Module.Free (MvPolynomial σ k) (kernelData B x)] :
    Module.Free (MvPolynomial σ k) (kernelData (B.shift d) x) :=
  Module.Free.of_equiv (kernelShiftEquiv B x d).symm

 instance kernelProdFree (B C : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [Module.Free (MvPolynomial σ k) (kernelData B x)]
    [Module.Free (MvPolynomial σ k) (kernelData C x)] :
    Module.Free (MvPolynomial σ k) (kernelData (prod B C) x) :=
  Module.Free.of_equiv (kernelProdEquiv B C x).symm

 instance kernelPiFree {ι : Type um} [Fintype ι]
    (B : ι → GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [∀ i, Module.Free (MvPolynomial σ k) (kernelData (B i) x)] :
    Module.Free (MvPolynomial σ k) (kernelData (pi B) x) :=
  Module.Free.of_equiv (kernelPiEquiv B x).symm

 instance kernelZeroFree (x : V) :
    Module.Free (MvPolynomial σ k) (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) := by
  let : Subsingleton (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  infer_instance

 theorem kernelChar_shift (B : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V) (d : ℕ)
    [Module.Free (MvPolynomial σ k) (kernelData B x)] :
    (kernelData (B.shift d) x).char=X^d*(kernelData B x).char := by
  rw [← ModuleData.char_shift _ d]
  exact ModuleData.character_eq_of_gradedEquiv (kernelShiftEquiv B x d)
    (kernelShiftEquiv_graded B x d)

 theorem kernelChar_prod (B C : GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [Module.Free (MvPolynomial σ k) (kernelData B x)]
    [Module.Free (MvPolynomial σ k) (kernelData C x)] :
    (kernelData (prod B C) x).char=(kernelData B x).char+(kernelData C x).char := by
  rw [← ModuleData.char_prod]
  exact ModuleData.character_eq_of_gradedEquiv (kernelProdEquiv B C x)
    (kernelProdEquiv_graded B C x)

 theorem kernelChar_pi {ι : Type um} [Fintype ι]
    (B : ι → GradedSheaf (𝓐 := polynomialGrading k σ) G) (x : V)
    [∀ i, Module.Free (MvPolynomial σ k) (kernelData (B i) x)] :
    (kernelData (pi B) x).char=∑ i, (kernelData (B i) x).char := by
  rw [← ModuleData.char_pi]
  exact ModuleData.character_eq_of_gradedEquiv (kernelPiEquiv B x) (kernelPiEquiv_graded B x)

 theorem kernelChar_zero (x : V) :
    (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x).char=0 := by
  let : Subsingleton (kernelData (zero (𝓐 := polynomialGrading k σ) (G := G)) x) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  exact ModuleData.char_zero _

 theorem ModelSum.kernelFree {O : V → GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (hf : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O y) x))
    {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O U B) (x : V) : Module.Free (MvPolynomial σ k) (kernelData B x) := by
  induction h with
  | zero => infer_instance
  | @add C _ c _ n d ih =>
    let _ := ih
    let _ := hf c x
    infer_instance

 def freeKernelChar (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (kernelData B x)) (x : V) : Polynomial ℤ := by
  let := hf x
  exact (kernelData B x).char

 theorem ModelSum.character_both [Fintype V] {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (hk : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O.sheaf y) x))
    {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O.sheaf U B) :
    ∃ m : V → Polynomial ℤ, (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, freeStalkChar B (h.free O) x =
        ∑ y, m y*freeStalkChar (O.sheaf y) (O.free y) x) ∧
      (∀ x, freeKernelChar B (h.kernelFree hk) x =
        ∑ y, m y*freeKernelChar (O.sheaf y) (hk y) x) := by
  classical
  induction h with
  | zero =>
    refine ⟨0,by simp,?_,?_⟩
    · intro x
      change ((GradedSheaf.zero (𝓐 := polynomialGrading k σ) (G := G)).vertex x).char = _
      simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
      exact ModuleData.char_zero _
    · intro x
      change (kernelData (GradedSheaf.zero (𝓐 := polynomialGrading k σ) (G := G)) x).char = _
      simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
      exact kernelChar_zero (σ := σ) (G := G) x
  | @add B h c hc n d ih =>
    obtain ⟨m,hm,heq,hkeq⟩ := ih
    let a : Polynomial ℤ := ∑ i, X^(d i)
    have ha (r : ℕ) : 0 ≤ a.coeff r := by
      simp only [a,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
      exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
    refine ⟨fun y => m y+if y=c then a else 0,?_,?_,?_⟩
    · intro y r
      rw [Polynomial.coeff_add]
      apply add_nonneg (hm y r)
      split
      · exact ha r
      · simp
    · intro x
      let _ := h.free O x
      let _ := O.free c x
      change ((B.vertex x).prod (ModuleData.pi (fun i => ((O.sheaf c).vertex x).shift (d i)))).char = _
      rw [ModuleData.char_prod,ModuleData.char_pi]
      simp only [ModuleData.char_shift]
      change freeStalkChar B (h.free O) x + _ = _
      rw [heq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl
    · intro x
      let _ := h.kernelFree hk x
      let _ := hk c x
      change (kernelData (prod B (pi (fun i => (O.sheaf c).shift (d i)))) x).char = _
      rw [kernelChar_prod,kernelChar_pi]
      simp only [kernelChar_shift]
      change freeKernelChar B (h.kernelFree hk) x + _ = _
      rw [hkeq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 theorem exists_character_decomposition [Fintype V] [Fintype E]
    {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (hk : ∀ y x, Module.Free (MvPolynomial σ k) (kernelData (O.sheaf y) x))
    (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x))
    (hkb : ∀ x, Module.Free (MvPolynomial σ k) (kernelData B x))
    (hq : B.UpperQuotient α) (hfl : B.forget.Flabby) (hg : B.forget.Generated) :
    ∃ m : V → Polynomial ℤ, (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, freeStalkChar B hf x =
        ∑ y, m y*freeStalkChar (O.sheaf y) (O.free y) x) ∧
      (∀ x, freeKernelChar B hkb x =
        ∑ y, m y*freeKernelChar (O.sheaf y) (hk y) x) := by
  obtain ⟨C,hC,⟨j⟩⟩ := exists_modelSumIso (polynomialGrading_zero k σ) O B hf hq hfl hg
  obtain ⟨m,hm,heq,hkeq⟩ := hC.character_both O hk
  refine ⟨m,hm,fun x => ?_,fun x => ?_⟩
  · rw [← heq x]
    let _ := hf x
    let _ := hC.free O x
    exact ModuleData.character_eq_of_gradedEquiv (j.vertex x) (j.vertex_graded x)
  · rw [← hkeq x]
    let _ := hkb x
    let _ := hC.kernelFree hk x
    exact ModuleData.character_eq_of_gradedEquiv (j.kernelEquiv x) (j.kernelEquiv_graded x)

end
end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
