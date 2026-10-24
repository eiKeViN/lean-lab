module
public import Mathlib
public import ForMathlib.Algebra.Module.Flat.Kernel
public import ForMathlib.Algebra.Module.Localization.Membership
public import ForMathlib.Algebra.Module.Submodule.ProductScaling
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Localization

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages. Source spans: TerminalKernels:14, TerminalKernels:7, TerminalKernels:1, TerminalKernels:18, TerminalKernels:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} [Finite E] {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section
open scoped Classical

 @[expose] def outgoingLabelProduct (α : E → R) (x : V) (F : Set (Outgoing (G := G) x)) : R :=
   ∏ f ∈ F.toFinite.toFinset, α f.val

 theorem outgoingLabelProduct_dvd (α : E → R) (x : V) (F : Set (Outgoing (G := G) x))
    (f : Outgoing (G := G) x) (hf : f ∈ F) : α f.val ∣ outgoingLabelProduct α x F := by
   exact Finset.dvd_prod_of_mem _ (F.toFinite.mem_toFinset.mpr hf)

 theorem outgoingLabelProduct_smul_mem (α : E → R) (hα : ∀ e (v : B.edge e), α e • v=0)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    outgoingLabelProduct α x F • v ∈ B.upwardKernel x F := by
   intro f hf
   obtain ⟨r,hr⟩ := outgoingLabelProduct_dvd α x F f hf
   rw [map_smul,hr,mul_comm,mul_smul]
   have h := hα f.val (B.stalkMap x v f)
   change r • (α f.val • B.stalkMap x v f) = 0
   rw [h,smul_zero]

 theorem outgoingLabelProduct_smul_upperImage (α : E → R) (hα : ∀ e (v : B.edge e), α e • v=0)
    (e : E) (hq : Function.Surjective (B.upper e))
    (F : Set (Outgoing (G := G) (G.target e))) (v : B.edge e) :
    outgoingLabelProduct α (G.target e) F • v ∈
      (B.upwardKernel (G.target e) F).map (B.upper e) := by
   obtain ⟨w,rfl⟩ := hq v
   exact ⟨_,B.outgoingLabelProduct_smul_mem α hα _ F w,(B.upper e).map_smul _ w⟩

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section

 @[expose] def kernelConstraint (x : V) (F : Set (Outgoing (G := G) x)) :
    B.vertex x →ₗ[R] (∀ e : F, B.edge e.val.val) :=
  LinearMap.pi (fun e => (LinearMap.proj e.val).comp (B.stalkMap x))

 theorem ker_kernelConstraint (x : V) (F : Set (Outgoing (G := G) x)) :
    LinearMap.ker (B.kernelConstraint x F) = B.upwardKernel x F := by
  ext v
  constructor
  · intro h e he
    exact congrFun (LinearMap.mem_ker.mp h) ⟨e,he⟩
  · intro h
    exact LinearMap.mem_ker.mpr (funext fun e => h e.val e.property)

 theorem kernelConstraint_tensor (x : V) (F : Set (Outgoing (G := G) x))
    (z : S ⊗[R] B.vertex x) :
    (B.baseChange S).kernelConstraint x F z =
      TensorProduct.piRightHom R S S (fun e : F => B.edge e.val.val)
        ((B.kernelConstraint x F).baseChange S z) := by
  let k : (S ⊗[R] B.vertex x) →ₗ[S] (∀ e : F, S ⊗[R] B.edge e.val.val) :=
    (B.baseChange S).kernelConstraint x F
  change k z = _
  induction z using TensorProduct.inductionOn with
  | tmul s v =>
    funext e
    rcases e with ⟨⟨e,he⟩,heF⟩
    subst x
    rfl
  | add z t hz ht =>
    simp only [map_add,hz,ht]

 theorem baseChange_upwardKernel [Finite E] [Module.Flat R S]
    (x : V) (F : Set (Outgoing (G := G) x)) :
    (B.upwardKernel x F).baseChange S = (B.baseChange S).upwardKernel x F := by
  classical
  let := Fintype.ofFinite E
  rw [← B.ker_kernelConstraint x F,FlatSubmodule.baseChange_ker,
    ← (B.baseChange S).ker_kernelConstraint x F]
  ext z
  change (B.kernelConstraint x F).baseChange S z = 0 ↔
    (B.baseChange S).kernelConstraint x F z = 0
  rw [B.kernelConstraint_tensor S]
  exact ((TensorProduct.piRight R S S (fun e : F => B.edge e.val.val)).map_eq_zero_iff).symm

 theorem baseChange_lowerImage [Finite E] [Module.Flat R S]
    (e : E) (F : Set (Outgoing (G := G) (G.source e))) :
    ((B.upwardKernel (G.source e) F).map (B.lower e)).baseChange S =
      ((B.baseChange S).upwardKernel (G.source e) F).map ((B.baseChange S).lower e) := by
  rw [FlatSubmodule.baseChange_map,B.baseChange_upwardKernel S]
  rfl

 theorem baseChange_upperImage [Finite E] [Module.Flat R S]
    (e : E) (F : Set (Outgoing (G := G) (G.target e))) :
    ((B.upwardKernel (G.target e) F).map (B.upper e)).baseChange S =
      ((B.baseChange S).upwardKernel (G.target e) F).map ((B.baseChange S).upper e) := by
  rw [FlatSubmodule.baseChange_map,B.baseChange_upwardKernel S]
  rfl

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf.Iso
universe ur uv ue uz uz'
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}
  {B : Sheaf.{ur,uv,ue,uz} (R := R) G} {C : Sheaf.{ur,uv,ue,uz'} (R := R) G}
  (j : Iso B C)

/-- Membership in a lower kernel image is transported by the inverse edge
isomorphism. The vertex-kernel condition and lower commuting square are both
included, so callers do not have to transport witnesses themselves. -/
theorem mem_lowerImage_iff_symm (e : E)
    (F : Set (Outgoing (G := G) (G.source e))) (z : C.edge e) :
    z ∈ (C.upwardKernel (G.source e) F).map (C.lower e) ↔
      (j.edge e).symm z ∈ (B.upwardKernel (G.source e) F).map (B.lower e) := by
  rw [← j.map_lowerImage e F, Submodule.mem_map_equiv]

/-- Membership in a scalar multiple of an upper kernel image is transported
by the inverse edge isomorphism. The scalar is arbitrary, including zero; no
injectivity of scalar multiplication is used. -/
theorem mem_scaledUpperImage_iff_symm (e : E)
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) (z : C.edge e) :
    (∃ w ∈ C.upwardKernel (G.target e) H, r • C.upper e w = z) ↔
      ∃ w ∈ B.upwardKernel (G.target e) H, r • B.upper e w = (j.edge e).symm z := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hw' : (j.vertex (G.target e)).symm w ∈ B.upwardKernel (G.target e) H := by
      apply (j.upwardKernel_iff _ _ _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hw
    refine ⟨_,hw',?_⟩
    apply (j.edge e).injective
    rw [map_smul,j.upper,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,he]
  · rintro ⟨w,hw,he⟩
    refine ⟨j.vertex (G.target e) w,(j.upwardKernel_iff _ _ _).mpr hw,?_⟩
    rw [← j.upper,← map_smul,he,LinearEquiv.apply_symm_apply]

include j in
 theorem scaledImages (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (h : B.ScaledImages e F H r) : C.ScaledImages e F H r := by
  intro z
  exact (j.mem_lowerImage_iff_symm e F z).trans
    ((h ((j.edge e).symm z)).trans (j.mem_scaledUpperImage_iff_symm e H r z).symm)

end KLInvariance.MomentGraph.Sheaf.Iso
end


section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Finite E] {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
  (P : Submonoid R) [IsLocalization P S]
noncomputable section

 theorem scaledImages_denominator
    (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (a : R)
    (h : (B.baseChange S).ScaledImages e F H (algebraMap R S a))
    (x : B.edge e) (hx : x ∈ (B.upwardKernel (G.source e) F).map (B.lower e)) :
    ∃ s : P, (s:R) • x ∈ ((B.upwardKernel (G.target e) H).map (B.upper e)).map
      (LinearMap.lsmul R (B.edge e) a) := by
  let _ : Module.Flat R S := IsLocalization.flat S P
  apply TensorLocalMembership.denominator S P _ x
  rw [FlatSubmodule.baseChange_map,B.baseChange_upperImage S]
  have hx' : 1 ⊗ₜ[R] x ∈ ((B.baseChange S).upwardKernel (G.source e) F).map
      ((B.baseChange S).lower e) := by
    rw [← B.baseChange_lowerImage S]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  obtain ⟨v,hv,he⟩ := hx'
  obtain ⟨w,hw,hwx⟩ := (h (1 ⊗ₜ[R] x)).mp ⟨v,hv,he⟩
  refine ⟨(B.baseChange S).upper e w,⟨w,hw,rfl⟩,?_⟩
  change (LinearMap.lsmul R (B.edge e) a).baseChange S ((B.baseChange S).upper e w) = _
  have hg : (LinearMap.lsmul R (B.edge e) a).baseChange S =
      LinearMap.lsmul S (S ⊗[R] B.edge e) (algebraMap R S a) := by
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro r v
    change (LinearMap.lsmul R (B.edge e) a).baseChange S (r ⊗ₜ[R] v) =
      (algebraMap R S a) • (r ⊗ₜ[R] v)
    simp only [LinearMap.baseChange_tmul,LinearMap.lsmul_apply,
      algebraMap_smul,TensorProduct.tmul_smul,TensorProduct.smul_tmul']
  rw [hg]
  exact hwx

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue} [Fintype E]
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

/-- A quotient-product equality gives the actual two embedded model images.
The common quotient is the edge module's coefficient ring. -/
 theorem structure_scaledImages (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hF : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (hH : (supportedOutgoing G c (G.target e) H : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (h : Associated
      (algebraMap R (R ⧸ Ideal.span {α e}) (kernelProduct G α c (G.source e) F))
      (algebraMap R (R ⧸ Ideal.span {α e}) (r*kernelProduct G α c (G.target e) H))) :
    (structureSheaf G α c).ScaledImages e F H r := by
  rw [scaledImages_iff,structure_lower_image (G := G) α c e F hF,
    structure_upper_image (G := G) α c e H hH,← mul_smul]
  let S := R ⧸ Ideal.span {α e}
  let : Module S ((structureSheaf G α c).edge e) :=
    inferInstanceAs (Module S (PLift (G.target e ≤ c) → S))
  let : IsScalarTower R S ((structureSheaf G α c).edge e) :=
    inferInstanceAs (IsScalarTower R S (PLift (G.target e ≤ c) → S))
  exact LocalProducts.smul_top_eq_of_map_associated (S := S) h

 theorem structure_scaledImages_of_count (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) (p : R ⧸ Ideal.span {α e}) (k : ℕ)
    (hF : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (hH : (supportedOutgoing G c (G.target e) H : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val)))
    (ha : ∀ i ∈ supportedOutgoing G c (G.source e) F,
      Associated (algebraMap R (R ⧸ Ideal.span {α e}) (α i.val)) p)
    (hb : ∀ i ∈ supportedOutgoing G c (G.target e) H,
      Associated (algebraMap R (R ⧸ Ideal.span {α e}) (α i.val)) p)
    (hr : Associated (algebraMap R (R ⧸ Ideal.span {α e}) r) (p^k))
    (hc : (supportedOutgoing G c (G.source e) F).card=
      (supportedOutgoing G c (G.target e) H).card+k) :
    (structureSheaf G α c).ScaledImages e F H r := by
  apply structure_scaledImages G α c e F H r hF hH
  simpa only [kernelProduct,map_prod,map_mul] using
    LocalProducts.associated_prod_scale _ _ _ _ p _ k ha hb hr hc

end
end KLInvariance.MomentGraph.Sheaf
end

end OAI
