module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure. Source spans: MinimalExtensions:14, MinimalExtensions:18.
See migration.json and MIGRATION.md for exact provenance.
The scalar-quotient structure sheaf, its defining properties, natural base-change isomorphism and preservation of flabbiness. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

private def quotientLinear (e : E) : R →ₗ[R] R ⧸ Ideal.span {α e} :=
  (Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap

 @[expose] def structureSheaf : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (PLift (x ≤ c) → R)
  edge e := ModuleCat.of R (PLift (G.target e ≤ c) → R ⧸ Ideal.span {α e})
  upper e := LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp (LinearMap.proj h))
  lower e := LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp
    (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩))

 theorem structureSheaf_free (x : V) : Module.Free R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Free R (PLift (x ≤ c) → R))

 theorem structureSheaf_finite (x : V) : Module.Finite R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Finite R (PLift (x ≤ c) → R))

 theorem structureSheaf_support (x : V) (hx : ¬ x ≤ c) :
    Subsingleton ((structureSheaf G α c).vertex x) := by
  refine ⟨fun f g => funext fun h => False.elim (hx h.down)⟩

 @[expose] def structureVertexIso (x : V) (hx : x ≤ c) :
    (structureSheaf G α c).vertex x ≃ₗ[R] R where
  toFun f := f ⟨hx⟩
  invFun r := fun _ => r
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem structureSheaf_generated : (structureSheaf G α c).Generated := by
  classical
  intro x v
  by_cases hx : x ≤ c
  · refine ⟨fun _ _ => v ⟨hx⟩, fun _ _ _ => rfl, rfl⟩
  · let _ := structureSheaf_support G α c x hx
    exact ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩

 theorem structureSheaf_upperQuotient : (structureSheaf G α c).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose r hr using fun h : PLift (G.target e ≤ c) => Ideal.Quotient.mk_surjective (v h)
    exact ⟨r,funext hr⟩
  · intro v
    constructor
    · intro hv
      have hh (h : PLift (G.target e ≤ c)) :
          v h ∈ Ideal.span {α e} := Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv h)
      choose r hr using fun h => Ideal.mem_span_singleton.mp (hh h)
      exact ⟨r,funext hr⟩
    · rintro ⟨w,rfl⟩
      funext h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨w h,rfl⟩)

 theorem structureSheaf_minimal [IsLocalRing R]
    (hα : ∀ e, α e ∈ IsLocalRing.maximalIdeal R)
    (hreach : ∀ x, x < c → ∃ e, G.source e = x ∧ G.target e ≤ c)
    (x : V) (hxc : x ≠ c) :
    LinearMap.ker ((structureSheaf G α c).stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R ((structureSheaf G α c).vertex x)) := by
  classical
  intro v hv
  by_cases hx : x ≤ c
  · obtain ⟨e,he,het⟩ := hreach x (lt_of_le_of_ne hx hxc)
    subst x
    have heq := congrFun (LinearMap.mem_ker.mp hv) ⟨e,rfl⟩
    have hvα : v ⟨hx⟩ ∈ Ideal.span {α e} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (congrFun heq ⟨het⟩)
    have hm : v ⟨hx⟩ ∈ IsLocalRing.maximalIdeal R :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hα e))) hvα
    let one : (structureSheaf G α c).vertex (G.source e) := fun _ => 1
    have hs : v ⟨hx⟩ • one ∈ IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) :=
      Submodule.smul_mem_smul hm (show one ∈
        (⊤ : Submodule R ((structureSheaf G α c).vertex (G.source e))) from Submodule.mem_top)
    have heqv : v = v ⟨hx⟩ • one := by
      funext h
      exact (mul_one _).symm
    rw [heqv]
    exact hs
  · let _ := structureSheaf_support G α c x hx
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um un
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}
noncomputable section

namespace Iso
variable {B : Sheaf.{ur,uv,ue,um} (R := R) G}
  {C : Sheaf.{ur,uv,ue,un} (R := R) G} (j : Iso B C)
include j

 theorem flabby (hb : B.Flabby) : C.Flabby := by
  intro Ω hΩ f hf
  have hsf : B.CompatibleOn Ω (j.symm.assignments f) :=
    (j.symm.compatible_iff Ω f).mpr hf
  obtain ⟨g,hg,hgf⟩ := hb Ω hΩ (j.symm.assignments f) hsf
  refine ⟨j.assignments g,(j.compatible_iff Set.univ g).mpr hg,?_⟩
  intro x hx
  rw [j.assignments_apply,hgf x hx]
  exact (congrArg (j.vertex x) (j.symm.assignments_apply f x)).trans
    ((j.vertex x).apply_symm_apply _)

 theorem generated (hb : B.Generated) : C.Generated := by
  intro x v
  obtain ⟨f,hf,hfv⟩ := hb x ((j.vertex x).symm v)
  refine ⟨j.assignments f,(j.compatible_iff Set.univ f).mpr hf,?_⟩
  rw [j.assignments_apply,hfv,LinearEquiv.apply_symm_apply]

end Iso

variable (S : Type us) [CommRing S] [Algebra R S]

@[expose] def baseChangeScalar : S ⊗[R] R ≃ₗ[S] S := AlgebraTensorModule.rid R S S

@[simp] theorem baseChangeScalar_tmul (s : S) (r : R) :
    baseChangeScalar S (s ⊗ₜ[R] r) = s * algebraMap R S r := by
  change r • s = s * algebraMap R S r
  rw [Algebra.smul_def,mul_comm]

 theorem span_map (a : R) :
    (Ideal.span {a}).map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
  rw [Ideal.map_span,Set.image_singleton]

 @[expose] def baseChangeQuotient (a : R) :
    S ⊗[R] (R ⧸ Ideal.span {a}) ≃ₗ[S] S ⧸ Ideal.span {algebraMap R S a} :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {a})).symm.toLinearEquiv.trans
    (Ideal.quotientEquivAlgOfEq S (span_map S a)).toLinearEquiv

@[simp] theorem baseChangeQuotient_tmul (a r : R) (s : S) :
    baseChangeQuotient S a (s ⊗ₜ[R] Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (s * algebraMap R S r) := by
  simp only [baseChangeQuotient,LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_apply,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk _ (r • s) = Ideal.Quotient.mk _ (s * algebraMap R S r)
  rw [Algebra.smul_def,mul_comm]


 @[expose] def baseChangePiScalar (p : Prop) :
    S ⊗[R] (PLift p → R) ≃ₗ[S] (PLift p → S) := by
  classical
  exact (TensorProduct.piRight R S S (fun _ : PLift p => R)).trans
    (LinearEquiv.piCongrRight (fun _ => baseChangeScalar S))

 @[expose] def baseChangePiQuotient (a : R) (p : Prop) :
    S ⊗[R] (PLift p → R ⧸ Ideal.span {a}) ≃ₗ[S]
      (PLift p → S ⧸ Ideal.span {algebraMap R S a}) := by
  classical
  exact (TensorProduct.piRight R S S
    (fun _ : PLift p => R ⧸ Ideal.span {a})).trans
      (LinearEquiv.piCongrRight (fun _ => baseChangeQuotient S a))

 theorem baseChangePiScalar_tmul (p : Prop) (s : S) (v : PLift p → R) (h : PLift p) :
    baseChangePiScalar S p (s ⊗ₜ v) h = s * algebraMap R S (v h) :=
  baseChangeScalar_tmul S s (v h)

 theorem baseChangePiQuotient_tmul (a : R) (p : Prop)
    (s : S) (v : PLift p → R ⧸ Ideal.span {a}) (h : PLift p) :
    baseChangePiQuotient S a p (s ⊗ₜ v) h = baseChangeQuotient S a (s ⊗ₜ v h) := rfl

 @[expose] def quotientPullback (a : R) (p q : Prop) (h : q → p) :
    (PLift p → R) →ₗ[R] (PLift q → R ⧸ Ideal.span {a}) :=
  LinearMap.pi fun t => (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap.comp
    (LinearMap.proj ⟨h t.down⟩)

 /-- Pull back a scalar function and reduce each value modulo the label. -/
 @[simp] theorem quotientPullback_apply (a : R) (p q : Prop) (h : q → p)
    (v : PLift p → R) (t : PLift q) :
    quotientPullback a p q h v t = Ideal.Quotient.mk _ (v ⟨h t.down⟩) := by rfl

 theorem baseChangePi_natural (a : R) (p q : Prop) (h : q → p)
    (v : S ⊗[R] (PLift p → R)) :
    baseChangePiQuotient S a q
      (AlgebraTensorModule.lTensor S S (quotientPullback a p q h) v) =
      quotientPullback (algebraMap R S a) p q h (baseChangePiScalar S p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    funext hh
    change baseChangePiQuotient S a q (s ⊗ₜ quotientPullback a p q h v) hh = _
    rw [baseChangePiQuotient_tmul]
    rw [quotientPullback_apply, baseChangeQuotient_tmul, quotientPullback_apply,
      baseChangePiScalar_tmul]
  | add v w hv hw => simp only [map_add,hv,hw]

 @[expose] def structureBaseChangeIso (G : OrderedGraph V E) (α : E → R) (c : V) :
    Iso ((structureSheaf G α c).baseChange S)
      (structureSheaf G (fun e => algebraMap R S (α e)) c) where
  vertex x := baseChangePiScalar S (x ≤ c)
  edge e := baseChangePiQuotient S (α e) (G.target e ≤ c)
  lower e v := baseChangePi_natural S (α e) (G.source e ≤ c) (G.target e ≤ c)
    ((G.increasing e).le.trans ·) v
  upper e v := baseChangePi_natural S (α e) (G.target e ≤ c) (G.target e ≤ c) id v

 theorem structureSheaf_flat_flabby [Finite V] [Finite E] [Module.Flat R S]
    (G : OrderedGraph V E) (α : E → R) (c : V) (hf : (structureSheaf G α c).Flabby) :
    (structureSheaf G (fun e => algebraMap R S (α e)) c).Flabby :=
  (structureBaseChangeIso S G α c).flabby ((structureSheaf G α c).baseChange_flabby S hf)

end
end KLInvariance.MomentGraph.Sheaf
end

end OAI
