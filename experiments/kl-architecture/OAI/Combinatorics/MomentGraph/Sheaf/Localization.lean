import Mathlib
import OAI.Combinatorics.MomentGraph.Sheaf.Extension
import OAI.Combinatorics.MomentGraph.Sheaf.Models

/-! Semantic home: OAI.Combinatorics.MomentGraph.Sheaf.Localization. Source spans: PlaneLocalization:10, PlaneLocalization:14, PlaneLocalization:12, PlaneLocalization:5, PlaneLocalization:2, PlaneLocalization:15, PlaneLocalization:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem edge_subsingleton_of_unit (α : E → R) (hq : B.UpperQuotient α)
    (e : E) (he : IsUnit (α e)) : Subsingleton (B.edge e) := by
  obtain ⟨a,ha⟩ := he
  have hz : ∀ v : B.edge e, v=0 := by
    intro v
    obtain ⟨w,rfl⟩ := (hq e).1 v
    apply ((hq e).2 w).mpr
    refine ⟨(↑a⁻¹ : R) • w,?_⟩
    rw [← ha,smul_smul]
    simp
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

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

 def supportedOutgoing (x : V) (F : Set (Outgoing (G := G) x)) : Finset (Outgoing (G := G) x) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ F ∧ G.target e.val ≤ c)

 def kernelProduct (x : V) (F : Set (Outgoing (G := G) x)) : R :=
  ∏ e ∈ supportedOutgoing G c x F, α e.val

 theorem structure_kernel_iff_dvd (x : V) (hx : x ≤ c)
    (F : Set (Outgoing (G := G) x))
    (hrel : (supportedOutgoing G c x F : Set (Outgoing (G := G) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => α e.val)))
    (v : (structureSheaf G α c).vertex x) :
    v ∈ (structureSheaf G α c).upwardKernel x F ↔ kernelProduct G α c x F ∣ v ⟨hx⟩ := by
  classical
  constructor
  · intro hv
    apply Finset.prod_dvd_of_isRelPrime hrel
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    have hvv := congrFun (hv e hh.1) ⟨hh.2⟩
    rcases e with ⟨e,he⟩
    subst x
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hvv)
  · intro hv e he
    funext h
    have hh : e ∈ supportedOutgoing G c x F :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,h.down⟩
    have hd : α e.val ∣ v ⟨hx⟩ := (Finset.dvd_prod_of_mem (fun a => α a.val) hh).trans hv
    rcases e with ⟨e,heq⟩
    subst x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)

 theorem structure_kernel_product (x : V) (F : Set (Outgoing (G := G) x))
    (hrel : (supportedOutgoing G c x F : Set (Outgoing (G := G) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => α e.val))) :
    (structureSheaf G α c).upwardKernel x F =
      kernelProduct G α c x F • (⊤ : Submodule R ((structureSheaf G α c).vertex x)) := by
  classical
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  by_cases hx : x ≤ c
  · rw [structure_kernel_iff_dvd G α c x hx F hrel]
    constructor
    · rintro ⟨r,hr⟩
      refine ⟨fun _ => r,Submodule.mem_top,?_⟩
      funext h
      exact hr.symm
    · rintro ⟨w,_,hw⟩
      exact ⟨w ⟨hx⟩,(congrFun hw ⟨hx⟩).symm⟩
  · let _ := structureSheaf_support G α c x hx
    constructor
    · intro _
      exact ⟨0,Submodule.mem_top,Subsingleton.elim _ _⟩
    · intro _
      rw [Subsingleton.elim v 0]
      exact Submodule.zero_mem _

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} {W : Type uw} [PartialOrder W]
  {F : Type uf} {H : OrderedGraph W F}
noncomputable section

 def propPiEquiv (N : Type*) [AddCommGroup N] [Module R N]
    {p q : Prop} (h : p ↔ q) : (PLift p → N) ≃ₗ[R] (PLift q → N) where
  toFun v t := v ⟨h.mpr t.down⟩
  invFun v t := v ⟨h.mp t.down⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem moduleEq_pi_apply {X : Type*} (p : X → Prop) {x y : X} (h : x=y)
    (v : PLift (p x) → R) (t : PLift (p y)) :
    moduleEq (congrArg (fun z => ModuleCat.of R (PLift (p z) → R)) h) v t =
      v ⟨h.symm ▸ t.down⟩ := by
  subst y
  rfl

 def structurePullbackIso (f : GraphMap G H) (α : F → R) (c : V)
    (ho : ∀ x y, f.vertex x ≤ f.vertex y ↔ x ≤ y) :
    Iso ((structureSheaf H α (f.vertex c)).pullback f)
      (structureSheaf G (fun e => α (f.edge e)) c) where
  vertex x := propPiEquiv R (ho x c)
  edge e := propPiEquiv (R ⧸ Ideal.span {α (f.edge e)}) (by
    rw [← f.target e]; exact ho (G.target e) c)
  lower e v := by
    change (PLift (f.vertex (G.source e) ≤ f.vertex c) → R) at v
    funext h
    change Ideal.Quotient.mk _
      (moduleEq (congrArg (fun z => ModuleCat.of R (PLift (z ≤ f.vertex c) → R))
        (f.source e)) v _) = Ideal.Quotient.mk _ (v _)
    apply congrArg (Ideal.Quotient.mk _)
    exact moduleEq_pi_apply (fun z => z ≤ f.vertex c) (f.source e) v _
  upper e v := by
    change (PLift (f.vertex (G.target e) ≤ f.vertex c) → R) at v
    funext h
    change Ideal.Quotient.mk _
      (moduleEq (congrArg (fun z => ModuleCat.of R (PLift (z ≤ f.vertex c) → R))
        (f.target e)) v _) = Ideal.Quotient.mk _ (v _)
    apply congrArg (Ideal.Quotient.mk _)
    exact moduleEq_pi_apply (fun z => z ≤ f.vertex c) (f.target e) v _

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [IsLocalRing R]
  {V : Type uv} [PartialOrder V] {E : Type ue} (G : OrderedGraph V E) (α : E → R)
noncomputable section

 def structureLocalModels
    (hα : ∀ e, α e ∈ IsLocalRing.maximalIdeal R)
    (hreach : ∀ x c, x < c → ∃ e, G.source e = x ∧ G.target e ≤ c)
    (hfl : ∀ c, (structureSheaf G α c).Flabby) : LocalModels (G := G) α where
  sheaf := structureSheaf G α
  free := structureSheaf_free G α
  finite := structureSheaf_finite G α
  quotient := structureSheaf_upperQuotient G α
  generated := structureSheaf_generated G α
  flabby := hfl
  support := structureSheaf_support G α
  top c := structureVertexIso G α c c le_rfl
  minimal c x hx := structureSheaf_minimal G α c hα (fun x => hreach x c) x hx

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}
  {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  {B C : Sheaf.{u,v,w,z} (R := R) G}


theorem extend_modelSum {U : Set V} (hU : IsUpperSet U)
    (hC : ModelSum O.sheaf U C) (j : OnIso B C U)
    (hBq : B.UpperQuotient α) (hBf : B.Flabby) (hBg : B.Generated)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U)
    [Module.Free R (B.vertex x)] [Module.Finite R (B.vertex x)] :
    ∃ D : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf (insert x U) D ∧ Nonempty (OnIso B D (insert x U)) := by
  classical
  let := hC.free O x
  let := hC.finite O x
  obtain ⟨g,jv,hfree,hfinite,hjv⟩ := (j.above x hmax).extend_stalk
    hBf hBg (hC.flabby O) (hC.generated O) (hC.minimal O x hx)
  let := hfree
  let := hfinite
  let n := Module.finrank R (LinearMap.ker g)
  let S : Sheaf.{u,v,w,z} (R := R) G := pi (fun _ : Fin n => O.sheaf x)
  let jq : LinearMap.ker g ≃ₗ[R] S.vertex x :=
    (Module.finBasis R (LinearMap.ker g)).equivFun.trans
      (LinearEquiv.piCongrRight (fun _ : Fin n => O.top x)).symm
  let jv' : B.vertex x ≃ₗ[R] (prod C S).vertex x :=
    jv.trans (LinearEquiv.prodCongr (LinearEquiv.refl R (C.vertex x)) jq)
  have hSV (y : V) (hy : y ∈ U) : Subsingleton (S.vertex y) :=
    pi_subsingleton_vertex _ y (fun _ => O.support x y (fun hyx => hx (hU hyx hy)))
  have hSE (e : E) (he : G.target e ∈ U) : Subsingleton (S.edge e) := by
    apply pi_subsingleton_edge
    intro i
    let := O.support x (G.target e) (fun h => hx (hU h he))
    exact (O.quotient x e).1.subsingleton
  let jj : OnIso B (prod C S) U := j.prodZero S hSV hSE
  have hq : (prod C S).UpperQuotient α :=
    prod_upperQuotient C S α (hC.quotient O) (pi_upperQuotient _ α (fun _ => O.quotient x))
  have hout : ∀ e (he : G.source e = x) v,
      jj.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.lower e v) = (prod C S).lower e (castStalkIso B (prod C S) he.symm jv' v) := by
    intro e he v
    subst x
    apply Prod.ext
    · exact hjv v ⟨e,rfl⟩
    · let := hSE e (hmax (G.increasing e))
      exact Subsingleton.elim _ _
  refine ⟨prod C S,?_,⟨jj.extend hU x hx hmax α hBq hq jv' hout⟩⟩
  exact .add (hC.mono (Set.subset_insert x U)) x (Set.mem_insert x U) n

end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}

 theorem lower_surjective_of_generated (B : Sheaf (R := R) G) (hg : B.Generated)
    (hu : ∀ e, Function.Surjective (B.upper e)) (e : E) : Function.Surjective (B.lower e) := by
  intro v
  obtain ⟨w,hw⟩ := hu e v
  obtain ⟨s,hs,ht⟩ := hg (G.target e) w
  refine ⟨s (G.source e),?_⟩
  rw [hs e (Set.mem_univ _) (Set.mem_univ _),ht,hw]

variable [DecompositionMonoid R] [Fintype E] (α : E → R) (c : V)

 theorem structure_lower_image (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (hrel : (supportedOutgoing G c (G.source e) F : Set (Outgoing (G := G) (G.source e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val))) :
    ((structureSheaf G α c).upwardKernel (G.source e) F).map ((structureSheaf G α c).lower e) =
      kernelProduct G α c (G.source e) F • (⊤ : Submodule R ((structureSheaf G α c).edge e)) := by
  rw [structure_kernel_product G α c _ F hrel,Submodule.map_pointwise_smul,Submodule.map_top]
  congr 1
  apply LinearMap.range_eq_top.mpr
  exact lower_surjective_of_generated _ (structureSheaf_generated G α c)
    (fun a => (structureSheaf_upperQuotient G α c a).1) e

 theorem structure_upper_image (e : E) (F : Set (Outgoing (G := G) (G.target e)))
    (hrel : (supportedOutgoing G c (G.target e) F : Set (Outgoing (G := G) (G.target e))).Pairwise
      (Function.onFun IsRelPrime (fun a => α a.val))) :
    ((structureSheaf G α c).upwardKernel (G.target e) F).map ((structureSheaf G α c).upper e) =
      kernelProduct G α c (G.target e) F • (⊤ : Submodule R ((structureSheaf G α c).edge e)) := by
  rw [structure_kernel_product G α c _ F hrel,Submodule.map_pointwise_smul,Submodule.map_top]
  congr 1
  exact LinearMap.range_eq_top.mpr (structureSheaf_upperQuotient G α c e).1

end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}
  {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  (B : Sheaf.{u,v,w,z} (R := R) G)

/-- Actual finite descending decomposition over a local ring. This does not
assume that localization preserves indecomposability. Its explicitly stated
rank-one model criteria must be proved before applying it to a root plane. -/
theorem exists_modelSumIso [Finite V]
    (hBfree : ∀ x, Module.Free R (B.vertex x))
    (hBfinite : ∀ x, Module.Finite R (B.vertex x))
    (hBq : B.UpperQuotient α) (hBf : B.Flabby) (hBg : B.Generated) :
    ∃ C : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf Set.univ C ∧ Nonempty (Iso B C) := by
  classical
  let := Fintype.ofFinite V
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ C : Sheaf.{u,v,w,z} (R := R) G,
      ModelSum O.sheaf ((s : Set V)ᶜ) C → OnIso B C ((s : Set V)ᶜ) →
      ∃ D : Sheaf.{u,v,w,z} (R := R) G,
        ModelSum O.sheaf Set.univ D ∧ Nonempty (Iso B D) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU C hC j
      by_cases hs : s = ∅
      · subst s
        have hh : ((∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
        exact ⟨C,hh ▸ hC,⟨OnIso.ofUniv (hh ▸ j)⟩⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        let := hBfinite x
        obtain ⟨D,hD,⟨jj⟩⟩ := extend_modelSum O hU hC j hBq hBf hBg x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') D (heq ▸ hD) (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : OnIso B zero (∅ : Set V) :=
    ⟨fun x hx => False.elim hx,fun e he => False.elim he,
      fun e hs => False.elim hs,fun e ht => False.elim ht⟩
  have hinit := h Finset.univ
  rw [hset] at hinit
  exact hinit isUpperSet_empty zero .zero hj

end KLInvariance.MomentGraph.Sheaf
end

end OAI
