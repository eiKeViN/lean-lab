import Mathlib
import OAI.Combinatorics.MomentGraph.GradedSheaf.Extension

/-! Semantic home: OAI.Combinatorics.MomentGraph.Sheaf.Extension. Source spans: MinimalExtensions:15, MinimalExtensions:17, MinimalExtensions:14, MinimalExtensions:16, MinimalExtensions:19, MinimalExtensions:18, MinimalExtensions:22, MinimalExtensions:20, MinimalExtensions:3, MinimalExtensions:12.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

noncomputable def baseChange : Sheaf (R := S) G where
  vertex x := ModuleCat.of S (S ⊗[R] B.vertex x)
  edge e := ModuleCat.of S (S ⊗[R] B.edge e)
  lower e := AlgebraTensorModule.lTensor S S (B.lower e)
  upper e := AlgebraTensorModule.lTensor S S (B.upper e)

noncomputable def tensorAssignments : S ⊗[R] B.Assignment →ₗ[S] (B.baseChange S).Assignment :=
  TensorProduct.piRightHom R S S (fun x => B.vertex x)

@[simp] theorem tensorAssignments_tmul (s : S) (f : B.Assignment) (x : V) :
    B.tensorAssignments S (s ⊗ₜ f) x = s ⊗ₜ f x := rfl

lemma baseChange_tmul_compatible (Ω : Set V) (s : S) (f : B.Assignment)
    (hf : B.CompatibleOn Ω f) : (B.baseChange S).CompatibleOn Ω (fun x => s ⊗ₜ f x) := by
  intro e hs ht
  change s ⊗ₜ[R] B.lower e (f (G.source e)) = s ⊗ₜ[R] B.upper e (f (G.target e))
  rw [hf e hs ht]

noncomputable def tensorSections (Ω : Set V) :
    S ⊗[R] B.sections Ω →ₗ[S] (B.baseChange S).sections Ω :=
  ((B.tensorAssignments S).comp (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype)).codRestrict
    ((B.baseChange S).sections Ω) (by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul s f => exact B.baseChange_tmul_compatible S Ω s f.val f.property
      | add z t hz ht => simpa only [map_add] using Submodule.add_mem _ hz ht)

@[simp] theorem tensorSections_tmul (Ω : Set V) (s : S) (f : B.sections Ω) (x : V) :
    (B.tensorSections S Ω (s ⊗ₜ f)).val x = s ⊗ₜ f.val x := rfl

theorem baseChange_generated (h : B.Generated) : (B.baseChange S).Generated := by
  intro x v
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    obtain ⟨f,hf,hx⟩ := h x v
    exact ⟨fun y => s ⊗ₜ f y,B.baseChange_tmul_compatible S Set.univ s f hf,congrArg (fun v => s ⊗ₜ[R] v) hx⟩
  | add v w hv hw =>
    obtain ⟨f,hf,hfv⟩ := hv
    obtain ⟨g,hg,hgw⟩ := hw
    exact ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,congrArg₂ (·+·) hfv hgw⟩

/-- The finite section constraint whose kernel is the actual section module. -/
noncomputable def constraint (Ω : Set V) : B.Assignment →ₗ[R]
    (∀ e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω}, B.edge e.val) :=
  LinearMap.pi (fun e => (B.lower e.val).comp (LinearMap.proj (G.source e.val)) -
    (B.upper e.val).comp (LinearMap.proj (G.target e.val)))

lemma ker_constraint (Ω : Set V) : LinearMap.ker (B.constraint Ω) = B.sections Ω := by
  ext f
  constructor
  · intro h e hs ht
    have hh := congrFun (LinearMap.mem_ker.mp h) ⟨e,hs,ht⟩
    exact sub_eq_zero.mp hh
  · intro h
    apply LinearMap.mem_ker.mpr
    funext e
    exact sub_eq_zero.mpr (h e.val e.property.1 e.property.2)

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

 theorem tensorAssignments_bijective [Finite V] : Function.Bijective (B.tensorAssignments S) := by
  classical
  let := Fintype.ofFinite V
  exact (TensorProduct.piRight R S S (fun x => B.vertex x)).bijective

 theorem constraint_tensorAssignments (Ω : Set V) (z : S ⊗[R] B.Assignment) :
    (B.baseChange S).constraint Ω (B.tensorAssignments S z) =
      TensorProduct.piRightHom R S S (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} =>
        B.edge e.val) (AlgebraTensorModule.lTensor S S (B.constraint Ω) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    ext e
    change s ⊗ₜ[R] B.lower e.val (f (G.source e.val)) -
      s ⊗ₜ[R] B.upper e.val (f (G.target e.val)) =
      s ⊗ₜ[R] (B.lower e.val (f (G.source e.val)) -
        B.upper e.val (f (G.target e.val)))
    exact (tmul_sub _ _ _).symm
  | add z w hz hw => simp only [map_add,hz,hw]; rfl

 theorem tensorSections_surjective [Finite V] [Finite E] [Module.Flat R S] (Ω : Set V) :
    Function.Surjective (B.tensorSections S Ω) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  intro f
  obtain ⟨z,hz⟩ := (B.tensorAssignments_bijective S).2 f.val
  have hc : (B.baseChange S).constraint Ω (B.tensorAssignments S z) = 0 := by
    rw [hz]
    apply LinearMap.mem_ker.mp
    rw [(B.baseChange S).ker_constraint Ω]
    exact f.property
  have he : AlgebraTensorModule.lTensor S S (B.constraint Ω) z = 0 := by
    apply (TensorProduct.piRight R S S
      (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} => B.edge e.val)).injective
    rw [map_zero]
    exact (B.constraint_tensorAssignments S Ω z).symm.trans hc
  have hex : Function.Exact (B.sections Ω).subtype (B.constraint Ω) := by
    rw [← B.ker_constraint Ω]
    exact (B.constraint Ω).exact_subtype_ker_map
  obtain ⟨w,hw⟩ := (Module.Flat.lTensor_exact S hex z).mp he
  refine ⟨w,?_⟩
  apply Subtype.ext
  change B.tensorAssignments S (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype w) = _
  exact (congrArg (B.tensorAssignments S) hw).trans hz

 theorem tensorSections_injective [Finite V] [Module.Flat R S] (Ω : Set V) :
    Function.Injective (B.tensorSections S Ω) := by
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (B.sections Ω).subtype (B.sections Ω).injective_subtype
  apply (B.tensorAssignments_bijective S).1
  exact congrArg Subtype.val h

/-- Sections over every vertex subset commute with flat extension of scalars
for a finite moment graph. No freeness or BMP character input is used. -/
 def tensorSectionsEquiv [Finite V] [Finite E] [Module.Flat R S] (Ω : Set V) :
    S ⊗[R] B.sections Ω ≃ₗ[S] (B.baseChange S).sections Ω :=
  LinearEquiv.ofBijective (B.tensorSections S Ω)
    ⟨B.tensorSections_injective S Ω,B.tensorSections_surjective S Ω⟩

 theorem baseChange_flabby [Finite V] [Finite E] [Module.Flat R S]
    (hb : B.Flabby) : (B.baseChange S).Flabby := by
  intro Ω hΩ f hf
  obtain ⟨z,hz⟩ := B.tensorSections_surjective S Ω ⟨f,hf⟩
  suffices ∃ g : (B.baseChange S).Assignment, (B.baseChange S).IsGlobal g ∧
      ∀ x ∈ Ω, g x = (B.tensorSections S Ω z).val x by
    simpa only [hz] using this
  clear hz f hf
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    obtain ⟨g,hg,hgf⟩ := hb Ω hΩ f.val f.property
    refine ⟨fun x => s ⊗ₜ g x,B.baseChange_tmul_compatible S Set.univ s g hg,?_⟩
    intro x hx
    change s ⊗ₜ[R] g x = s ⊗ₜ[R] f.val x
    rw [hgf x hx]
  | add z w hz hw =>
    obtain ⟨f,hf,hfz⟩ := hz
    obtain ⟨g,hg,hgw⟩ := hw
    refine ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,?_⟩
    intro x hx
    simp only [map_add,Submodule.coe_add,Pi.add_apply]
    rw [hfz x hx,hgw x hx]

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

private def quotientLinear (e : E) : R →ₗ[R] R ⧸ Ideal.span {α e} :=
  (Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap

 def structureSheaf : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (PLift (x ≤ c) → R)
  edge e := ModuleCat.of R (PLift (G.target e ≤ c) → R ⧸ Ideal.span {α e})
  upper e := LinearMap.pi (fun h => (quotientLinear α e).comp (LinearMap.proj h))
  lower e := LinearMap.pi (fun h => (quotientLinear α e).comp
    (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩))

 theorem structureSheaf_free (x : V) : Module.Free R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Free R (PLift (x ≤ c) → R))

 theorem structureSheaf_finite (x : V) : Module.Finite R ((structureSheaf G α c).vertex x) :=
  inferInstanceAs (Module.Finite R (PLift (x ≤ c) → R))

 theorem structureSheaf_support (x : V) (hx : ¬ x ≤ c) :
    Subsingleton ((structureSheaf G α c).vertex x) := by
  refine ⟨fun f g => funext fun h => False.elim (hx h.down)⟩

 def structureVertexIso (x : V) (hx : x ≤ c) :
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
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem baseChange_vertex_free (x : V) [Module.Free R (B.vertex x)] :
    Module.Free S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Free S (S ⊗[R] B.vertex x))

 theorem baseChange_vertex_finite (x : V) [Module.Finite R (B.vertex x)] :
    Module.Finite S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Finite S (S ⊗[R] B.vertex x))

 theorem baseChange_upperQuotient [Module.Flat R S] (α : E → R)
    (h : B.UpperQuotient α) : (B.baseChange S).UpperQuotient (fun e => algebraMap R S (α e)) := by
  intro e
  refine ⟨LinearMap.lTensor_surjective S (h e).1, ?_⟩
  have hs : Function.Exact (DistribSMul.toLinearMap R (B.vertex (G.target e)) (α e))
      (B.upper e) := by
    intro v
    exact ((h e).2 v).trans (by simp only [Set.mem_range, DistribSMul.toLinearMap_apply,
      eq_comm])
  have ht := Module.Flat.lTensor_exact S hs
  intro v
  change (B.upper e).lTensor S v = 0 ↔ ∃ w, v = algebraMap R S (α e) • w
  rw [ht v, LinearMap.lTensor_smul_action]
  change (∃ w : S ⊗[R] B.vertex (G.target e), α e • w = v) ↔
    ∃ w : S ⊗[R] B.vertex (G.target e), v = algebraMap R S (α e) • w
  simp only [IsScalarTower.algebraMap_smul]
  constructor <;> rintro ⟨w,hw⟩ <;> exact ⟨w,hw.symm⟩

end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph
universe ur uv ue um
variable {V : Type uv} [PartialOrder V] {E : Type ue} (G : OrderedGraph V E)

 def inducedGraph (K : Set V) : OrderedGraph K {e : E // G.source e ∈ K ∧ G.target e ∈ K} where
  source e := ⟨G.source e.val,e.property.1⟩
  target e := ⟨G.target e.val,e.property.2⟩
  increasing e := G.increasing e.val

namespace Sheaf
variable {G} {R : Type ur} [CommRing R] (B : Sheaf.{ur,uv,ue,um} (R := R) G)
  (K : Set V)
noncomputable section

 def restrict : Sheaf (R := R) (inducedGraph G K) where
  vertex x := B.vertex x.val
  edge e := B.edge e.val
  lower e := B.lower e.val
  upper e := B.upper e.val

 def restrictAssignment (f : B.Assignment) : (B.restrict K).Assignment := fun x => f x.val

 def extendAssignment (f : (B.restrict K).Assignment) : B.Assignment := by
  classical
  exact fun x => if h : x ∈ K then f ⟨x,h⟩ else 0

@[simp] theorem extendAssignment_mem (f : (B.restrict K).Assignment) (x : K) :
    B.extendAssignment K f x.val = f x := by
  classical
  change (if h : x.val ∈ K then f ⟨x.val,h⟩ else 0) = f x
  split_ifs with h
  · rfl
  · exact (h x.property).elim

 theorem restrict_compatible {Ω : Set V} {f : B.Assignment} (hf : B.CompatibleOn Ω f) :
    (B.restrict K).CompatibleOn (Subtype.val ⁻¹' Ω) (B.restrictAssignment K f) := by
  intro e hs ht
  exact hf e.val hs ht

 theorem restrict_global (f : B.Assignment) (hf : B.IsGlobal f) :
    (B.restrict K).IsGlobal (B.restrictAssignment K f) := by
  intro e _ _
  exact hf e.val (Set.mem_univ _) (Set.mem_univ _)

 theorem restrict_generated (hg : B.Generated) : (B.restrict K).Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hg x.val v
  exact ⟨B.restrictAssignment K f,B.restrict_global K f hf,hfx⟩

 theorem extend_compatible (Ω : Set K) (f : (B.restrict K).Assignment)
    (hf : (B.restrict K).CompatibleOn Ω f) :
    B.CompatibleOn (Subtype.val '' Ω) (B.extendAssignment K f) := by
  intro e hs ht
  obtain ⟨x,hx,hxe⟩ := hs
  obtain ⟨y,hy,hye⟩ := ht
  have hsk : G.source e ∈ K := hxe ▸ x.property
  have htk : G.target e ∈ K := hye ▸ y.property
  let ee : {e : E // G.source e ∈ K ∧ G.target e ∈ K} := ⟨e,hsk,htk⟩
  have hsx : (inducedGraph G K).source ee = x := Subtype.ext hxe.symm
  have hty : (inducedGraph G K).target ee = y := Subtype.ext hye.symm
  have hh := hf ee (hsx ▸ hx) (hty ▸ hy)
  change B.lower e (f ⟨G.source e,hsk⟩) = B.upper e (f ⟨G.target e,htk⟩) at hh
  simpa only [← B.extendAssignment_mem K f] using hh

/-- The induced subgraph may use upper sets which are not ambient upper
sets. All nonzero exiting edges must stay in the subgraph. -/
 theorem restrict_flabby_live [Finite V] (hb : B.Flabby) (live : Set E)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hclosed : ∀ e ∈ live, G.source e ∈ K → G.target e ∈ K) :
    (B.restrict K).Flabby := by
  intro Ω hΩ f hf
  have hc : B.ClosedUnder live (Subtype.val '' Ω) := by
    intro e he hs
    obtain ⟨x,hx,hxe⟩ := hs
    have hsk : G.source e ∈ K := hxe ▸ x.property
    have htk := hclosed e he hsk
    refine ⟨⟨G.target e,htk⟩,?_,rfl⟩
    apply hΩ _ hx
    change x.val ≤ G.target e
    rw [hxe]
    exact (G.increasing e).le
  obtain ⟨g,hg,hgf⟩ := B.extend_closedUnder hb live hdead (Subtype.val '' Ω) hc
    (B.extendAssignment K f) (B.extend_compatible K Ω f hf)
  refine ⟨B.restrictAssignment K g,B.restrict_global K g hg,?_⟩
  intro x hx
  exact (hgf x.val ⟨x,hx,rfl⟩).trans (B.extendAssignment_mem K f x)

 theorem restrict_quotient (α : E → R) (hB : B.UpperQuotient α) :
    (B.restrict K).UpperQuotient (fun e => α e.val) := fun e => hB e.val

end
end Sheaf
end KLInvariance.MomentGraph
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
  change j.vertex x (g x) = f x
  rw [hgf x hx]
  exact (j.vertex x).apply_symm_apply _

 theorem generated (hb : B.Generated) : C.Generated := by
  intro x v
  obtain ⟨f,hf,hfv⟩ := hb x ((j.vertex x).symm v)
  refine ⟨j.assignments f,(j.compatible_iff Set.univ f).mpr hf,?_⟩
  change j.vertex x (f x) = v
  rw [hfv,LinearEquiv.apply_symm_apply]

end Iso

variable (S : Type us) [CommRing S] [Algebra R S]

def baseChangeScalar : S ⊗[R] R ≃ₗ[S] S := AlgebraTensorModule.rid R S S

@[simp] theorem baseChangeScalar_tmul (s : S) (r : R) :
    baseChangeScalar S (s ⊗ₜ[R] r) = s * algebraMap R S r := by
  change r • s = s * algebraMap R S r
  rw [Algebra.smul_def,mul_comm]

 theorem span_map (a : R) :
    (Ideal.span {a}).map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
  rw [Ideal.map_span,Set.image_singleton]

 def baseChangeQuotient (a : R) :
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


 def baseChangePiScalar (p : Prop) :
    S ⊗[R] (PLift p → R) ≃ₗ[S] (PLift p → S) := by
  classical
  exact (TensorProduct.piRight R S S (fun _ : PLift p => R)).trans
    (LinearEquiv.piCongrRight (fun _ => baseChangeScalar S))

 def baseChangePiQuotient (a : R) (p : Prop) :
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

 def quotientPullback (a : R) (p q : Prop) (h : q → p) :
    (PLift p → R) →ₗ[R] (PLift q → R ⧸ Ideal.span {a}) :=
  LinearMap.pi fun t => (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap.comp
    (LinearMap.proj ⟨h t.down⟩)

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
    change baseChangeQuotient S a (s ⊗ₜ Ideal.Quotient.mk _ (v ⟨h hh.down⟩)) = _
    rw [baseChangeQuotient_tmul]
    exact congrArg (Ideal.Quotient.mk _) (baseChangePiScalar_tmul S p s v _).symm
  | add v w hv hw => simp only [map_add,hv,hw]

 def structureBaseChangeIso (G : OrderedGraph V E) (α : E → R) (c : V) :
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


section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf um
variable {R : Type ur} [CommRing R]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  {W : Type uw} [PartialOrder W] {F : Type uf} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 theorem stalkMap_assignment (s : B.Assignment) (x : W) (e : Outgoing (G := H) x) :
    B.stalkMap x (s x) e = B.lower e.val (s (H.source e.val)) := by
  rcases e with ⟨e,he⟩
  subst x
  rfl

 theorem pullback_kernel (x : V) (T : Set F)
    (live : Set F) (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).upwardKernel x {e | f.edge e.val ∈ T} =
      B.upwardKernel (f.vertex x) {e | e.val ∈ T} := by
  classical
  ext v
  change B.vertex (f.vertex x) at v
  let s : B.Assignment := Function.update (fun _ => 0) (f.vertex x) v
  have hs : s (f.vertex x)=v := Function.update_self (β := fun y => B.vertex y) (f.vertex x) v (fun _ => 0)
  have hxs : B.pullAssignment f s x = v := hs
  constructor
  · intro hv e he
    rw [← hs,B.stalkMap_assignment s]
    by_cases hl : e.val ∈ live
    · obtain ⟨a,ha,hax⟩ := hlift e.val hl e.property.symm
      have hh := hv ⟨a,hax⟩ (show f.edge a ∈ T from ha.symm ▸ he)
      rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s)] at hh
      rw [B.pull_lower f] at hh
      exact (congrArg (fun q : F => B.lower q (s (H.source q)) = 0) ha).mp hh
    · exact @Subsingleton.elim _ (hdead e.val hl) _ _
  · intro hv e he
    have hh := hv ⟨f.edge e.val,(f.source e.val).symm.trans (congrArg f.vertex e.property)⟩ he
    rw [← hs,B.stalkMap_assignment s] at hh
    rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s),B.pull_lower f]
    exact hh

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (K : Set V)
noncomputable section

 def structureRestrictIso (c : K) :
    Iso ((structureSheaf G α c.val).restrict K)
      (structureSheaf (inducedGraph G K) (fun e => α e.val) c) where
  vertex _ := LinearEquiv.refl R _
  edge _ := LinearEquiv.refl R _
  lower _ _ := rfl
  upper _ _ := rfl

 theorem structureSheaf_edge_subsingleton (c : V) (e : E) (he : ¬ G.target e ≤ c) :
    Subsingleton ((structureSheaf G α c).edge e) :=
  ⟨fun _ _ => funext (fun h => False.elim (he h.down))⟩

 theorem structureSheaf_lowerIdeal_flabby [Finite V] (hK : IsLowerSet K) (c : K)
    (hf : (structureSheaf G α c.val).Flabby) :
    (structureSheaf (inducedGraph G K) (fun e => α e.val) c).Flabby := by
  apply (structureRestrictIso G α K c).flabby
  apply (structureSheaf G α c.val).restrict_flabby_live K hf {e | G.target e ∈ K}
  · intro e he
    exact structureSheaf_edge_subsingleton G α c.val e (fun hc => he (hK hc c.property))
  · intro e he _
    exact he

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem extend_stalk_graded
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hBmin : B.KernelMinimal x) (hCmin : C.KernelMinimal x) :
    ∃ e : B.vertex x ≃ₗ[A] C.vertex x,
      (∀ n v, v ∈ (B.vertex x).piece n → e v ∈ (C.vertex x).piece n) ∧
      ∀ v, j.boundary (B.forget.stalkMap x v) = C.forget.stalkMap x (e v) := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let g : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hgs : Function.Surjective g.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hfm : LinearMap.ker f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
    intro v hv
    apply (B.kernelMinimal_iff x).mp hBmin
    apply LinearMap.mem_ker.mpr
    apply j.boundary.injective
    rw [map_zero]
    have hh : f.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  have hgm : LinearMap.ker g.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : g.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let F : ModuleData.MinimalCover T := ⟨B.vertex x,hBfree,f,hfs,hfm⟩
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,g,hgs,hgm⟩
  obtain ⟨e,he,hef⟩ := ModuleData.MinimalCover.equiv hneg hzero F D
  refine ⟨e,he,?_⟩
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hef v)).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso
end


section
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  (G : OrderedGraph V E) (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1)
noncomputable section
attribute [local instance] Classical.propDecidable

 def lowerBoundary (c : V) : BoundarySheaf hneg (lowerGraph G (Set.Iic c) (isLowerSet_Iic c))
    (fun e => α e.val) ⟨c,le_rfl⟩ :=
  (exists_boundarySheaf hneg (lowerGraph G (Set.Iic c) (isLowerSet_Iic c)) hscalar
    ⟨c,le_rfl⟩ (fun x => x.property) (fun e => α e.val) (fun e => hα e.val)).some

 def actualBoundaryModels : GradedSheaf.BoundaryModels hneg (G := G) α where
  sheaf c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend
  free c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_free
    (lowerBoundary hneg hscalar G α hα c).free
  quotient c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_quotient α
    (lowerBoundary hneg hscalar G α hα c).quotient
  generated c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_generated
    (lowerBoundary hneg hscalar G α hα c).generated
  flabby c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_flabby
    (lowerBoundary hneg hscalar G α hα c).flabby.flabby
  support c x hx := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_support x hx
  top c := ((lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtendVertex ⟨c,le_rfl⟩).trans
    (ModuleData.equivOfEq (lowerBoundary hneg hscalar G α hα c).top)
  top_graded c n v hv := ModuleData.equivOfEq_graded
    (lowerBoundary hneg hscalar G α hα c).top n _
    ((lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtendVertex_graded ⟨c,le_rfl⟩ n v hv)
  minimal c x hx := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_minimal x
    (fun hxc => (lowerBoundary hneg hscalar G α hα c).minimal ⟨x,hxc⟩
      (fun hh => hx (congrArg Subtype.val hh)))

end
end KLInvariance.MomentGraph
end

end OAI
