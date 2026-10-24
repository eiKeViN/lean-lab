module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback. Source spans: MinimalExtensions:21, MinimalExtensions:22.
See migration.json and MIGRATION.md for exact provenance.
Graph maps and pullback sheaves, assignments and live-edge flabbiness, quotient and upward-kernel transport. -/

namespace OAI

section
namespace KLInvariance.MomentGraph
universe ur uv ue uw uf um
variable {V : Type uv} [PartialOrder V] {E : Type ue}
  {W : Type uw} [PartialOrder W] {F : Type uf}

structure GraphMap (G : OrderedGraph V E) (H : OrderedGraph W F) where
  vertex : V → W
  edge : E → F
  source : ∀ e, vertex (G.source e) = H.source (edge e)
  target : ∀ e, vertex (G.target e) = H.target (edge e)

namespace Sheaf
variable {R : Type ur} [CommRing R] {G : OrderedGraph V E} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 @[expose] def moduleEq {M N : ModuleCat.{um} R} (h : M=N) : M ≃ₗ[R] N := h ▸ LinearEquiv.refl R M

 theorem moduleEq_apply {X : Type*} (M : X → ModuleCat.{um} R) {x y : X} (h : x=y)
    (s : ∀ z, M z) : moduleEq (congrArg M h) (s x) = s y := by subst y; rfl

 @[expose] def pullback : Sheaf (R := R) G where
  vertex x := B.vertex (f.vertex x)
  edge e := B.edge (f.edge e)
  lower e := (B.lower (f.edge e)).comp (moduleEq (congrArg B.vertex (f.source e))).toLinearMap
  upper e := (B.upper (f.edge e)).comp (moduleEq (congrArg B.vertex (f.target e))).toLinearMap

 @[expose] def pullAssignment (s : B.Assignment) : (B.pullback f).Assignment := fun x => s (f.vertex x)

@[simp] theorem pull_lower (e : E) (s : B.Assignment) :
    (B.pullback f).lower e (B.pullAssignment f s (G.source e)) =
      B.lower (f.edge e) (s (H.source (f.edge e))) := by
  exact congrArg (B.lower (f.edge e)) (moduleEq_apply B.vertex (f.source e) s)

@[simp] theorem pull_upper (e : E) (s : B.Assignment) :
    (B.pullback f).upper e (B.pullAssignment f s (G.target e)) =
      B.upper (f.edge e) (s (H.target (f.edge e))) := by
  exact congrArg (B.upper (f.edge e)) (moduleEq_apply B.vertex (f.target e) s)

 theorem pull_global (s : B.Assignment) (hs : B.IsGlobal s) :
    (B.pullback f).IsGlobal (B.pullAssignment f s) := by
  intro e _ _
  rw [pull_lower,pull_upper]
  exact hs (f.edge e) (Set.mem_univ _) (Set.mem_univ _)

 theorem pullback_generated (hg : B.Generated) : (B.pullback f).Generated := by
  intro x v
  obtain ⟨s,hs,hx⟩ := hg (f.vertex x) v
  exact ⟨B.pullAssignment f s,B.pull_global f s hs,hx⟩

 @[expose] def pushAssignment (s : (B.pullback f).Assignment) : B.Assignment := by
  classical
  exact fun y => if h : ∃ x, f.vertex x=y then
    moduleEq (congrArg B.vertex h.choose_spec) (s h.choose) else 0

 theorem pull_push (hi : Function.Injective f.vertex) (s : (B.pullback f).Assignment) :
    B.pullAssignment f (B.pushAssignment f s) = s := by
  classical
  change (∀ x, B.vertex (f.vertex x)) at s
  funext x
  have h : ∃ z, f.vertex z=f.vertex x := ⟨x,rfl⟩
  change @Eq (B.vertex (f.vertex x))
    (if hh : ∃ z, f.vertex z=f.vertex x then
      moduleEq (congrArg B.vertex hh.choose_spec) (s hh.choose) else 0) (s x)
  rw [dite_eq_left h]
  have hx : h.choose=x := hi h.choose_spec
  exact moduleEq_apply (fun z => B.vertex (f.vertex z)) hx s

/-- An upper vertex set maps to a live-edge-closed set when every live edge
out of its image lifts. Injectivity and sheaf flabbiness are not needed for this
geometric closure argument. -/
theorem image_closedUnder_live (live : Set F)
    (hlift : ∀ e ∈ live, ∀ x, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) (Ω : Set V) (hΩ : IsUpperSet Ω) :
    B.ClosedUnder live (f.vertex '' Ω) := by
  intro e he hsource
  obtain ⟨x,hx,hxe⟩ := hsource
  obtain ⟨a,rfl,rfl⟩ := hlift e he x hxe
  exact ⟨G.target a,hΩ (G.increasing a).le hx,f.target a⟩

/-- Pushing a compatible partial section along an injective graph map
preserves compatibility on its image when live edges lift and dead edge modules
are subsingletons. No extension or finiteness assumption is needed. -/
theorem push_compatible_live (hi : Function.Injective f.vertex) (live : Set F)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, ∀ x, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) (Ω : Set V)
    (s : (B.pullback f).Assignment) (hs : (B.pullback f).CompatibleOn Ω s) :
    B.CompatibleOn (f.vertex '' Ω) (B.pushAssignment f s) := by
  classical
  intro e hsource htarget
  by_cases he : e ∈ live
  · obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e he x hxe
    obtain ⟨y,hy,hye⟩ := htarget
    have hya : y=G.target a := hi (hye.trans (f.target a).symm)
    subst y
    have hh := hs a hx hy
    rw [← B.pull_push f hi s] at hh
    change (B.pullback f).lower a (B.pullAssignment f (B.pushAssignment f s) (G.source a)) =
      (B.pullback f).upper a (B.pullAssignment f (B.pushAssignment f s) (G.target a)) at hh
    rw [pull_lower,pull_upper] at hh
    exact hh
  · exact @Subsingleton.elim _ (hdead e he) _ _

 theorem pullback_flabby_live [Finite W] (hb : B.Flabby)
    (hi : Function.Injective f.vertex) (live : Set F)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, ∀ x, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) : (B.pullback f).Flabby := by
  intro Ω hΩ s hs
  have hc := B.image_closedUnder_live f live hlift Ω hΩ
  have hcompat := B.push_compatible_live f hi live hdead hlift Ω s hs
  obtain ⟨t,ht,hts⟩ := B.extend_closedUnder hb live hdead (f.vertex '' Ω) hc
    (B.pushAssignment f s) hcompat
  refine ⟨B.pullAssignment f t,B.pull_global f t ht,?_⟩
  intro x hx
  change t (f.vertex x) = s x
  rw [hts (f.vertex x) ⟨x,hx,rfl⟩]
  exact congrFun (B.pull_push f hi s) x

 theorem pullback_quotient (α : F → R) (hq : B.UpperQuotient α) :
    (B.pullback f).UpperQuotient (fun e => α (f.edge e)) := by
  intro e
  let j := moduleEq (congrArg B.vertex (f.target e))
  refine ⟨?_,?_⟩
  · exact (hq (f.edge e)).1.comp j.surjective
  · intro v
    change B.upper (f.edge e) (j v) = 0 ↔ _
    rw [(hq (f.edge e)).2]
    constructor
    · rintro ⟨w,hw⟩
      refine ⟨j.symm w,?_⟩
      apply j.injective
      change j v = j (α (f.edge e) • j.symm w)
      rw [map_smul,LinearEquiv.apply_symm_apply]
      exact hw
    · rintro ⟨w,rfl⟩
      exact ⟨j w,j.map_smul _ _⟩

end
end Sheaf
end KLInvariance.MomentGraph
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

/-- An ambient upward-kernel condition always pulls back along a graph map.
The reverse direction is the one that needs live-edge lifting; this inclusion
uses only the commuting lower maps. -/
theorem upwardKernel_le_pullback (x : V) (T : Set F) :
    B.upwardKernel (f.vertex x) {e | e.val ∈ T} ≤
      (B.pullback f).upwardKernel x {e | f.edge e.val ∈ T} := by
  intro v hv
  classical
  let s : B.Assignment := Function.update (fun _ => 0) (f.vertex x) v
  have hs : s (f.vertex x)=v := Function.update_self (β := fun y => B.vertex y) (f.vertex x) v (fun _ => 0)
  have hxs : B.pullAssignment f s x = v := hs
  intro e he
  have hh := hv ⟨f.edge e.val,(f.source e.val).symm.trans (congrArg f.vertex e.property)⟩ he
  rw [← hs,B.stalkMap_assignment s] at hh
  rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s),B.pull_lower f]
  exact hh

/-- Lifting live outgoing edges and killing the other edge modules reflect
upward-kernel conditions back to the ambient graph. The statement isolates the
hypotheses absent from unconditional kernel pullback. -/
theorem pullbackKernel_le_of_live (x : V) (T : Set F)
    (live : Set F) (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).upwardKernel x {e | f.edge e.val ∈ T} ≤
      B.upwardKernel (f.vertex x) {e | e.val ∈ T} := by
  intro v hv
  classical
  let s : B.Assignment := Function.update (fun _ => 0) (f.vertex x) v
  have hs : s (f.vertex x)=v := Function.update_self (β := fun y => B.vertex y) (f.vertex x) v (fun _ => 0)
  have hxs : B.pullAssignment f s x = v := hs
  intro e he
  rw [← hs,B.stalkMap_assignment s]
  by_cases hl : e.val ∈ live
  · obtain ⟨a,ha,hax⟩ := hlift e.val hl e.property.symm
    have hh := hv ⟨a,hax⟩ (show f.edge a ∈ T from ha.symm ▸ he)
    rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s)] at hh
    rw [B.pull_lower f] at hh
    exact (congrArg (fun q : F => B.lower q (s (H.source q)) = 0) ha).mp hh
  · exact @Subsingleton.elim _ (hdead e.val hl) _ _

 theorem pullback_kernel (x : V) (T : Set F)
    (live : Set F) (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).upwardKernel x {e | f.edge e.val ∈ T} =
      B.upwardKernel (f.vertex x) {e | e.val ∈ T} := by
  exact le_antisymm (B.pullbackKernel_le_of_live f x T live hdead hlift)
    (B.upwardKernel_le_pullback f x T)

end
end KLInvariance.MomentGraph.Sheaf
end

end OAI
