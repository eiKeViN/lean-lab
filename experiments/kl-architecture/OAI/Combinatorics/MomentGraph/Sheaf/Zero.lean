import Mathlib
import OAI.Combinatorics.MomentGraph.Sheaf.Isomorphism

/-! Semantic home: OAI.Combinatorics.MomentGraph.Sheaf.Zero. Source spans: MinimalExtensions:6, MinimalExtensions:21, MinimalExtensions:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

 def zero : Sheaf.{u,v,w,z} (R := R) G where
  vertex _ := ModuleCat.of R PUnit.{z+1}
  edge _ := ModuleCat.of R PUnit.{z+1}
  lower _ := 0
  upper _ := 0

 def prod (B C : Sheaf.{u,v,w,z} (R := R) G) : Sheaf.{u,v,w,z} (R := R) G where
  vertex x := ModuleCat.of R (B.vertex x × C.vertex x)
  edge e := ModuleCat.of R (B.edge e × C.edge e)
  lower e := (B.lower e).prodMap (C.lower e)
  upper e := (B.upper e).prodMap (C.upper e)

lemma prod_generated (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Generated) (hC : C.Generated) : (prod B C).Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hB x v.1
  obtain ⟨g,hg,hgx⟩ := hC x v.2
  exact ⟨fun y => (f y,g y),fun e hs ht => Prod.ext (hf e hs ht) (hg e hs ht),Prod.ext hfx hgx⟩

lemma prod_flabby (B C : Sheaf.{u,v,w,z} (R := R) G)
    (hB : B.Flabby) (hC : C.Flabby) : (prod B C).Flabby := by
  intro U hU f hf
  obtain ⟨g,hg,hgf⟩ := hB U hU (fun y => (f y).1) (fun e hs ht => congrArg Prod.fst (hf e hs ht))
  obtain ⟨t,ht,htf⟩ := hC U hU (fun y => (f y).2) (fun e hs htt => congrArg Prod.snd (hf e hs htt))
  exact ⟨fun y => (g y,t y),fun e hs htt => Prod.ext (hg e hs htt) (ht e hs htt),
    fun y hy => Prod.ext (hgf y hy) (htf y hy)⟩

lemma prod_upperQuotient (B C : Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : B.UpperQuotient α) (hC : C.UpperQuotient α) : (prod B C).UpperQuotient α := by
  intro e
  refine ⟨?_,?_⟩
  · intro v
    obtain ⟨b,hb⟩ := (hB e).1 v.1
    obtain ⟨c,hc⟩ := (hC e).1 v.2
    exact ⟨(b,c),Prod.ext hb hc⟩
  · intro v
    constructor
    · intro h
      obtain ⟨b,hb⟩ := (hB e).2 v.1 |>.mp (congrArg Prod.fst h)
      obtain ⟨c,hc⟩ := (hC e).2 v.2 |>.mp (congrArg Prod.snd h)
      exact ⟨(b,c),Prod.ext hb hc⟩
    · rintro ⟨⟨b,c⟩,rfl⟩
      exact Prod.ext ((hB e).2 _ |>.mpr ⟨b,rfl⟩) ((hC e).2 _ |>.mpr ⟨c,rfl⟩)

lemma pi_upperQuotient {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G) (α : E → R)
    (hB : ∀ i, (B i).UpperQuotient α) : (pi B).UpperQuotient α := by
  classical
  intro e
  refine ⟨?_,?_⟩
  · intro v
    choose b hb using fun i => (hB i e).1 (v i)
    exact ⟨b,funext hb⟩
  · intro v
    constructor
    · intro h
      choose b hb using fun i => (hB i e).2 (v i) |>.mp (congrFun h i)
      exact ⟨b,funext hb⟩
    · rintro ⟨b,rfl⟩
      funext i
      exact (hB i e).2 _ |>.mpr ⟨b i,rfl⟩

lemma prod_kernel_iff (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (v : (prod B C).vertex x) :
    v ∈ LinearMap.ker ((prod B C).stalkMap x) ↔
      v.1 ∈ LinearMap.ker (B.stalkMap x) ∧ v.2 ∈ LinearMap.ker (C.stalkMap x) := by
  constructor
  · intro h
    constructor <;> apply LinearMap.mem_ker.mpr <;> funext e
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.fst (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
    · rcases e with ⟨e,he⟩
      subst x
      exact congrArg Prod.snd (congrFun (LinearMap.mem_ker.mp h) ⟨e,rfl⟩)
  · rintro ⟨hB,hC⟩
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact Prod.ext (congrFun (LinearMap.mem_ker.mp hB) ⟨e,rfl⟩)
      (congrFun (LinearMap.mem_ker.mp hC) ⟨e,rfl⟩)

lemma prod_minimal (B C : Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (hB : LinearMap.ker (B.stalkMap x) ≤ I • (⊤ : Submodule R (B.vertex x)))
    (hC : LinearMap.ker (C.stalkMap x) ≤ I • (⊤ : Submodule R (C.vertex x))) :
    LinearMap.ker ((prod B C).stalkMap x) ≤ I • (⊤ : Submodule R ((prod B C).vertex x)) := by
  intro v hv
  obtain ⟨hvB,hvC⟩ := (prod_kernel_iff B C x v).mp hv
  have h (M N : Type z) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
      (f : M →ₗ[R] N) : (I • (⊤ : Submodule R M)).map f ≤ I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hb := h _ _ (LinearMap.inl R (B.vertex x) (C.vertex x)) ⟨v.1,hB hvB,rfl⟩
  have hc := h _ _ (LinearMap.inr R (B.vertex x) (C.vertex x)) ⟨v.2,hC hvC,rfl⟩
  have heq : (v.1,0) + (0,v.2) = v := Prod.ext (add_zero _) (zero_add _)
  have hh := (I • (⊤ : Submodule R ((prod B C).vertex x))).add_mem hb hc
  change (v.1,0) + (0,v.2) ∈ I • (⊤ : Submodule R ((prod B C).vertex x)) at hh
  exact heq ▸ hh

end KLInvariance.MomentGraph.Sheaf
end


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

 def moduleEq {M N : ModuleCat.{um} R} (h : M=N) : M ≃ₗ[R] N := h ▸ LinearEquiv.refl R M

 theorem moduleEq_apply {X : Type*} (M : X → ModuleCat.{um} R) {x y : X} (h : x=y)
    (s : ∀ z, M z) : moduleEq (congrArg M h) (s x) = s y := by subst y; rfl

 def pullback : Sheaf (R := R) G where
  vertex x := B.vertex (f.vertex x)
  edge e := B.edge (f.edge e)
  lower e := (B.lower (f.edge e)).comp (moduleEq (congrArg B.vertex (f.source e))).toLinearMap
  upper e := (B.upper (f.edge e)).comp (moduleEq (congrArg B.vertex (f.target e))).toLinearMap

 def pullAssignment (s : B.Assignment) : (B.pullback f).Assignment := fun x => s (f.vertex x)

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

 def pushAssignment (s : (B.pullback f).Assignment) : B.Assignment := by
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

 theorem pullback_flabby_live [Finite W] (hb : B.Flabby)
    (hi : Function.Injective f.vertex) (live : Set F)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, ∀ x, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) : (B.pullback f).Flabby := by
  intro Ω hΩ s hs
  have hc : B.ClosedUnder live (f.vertex '' Ω) := by
    intro e he hsource
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e he x hxe
    exact ⟨G.target a,hΩ (G.increasing a).le hx,f.target a⟩
  have hcompat : B.CompatibleOn (f.vertex '' Ω) (B.pushAssignment f s) := by
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
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  {B C : Sheaf.{u,v,w,z} (R := R) G} (D : Sheaf.{u,v,w,z} (R := R) G)

noncomputable def addZeroRight (M N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] : M ≃ₗ[R] M × N where
  toFun m := (m,0)
  invFun := Prod.fst
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  map_add' _ _ := Prod.ext rfl (zero_add _).symm
  map_smul' _ _ := Prod.ext rfl (smul_zero _).symm

@[simp] lemma addZeroRight_apply (M N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] (m : M) :
    addZeroRight (R := R) M N m = (m,0) := rfl

noncomputable def OnIso.prodZero {U : Set V} (j : OnIso B C U)
    (hV : ∀ x ∈ U, Subsingleton (D.vertex x))
    (hE : ∀ e, G.target e ∈ U → Subsingleton (D.edge e)) : OnIso B (prod C D) U where
  vertex x hx := by
    letI := hV x hx
    exact (j.vertex x hx).trans (addZeroRight _ _)
  edge e he := by
    letI := hE e he
    exact (j.edge e he).trans (addZeroRight _ _)
  lower e hs ht v := by
    apply Prod.ext
    · exact j.lower e hs ht v
    · exact (D.lower e).map_zero.symm
  upper e ht v := by
    apply Prod.ext
    · exact j.upper e ht v
    · exact (D.upper e).map_zero.symm

lemma pi_subsingleton_vertex {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (x : V) (h : ∀ i, Subsingleton ((B i).vertex x)) : Subsingleton ((pi B).vertex x) := by
  exact ⟨fun f g => funext (fun i => @Subsingleton.elim _ (h i) (f i) (g i))⟩

lemma pi_subsingleton_edge {ι : Type*} (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (e : E) (h : ∀ i, Subsingleton ((B i).edge e)) : Subsingleton ((pi B).edge e) := by
  exact ⟨fun f g => funext (fun i => @Subsingleton.elim _ (h i) (f i) (g i))⟩

end KLInvariance.MomentGraph.Sheaf
end

end OAI
