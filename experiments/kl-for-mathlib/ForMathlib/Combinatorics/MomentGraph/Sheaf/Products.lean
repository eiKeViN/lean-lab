import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Products. Source spans: MinimalExtensions:6, MinimalExtensions:7.
See migration.json and MIGRATION.md for exact provenance.
Zero and binary product sheaves, finite-product quotient/minimality properties and adjoining a zero summand. -/

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
