import Mathlib
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties. Source spans: GradedSheaves:6.
See migration.json and MIGRATION.md for exact provenance.
Free stalks, upper-quotient and minimal-kernel conditions and their preservation by reindexing and bottom attachment. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

 def FreeStalks (B : GradedSheaf (𝓐 := 𝓐) G) : Prop := ∀ x, Module.Free A (B.vertex x)

/-- The genuine upper-end quotient rule, expressed without choosing a quotient
presentation of the edge object. -/
 def UpperQuotient (B : GradedSheaf (𝓐 := 𝓐) G) (α : E → A) : Prop :=
  ∀ e, Function.Surjective (B.upper e).map ∧
    ∀ v, (B.upper e).map v = 0 ↔ ∃ w, v = α e • w

/-- Minimality of the full outgoing boundary cover. The assignment formulation
avoids dependent casts and is equivalent to the usual kernel containment. -/
 def KernelMinimal (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) : Prop :=
  ∀ f : B.forget.Assignment,
    (∀ e, G.source e = x → B.forget.lower e (f (G.source e)) = 0) →
    f x ∈ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x))

 theorem kernelMinimal_iff (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    B.KernelMinimal x ↔ LinearMap.ker (B.forget.stalkMap x) ≤
      positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
  classical
  constructor
  · intro h v hv
    let f : B.forget.Assignment := Function.update 0 x v
    have hf : f x = v := by simp [f]
    rw [← hf]
    apply h f
    intro e he
    have hh := congrFun (LinearMap.mem_ker.mp hv) (⟨e,he⟩ : Sheaf.Outgoing x)
    subst x
    simpa [Sheaf.stalkMap,f] using hh
  · intro h f hf
    apply h
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact hf e rfl

 theorem reindex_freeStalks (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (h : B.FreeStalks) : (B.reindex e).FreeStalks := fun x => h (e.vertex x)

 theorem reindex_upperQuotient (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    {α : F → A} (h : B.UpperQuotient α) : (B.reindex e).UpperQuotient (α ∘ e.edge) := by
  intro a
  let j := ModuleData.Hom.ofEq (congrArg B.vertex (e.target a))
  have hj := ModuleData.Hom.ofEq_bijective (congrArg B.vertex (e.target a))
  refine ⟨(h (e.edge a)).1.comp hj.2,?_⟩
  intro v
  change (B.upper (e.edge a)).map (j.map v) = 0 ↔ ∃ w, v = α (e.edge a) • w
  rw [(h (e.edge a)).2]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨z,rfl⟩ := hj.2 w
    exact ⟨z,hj.1 (hw.trans (map_smul j.map (α (e.edge a)) z).symm)⟩
  · rintro ⟨w,rfl⟩
    exact ⟨j.map w,map_smul _ _ _⟩

 theorem reindex_kernelMinimal (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (x : V) (h : B.KernelMinimal (e.vertex x)) : (B.reindex e).KernelMinimal x := by
  intro f hf
  have hh : ∀ a, H.source a = e.vertex x →
      B.forget.lower a (B.unreindexAssignment e f (H.source a)) = 0 := by
    intro a ha
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    have hs : G.source a = x := e.vertex.injective ((e.source a).trans ha)
    have hv := hf a hs
    rw [← B.reindex_unreindexAssignment e f] at hv
    exact (B.reindex_lower e a (B.unreindexAssignment e f)).symm.trans hv
  have hm := h (B.unreindexAssignment e f) hh
  have he := congrFun (B.reindex_unreindexAssignment e f) x
  exact he ▸ hm

variable {D : Type um} [Fintype V] [Fintype D] [IsNoetherianRing A]
  (B : GradedSheaf (𝓐 := 𝓐) G) (τ : D → V) (α : D → A)
  (hα : ∀ d, α d ∈ 𝓐 1) (C : ModuleData.MinimalCover (B.attachImage τ α hα))

 theorem extendBottom_freeStalks (hb : B.FreeStalks) :
    (B.extendBottom τ α hα C).FreeStalks := by
  intro x
  induction x using WithBot.recBotCoe with
  | bot => exact C.free
  | coe x => exact hb x

 theorem extendBottom_upperQuotient {αold : E → A} (hb : B.UpperQuotient αold) :
    (B.extendBottom τ α hα C).UpperQuotient (Sum.elim αold α) := by
  intro e
  cases e with
  | inl e => exact hb e
  | inr d =>
    let S := LinearMap.range (LinearMap.lsmul A (B.vertex (τ d)) (α d))
    refine ⟨S.mkQ_surjective,?_⟩
    intro v
    change S.mkQ v = 0 ↔ ∃ w, v = α d • w
    refine (Submodule.Quotient.mk_eq_zero S).trans ?_
    change (∃ w, α d • w = v) ↔ ∃ w, v = α d • w
    exact ⟨fun ⟨w,hw⟩ => ⟨w,hw.symm⟩,fun ⟨w,hw⟩ => ⟨w,hw.symm⟩⟩

 theorem extendBottom_kernelMinimal_bot : (B.extendBottom τ α hα C).KernelMinimal ⊥ := by
  intro f hf
  apply C.minimal
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  funext d
  exact hf (Sum.inr d) rfl

 theorem extendBottom_kernelMinimal_coe (x : V) (h : B.KernelMinimal x) :
    (B.extendBottom τ α hα C).KernelMinimal (x : WithBot V) := by
  intro f hf
  apply h (fun y => f (y : WithBot V))
  intro a ha
  exact hf (Sum.inl a) (congrArg (fun y : V => (y : WithBot V)) ha)

end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
