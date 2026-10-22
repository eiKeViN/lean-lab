import Mathlib
import ForMathlib.Algebra.Module.CoefficientChange.Dual
import ForMathlib.Algebra.Module.Graded.Adjoint
import ForMathlib.Algebra.Module.Graded.Hilbert.Images
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality
import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality. Source spans: Support:24, Support:16, Support:21, Support:7, Support:30, Support:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open Module _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E] [DecidableEq V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)
  [IsNoetherianRing A] [IsDomain A]
  [∀ x, Module.IsTorsionFree A (B.forget.vertex x)]
  (α : E → A) (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (p : B.forget.sections Set.univ ≃ₗ[A] Dual A (B.forget.sections Set.univ))
  (hbalanced : ∀ x m n,
    p (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x m) n =
    p m (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x n))
noncomputable section

 theorem dualToSupport_homogeneous (l : ℤ)
    (hp : ∀ i j (m n : B.sections Set.univ),
      m ∈ (B.sections Set.univ).piece i → n ∈ (B.sections Set.univ).piece j →
      p m n ∈ 𝓐 (i+j-l))
    (x : V) (r : ℤ) (lam : Dual A (B.vertex x))
    (hlam : ∀ j (v : B.vertex x), v ∈ (B.vertex x).piece j → lam v ∈ 𝓐 (j+r)) :
    (IntegralSupport.dualToSupport (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha))
      (Sheaf.labelProduct_ne_zero α hα) p hbalanced x lam).val ∈
        (B.sections Set.univ).piece (r+l) := by
  apply perfect_inverse_of_homogeneous_functional 𝓐 (B.sections Set.univ).piece p l hp r
  intro j n hn
  exact hlam j (n.val x) (hn x (Set.mem_univ x))

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G) {α : E → A}

 theorem UpperQuotient.annihilates (h : B.UpperQuotient α) (e : E) (v : B.edge e) :
    α e • v = 0 := by
  obtain ⟨w,rfl⟩ := (h e).1 v
  rw [← map_smul]
  exact (h e).2 _ |>.mpr ⟨w,rfl⟩

end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)

 theorem upwardSubmodule_saturated (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (a : A) (hreg : ∀ e ∈ F, Function.Injective (fun v : B.edge e.val => a • v)) :
    ∀ v, a • v ∈ B.upwardSubmodule x F → v ∈ B.upwardSubmodule x F := by
  intro v hv e he
  have hz : (B.lowerAt x e).map (a • v) = 0 :=
    (B.lowerAt_map x e (a • v)).trans (hv e he)
  have hz' : (B.lowerAt x e).map v = 0 := by
    apply hreg e he
    change a • (B.lowerAt x e).map v = a • (0 : B.edge e.val)
    simpa only [map_smul,smul_zero] using hz
  exact (B.lowerAt_map x e v).symm.trans hz'


 theorem upper_image_value (α : E → A) (hquot : B.UpperQuotient α)
    (e : E) (F : Set (Sheaf.Outgoing (G := G) (G.target e)))
    [∀ n, Module.Finite k ((B.vertex (G.target e)).piece n)]
    (ha : α e ∈ 𝓐 1)
    (hreg : ∀ f ∈ F, Function.Injective (fun v : B.edge f.val => α e • v))
    (hinj : Function.Injective (fun v : B.vertex (G.target e) => α e • v))
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (term (B.vertex (G.target e)).piece
      ((B.upwardSubmodule (G.target e) F).restrictScalars k) q)) :
    value (B.edge e).piece
        (((B.upwardSubmodule (G.target e) F).map (B.upper e).map).restrictScalars k) q =
      (1-q) * value (B.vertex (G.target e)).piece
        ((B.upwardSubmodule (G.target e) F).restrictScalars k) q := by
  simpa only [zpow_one] using saturated_image_value 𝓐
    (B.vertex (G.target e)).piece (B.edge e).piece
    (B.upwardSubmodule (G.target e) F) (B.upwardKernel_homogeneous (G.target e) F)
    (B.upper e).map (B.upper e).graded (α e) 1 ha (hquot e).2
    (B.upwardSubmodule_saturated (G.target e) F (α e) hreg) hinj hq hs

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

 def coefficientChange (S : GradedSheaf (𝓐 := 𝓐) G) : GradedSheaf (𝓐 := 𝓑) G where
  vertex x := ModuleData.change e he (S.vertex x)
  edge f := ModuleData.change e he (S.edge f)
  lower f := ModuleData.changeHom e he (S.lower f)
  upper f := ModuleData.changeHom e he (S.upper f)

 def Hom.coefficientChange {S T : GradedSheaf (𝓐 := 𝓐) G} (g : Hom S T) :
    Hom (coefficientChange e he S) (coefficientChange e he T) where
  vertex x := ModuleData.changeHom e he (g.vertex x)
  edge f := ModuleData.changeHom e he (g.edge f)
  lower f m := CoefficientChange.ext (g.lower f m.val)
  upper f m := CoefficientChange.ext (g.upper f m.val)

 theorem coefficientChange_free (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.FreeStalks) :
    (coefficientChange e he S).FreeStalks := by
  intro x
  let := hS x
  exact ModuleData.change_free e he (S.vertex x)

 theorem coefficientChange_upperQuotient (S : GradedSheaf (𝓐 := 𝓐) G)
    (α : E → A) (hS : S.UpperQuotient α) :
    (coefficientChange e he S).UpperQuotient (fun f => e (α f)) := by
  intro f
  constructor
  · exact CoefficientChange.map_surjective e _ (hS f).1
  · intro m
    constructor
    · intro hm
      have hz : (S.upper f).map m.val=0 := congrArg CoefficientChange.val hm
      obtain ⟨n,hn⟩ := (hS f).2 m.val |>.mp hz
      refine ⟨CoefficientChange.mk n,CoefficientChange.ext ?_⟩
      change m.val=e.symm (e (α f)) • n
      simpa only [e.symm_apply_apply] using hn
    · rintro ⟨n,rfl⟩
      apply CoefficientChange.ext
      change (S.upper f).map (e.symm (e (α f)) • n.val)=0
      rw [e.symm_apply_apply]
      exact ((hS f).2 _).mpr ⟨n.val,rfl⟩

 theorem coefficientChange_flabby (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Flabby) :
    (coefficientChange e he S).forget.Flabby := by
  intro U hU f hf
  have hf' : S.forget.CompatibleOn U (fun x => (f x).val) := fun q hs ht =>
    congrArg CoefficientChange.val (hf q hs ht)
  obtain ⟨g,hg,hgf⟩ := hS U hU (fun x => (f x).val) hf'
  refine ⟨fun x => CoefficientChange.mk (g x),?_,?_⟩
  · intro q hs ht
    exact CoefficientChange.ext (hg q hs ht)
  · intro x hx
    exact CoefficientChange.ext (hgf x hx)

 theorem coefficientChange_generated (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Generated) :
    (coefficientChange e he S).forget.Generated := by
  intro x m
  obtain ⟨g,hg,hgx⟩ := hS x m.val
  refine ⟨fun x => CoefficientChange.mk (g x),?_,CoefficientChange.ext hgx⟩
  intro q hs ht
  exact CoefficientChange.ext (hg q hs ht)

 def coefficientChangeSections (S : GradedSheaf (𝓐 := 𝓐) G) (U : Set V) :
    CoefficientChange e (S.forget.sections U) ≃ₗ[B] (coefficientChange e he S).forget.sections U where
  toFun m := ⟨fun x => CoefficientChange.mk (m.val.val x),fun q hs ht =>
    CoefficientChange.ext (m.val.property q hs ht)⟩
  invFun m := CoefficientChange.mk ⟨fun x => (m.val x).val,fun q hs ht =>
    congrArg CoefficientChange.val (m.property q hs ht)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 structure PerfectPairing (S : GradedSheaf (𝓐 := 𝓐) G) (d : ℤ) where
  pairing : S.forget.sections Set.univ ≃ₗ[A] Dual A (S.forget.sections Set.univ)
  homogeneous : ∀ i j (m n : S.forget.sections Set.univ),
    (∀ x, m.val x∈(S.vertex x).piece i) → (∀ x, n.val x∈(S.vertex x).piece j) →
    pairing m n∈𝓐 (i+j-d)
  left_orthogonal : ∀ (x : V) (m n : S.forget.sections Set.univ),
    (∀ y, y≠x → m.val y=0) → n.val x=0 → pairing m n=0
  right_orthogonal : ∀ (x : V) (m n : S.forget.sections Set.univ),
    m.val x=0 → (∀ y, y≠x → n.val y=0) → pairing m n=0

 def PerfectPairing.pullback {S T : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : PerfectPairing T d) (j : Iso S T) : PerfectPairing S d where
  pairing := (j.toIso.sections Set.univ).trans
    (p.pairing.trans (j.toIso.sections Set.univ).dualMap)
  homogeneous i q m n hm hn := p.homogeneous i q _ _
    (fun x => j.vertex_graded x i _ (hm x)) (fun x => j.vertex_graded x q _ (hn x))
  left_orthogonal x m n hm hn := by
    apply p.left_orthogonal x
    · intro y hy
      change j.vertex y (m.val y)=0
      rw [hm y hy,map_zero]
    · change j.vertex x (n.val x)=0
      rw [hn,map_zero]
  right_orthogonal x m n hm hn := by
    apply p.right_orthogonal x
    · change j.vertex x (m.val x)=0
      rw [hm,map_zero]
    · intro y hy
      change j.vertex y (n.val y)=0
      rw [hn y hy,map_zero]

 variable {B : Type ua} [CommRing B] [Algebra k B] {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)

 def PerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : PerfectPairing S d) : PerfectPairing (coefficientChange e he S) d where
  pairing := (coefficientChangeSections e he S Set.univ).symm.trans
    ((CoefficientChange.pairingEquiv e p.pairing).trans
      (coefficientChangeSections e he S Set.univ).symm.dualMap)
  homogeneous i j m n hm hn := by
    apply (he (i+j-d) _).mp
    exact p.homogeneous i j _ _
      (fun x => (ModuleData.mem_changePiece e (S.vertex x) i (m.val x)).mp (hm x))
      (fun x => (ModuleData.mem_changePiece e (S.vertex x) j (n.val x)).mp (hn x))
  left_orthogonal x m n hm hn := by
    change e (p.pairing _ _)=0
    apply (congrArg e ?_).trans (map_zero e)
    apply p.left_orthogonal x
    · intro y hy
      exact congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hm y hy)
    · exact congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) hn
  right_orthogonal x m n hm hn := by
    change e (p.pairing _ _)=0
    apply (congrArg e ?_).trans (map_zero e)
    apply p.right_orthogonal x
    · exact congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) hm
    · intro y hy
      exact congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hn y hy)

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem SplitIn.flabby (s : SplitIn B C) (hC : C.forget.Flabby) : B.forget.Flabby := by
  intro Ω hΩ f hf
  obtain ⟨g,hg,hgf⟩ := hC Ω hΩ (s.inclusion.assignmentMap f)
    (s.inclusion.assignmentMap_compatible Ω f hf)
  refine ⟨s.projection.assignmentMap g,
    s.projection.assignmentMap_compatible Set.univ g hg,?_⟩
  intro x hx
  change (s.projection.vertex x).map (g x)=f x
  rw [hgf x hx]
  exact s.vertex_split x (f x)

 theorem SplitIn.generated (s : SplitIn B C) (hC : C.forget.Generated) : B.forget.Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hC x ((s.inclusion.vertex x).map v)
  refine ⟨s.projection.assignmentMap f,
    s.projection.assignmentMap_compatible Set.univ f hf,?_⟩
  change (s.projection.vertex x).map (f x)=v
  rw [hfx]
  exact s.vertex_split x v

 theorem SplitIn.upperQuotient (s : SplitIn B C) {α : E → A}
    (hC : C.UpperQuotient α) : B.UpperQuotient α := by
  intro e
  constructor
  · intro v
    obtain ⟨c,hc⟩ := (hC e).1 ((s.inclusion.edge e).map v)
    refine ⟨(s.projection.vertex (G.target e)).map c,?_⟩
    rw [← s.projection.upper,hc]
    exact s.edge_split e v
  · intro v
    constructor
    · intro hv
      have hz : (C.upper e).map ((s.inclusion.vertex _).map v)=0 := by
        rw [← s.inclusion.upper,hv]
        exact map_zero _
      obtain ⟨c,hc⟩ := (hC e).2 _ |>.mp hz
      refine ⟨(s.projection.vertex _).map c,?_⟩
      have h := congrArg (s.projection.vertex _).map hc
      rw [s.vertex_split,map_smul] at h
      exact h
    · rintro ⟨w,rfl⟩
      have hz := ((hC e).2 (α e • (s.inclusion.vertex _).map w)).mpr
        ⟨(s.inclusion.vertex _).map w,rfl⟩
      have he : (s.inclusion.edge e).map ((B.upper e).map (α e • w))=0 := by
        rw [s.inclusion.upper,map_smul]
        exact hz
      have h := congrArg (s.projection.edge e).map he
      rw [s.edge_split,map_zero] at h
      exact h

 theorem SplitIn.vertex_projective (s : SplitIn B C) (x : V)
    [Module.Projective A (C.vertex x)] : Module.Projective A (B.vertex x) := by
  apply Module.Projective.of_split (s.inclusion.vertex x).map (s.projection.vertex x).map
  apply LinearMap.ext
  exact s.vertex_split x

 theorem SplitIn.vertex_free
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    [IsDomain A] [IsNoetherianRing A]
    (hneg : ∀ n < 0, 𝓐 n=⊥)
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c=a)
    (s : SplitIn B C) (x : V) [Module.Projective A (C.vertex x)] :
    Module.Free A (B.vertex x) := by
  let D := B.vertex x
  let : Module.Projective A D := s.vertex_projective x
  obtain ⟨ι,_,bs,_⟩ := exists_homogeneous_basis_connected 𝓐 D.piece hneg hzero 0 D.nonneg
  exact Module.Free.of_basis bs

end
end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
