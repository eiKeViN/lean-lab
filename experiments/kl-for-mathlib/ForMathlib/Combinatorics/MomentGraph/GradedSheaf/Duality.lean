module
public import Mathlib
public import ForMathlib.Algebra.Module.CoefficientChange.Dual
public import ForMathlib.Algebra.Module.Graded.Adjoint
public import ForMathlib.Algebra.Module.Graded.Hilbert.Images
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality
public import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic

public section

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

/-- A homogeneous stalk functional gives a supported section in the complementary degree.
This formulation uses only the pairing characterization of single-support duality. -/
theorem singleSupportEquivDual_symm_homogeneous (hg : B.forget.Generated) (l : ℤ)
    (hp : ∀ i j (m n : B.sections Set.univ),
      m ∈ (B.sections Set.univ).piece i → n ∈ (B.sections Set.univ).piece j →
      p m n ∈ 𝓐 (i+j-l))
    (x : V) (r : ℤ) (lam : Dual A (B.vertex x))
    (hlam : ∀ j (v : B.vertex x), v ∈ (B.vertex x).piece j → lam v ∈ 𝓐 (j+r)) :
    ((B.forget.singleSupportEquivDual α hα ha p hbalanced hg x).symm lam).val ∈
      (B.sections Set.univ).piece (r+l) := by
  have he : ((B.forget.singleSupportEquivDual α hα ha p hbalanced hg x).symm lam).val =
      p.symm ((IntegralSupport.projection (B.forget.sections Set.univ) x).dualMap lam) := by
    apply p.injective
    apply LinearMap.ext
    intro n
    exact (B.forget.singleSupportEquivDual_symm_pairing α hα ha p hbalanced hg x lam n).trans
      (congrArg (fun f : Dual A (B.forget.sections Set.univ) => f n)
        (p.apply_symm_apply ((IntegralSupport.projection (B.forget.sections Set.univ) x).dualMap lam))).symm
  rw [he]
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

 @[expose] def coefficientChange (S : GradedSheaf (𝓐 := 𝓐) G) : GradedSheaf (𝓐 := 𝓑) G where
  vertex x := ModuleData.change e he (S.vertex x)
  edge f := ModuleData.change e he (S.edge f)
  lower f := ModuleData.changeHom e he (S.lower f)
  upper f := ModuleData.changeHom e he (S.upper f)

 /-- Coefficient transport preserves the lower edge map on underlying vectors. -/
 @[simp] theorem coefficientChange_lower_val (S : GradedSheaf (𝓐 := 𝓐) G)
     (f : E) (m : (coefficientChange e he S).vertex (G.source f)) :
     ((coefficientChange e he S).forget.lower f m).val = S.forget.lower f m.val := by
   exact ModuleData.val_changeHom e he (S.lower f) m

 /-- Coefficient transport preserves the upper edge map on underlying vectors. -/
 @[simp] theorem coefficientChange_upper_val (S : GradedSheaf (𝓐 := 𝓐) G)
     (f : E) (m : (coefficientChange e he S).vertex (G.target f)) :
     ((coefficientChange e he S).forget.upper f m).val = S.forget.upper f m.val := by
   exact ModuleData.val_changeHom e he (S.upper f) m

 /-- Compatibility is invariant under pointwise coefficient transport. -/
 theorem coefficientChange_compatibleOn_iff (S : GradedSheaf (𝓐 := 𝓐) G)
     (U : Set V) (a : (coefficientChange e he S).forget.Assignment) :
     (coefficientChange e he S).forget.CompatibleOn U a ↔
       S.forget.CompatibleOn U (fun x => (a x).val) := by
   constructor
   · intro ha f hs ht
     exact (coefficientChange_lower_val e he S f _).symm.trans
       ((congrArg CoefficientChange.val (ha f hs ht)).trans
         (coefficientChange_upper_val e he S f _))
   · intro ha f hs ht
     apply CoefficientChange.ext
     exact (coefficientChange_lower_val e he S f _).trans
       ((ha f hs ht).trans (coefficientChange_upper_val e he S f _).symm)

 @[expose] def Hom.coefficientChange {S T : GradedSheaf (𝓐 := 𝓐) G} (g : Hom S T) :
    Hom (coefficientChange e he S) (coefficientChange e he T) where
  vertex x := ModuleData.changeHom e he (g.vertex x)
  edge f := ModuleData.changeHom e he (g.edge f)
  lower f m := by
    apply CoefficientChange.ext
    calc
      _ = (g.edge f).map ((S.lower f).map m.val) :=
        (ModuleData.val_changeHom e he (g.edge f) _).trans
          (congrArg (g.edge f).map (coefficientChange_lower_val e he S f m))
      _ = (T.lower f).map ((g.vertex (G.source f)).map m.val) := g.lower f m.val
      _ = _ := ((coefficientChange_lower_val e he T f _).trans
        (congrArg (T.lower f).map (ModuleData.val_changeHom e he (g.vertex _) m))).symm
  upper f m := by
    apply CoefficientChange.ext
    calc
      _ = (g.edge f).map ((S.upper f).map m.val) :=
        (ModuleData.val_changeHom e he (g.edge f) _).trans
          (congrArg (g.edge f).map (coefficientChange_upper_val e he S f m))
      _ = (T.upper f).map ((g.vertex (G.target f)).map m.val) := g.upper f m.val
      _ = _ := ((coefficientChange_upper_val e he T f _).trans
        (congrArg (T.upper f).map (ModuleData.val_changeHom e he (g.vertex _) m))).symm

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
      have hz : (S.upper f).map m.val=0 :=
        (coefficientChange_upper_val e he S f m).symm.trans
          ((congrArg CoefficientChange.val hm).trans (CoefficientChange.val_zero e _))
      obtain ⟨n,hn⟩ := (hS f).2 m.val |>.mp hz
      refine ⟨CoefficientChange.mk n,CoefficientChange.ext ?_⟩
      calc
        m.val = α f • n := hn
        _ = e.symm (e (α f)) • n := congrArg (fun a : A => a • n) (e.symm_apply_apply _).symm
        _ = _ := (CoefficientChange.val_smul e (S.vertex (G.target f)) (e (α f)) (CoefficientChange.mk n)).symm
    · rintro ⟨n,rfl⟩
      apply CoefficientChange.ext
      calc
        _ = (S.upper f).map ((e (α f) • n).val) := coefficientChange_upper_val e he S f _
        _ = (S.upper f).map (α f • n.val) := congrArg (S.upper f).map
          ((CoefficientChange.val_smul e (S.vertex (G.target f)) (e (α f)) n).trans
            (congrArg (fun a : A => a • n.val) (e.symm_apply_apply _)))
        _ = 0 := ((hS f).2 _).mpr ⟨n.val,rfl⟩
        _ = _ := (CoefficientChange.val_zero e _).symm

 theorem coefficientChange_flabby (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Flabby) :
    (coefficientChange e he S).forget.Flabby := by
  intro U hU f hf
  have hf' := (coefficientChange_compatibleOn_iff e he S U f).mp hf
  obtain ⟨g,hg,hgf⟩ := hS U hU (fun x => (f x).val) hf'
  refine ⟨fun x => CoefficientChange.mk (g x),?_,?_⟩
  · exact (coefficientChange_compatibleOn_iff e he S Set.univ _).mpr hg
  · intro x hx
    exact CoefficientChange.ext (hgf x hx)

 theorem coefficientChange_generated (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Generated) :
    (coefficientChange e he S).forget.Generated := by
  intro x m
  obtain ⟨g,hg,hgx⟩ := hS x m.val
  refine ⟨fun x => CoefficientChange.mk (g x),?_,CoefficientChange.ext hgx⟩
  exact (coefficientChange_compatibleOn_iff e he S Set.univ _).mpr hg

 @[expose] def coefficientChangeSections (S : GradedSheaf (𝓐 := 𝓐) G) (U : Set V) :
    CoefficientChange e (S.forget.sections U) ≃ₗ[B] (coefficientChange e he S).forget.sections U where
  toFun m := ⟨fun x => CoefficientChange.mk (m.val.val x),
    (coefficientChange_compatibleOn_iff e he S U (fun x => CoefficientChange.mk (m.val.val x))).mpr m.val.property⟩
  invFun m := CoefficientChange.mk ⟨fun x => (m.val x).val,
    (coefficientChange_compatibleOn_iff e he S U m.val).mp m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 /-- The inverse section transport preserves each underlying stalk value. -/
 @[simp] theorem coefficientChangeSections_symm_val_apply
     (S : GradedSheaf (𝓐 := 𝓐) G) (U : Set V)
     (m : (coefficientChange e he S).forget.sections U) (x : V) :
     ((coefficientChangeSections e he S U).symm m).val.val x = (m.val x).val := by rfl

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

 @[expose] def PerfectPairing.pullback {S T : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
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

 @[expose] def PerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : PerfectPairing S d) : PerfectPairing (coefficientChange e he S) d where
  pairing := (coefficientChangeSections e he S Set.univ).symm.trans
    ((CoefficientChange.pairingEquiv e p.pairing).trans
      (coefficientChangeSections e he S Set.univ).symm.dualMap)
  homogeneous i j m n hm hn := by
    change CoefficientChange.pairingEquiv e p.pairing
      ((coefficientChangeSections e he S Set.univ).symm m)
      ((coefficientChangeSections e he S Set.univ).symm n) ∈ _
    rw [CoefficientChange.pairingEquiv_apply]
    apply (he (i+j-d) _).mp
    apply p.homogeneous i j
    · intro x
      rw [coefficientChangeSections_symm_val_apply]
      exact (ModuleData.mem_changePiece e (S.vertex x) i (m.val x)).mp (hm x)
    · intro x
      rw [coefficientChangeSections_symm_val_apply]
      exact (ModuleData.mem_changePiece e (S.vertex x) j (n.val x)).mp (hn x)
  left_orthogonal x m n hm hn := by
    change CoefficientChange.pairingEquiv e p.pairing
      ((coefficientChangeSections e he S Set.univ).symm m)
      ((coefficientChangeSections e he S Set.univ).symm n) = 0
    rw [CoefficientChange.pairingEquiv_apply]
    apply (congrArg e ?_).trans (map_zero e)
    apply p.left_orthogonal x
    · intro y hy
      rw [coefficientChangeSections_symm_val_apply]
      exact (congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hm y hy)).trans (CoefficientChange.val_zero e (S.vertex y))
    · rw [coefficientChangeSections_symm_val_apply]
      exact (congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) (hn)).trans (CoefficientChange.val_zero e (S.vertex x))
  right_orthogonal x m n hm hn := by
    change CoefficientChange.pairingEquiv e p.pairing
      ((coefficientChangeSections e he S Set.univ).symm m)
      ((coefficientChangeSections e he S Set.univ).symm n) = 0
    rw [CoefficientChange.pairingEquiv_apply]
    apply (congrArg e ?_).trans (map_zero e)
    apply p.right_orthogonal x
    · rw [coefficientChangeSections_symm_val_apply]
      exact (congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) (hm)).trans (CoefficientChange.val_zero e (S.vertex x))
    · intro y hy
      rw [coefficientChangeSections_symm_val_apply]
      exact (congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hn y hy)).trans (CoefficientChange.val_zero e (S.vertex y))

 /-- Pairing transport is coefficient transport after inverse section transport. -/
 theorem PerfectPairing.coefficientChange_apply {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
     (p : PerfectPairing S d) (m n : (GradedSheaf.coefficientChange e he S).forget.sections Set.univ) :
     (p.coefficientChange e he).pairing m n =
       e (p.pairing ((coefficientChangeSections e he S Set.univ).symm m).val
         ((coefficientChangeSections e he S Set.univ).symm n).val) := by
   exact CoefficientChange.pairingEquiv_apply e p.pairing _ _

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
