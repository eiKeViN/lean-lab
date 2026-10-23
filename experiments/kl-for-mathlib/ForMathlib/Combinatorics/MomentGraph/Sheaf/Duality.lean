module
public import Mathlib
public import ForMathlib.Algebra.Module.Free.ScalarDivisibility
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
public import ForMathlib.LinearAlgebra.Dual.IntegralSupport

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality. Source spans: Support:15, Support:17.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

/-- A common edge annihilator makes all the scaled coordinate idempotents
integral endomorphisms of the section module. -/
 theorem scaled_single_section [DecidableEq V] {p : R}
    (hp : ∀ e (v : B.edge e), p • v = 0) (x : V) (m : B.sections Set.univ) :
    p • Pi.single x (m.val x) ∈ B.sections Set.univ := by
  intro e _ _
  simp only [Pi.smul_apply,map_smul,hp]

variable [Fintype E] (α : E → R)

@[expose] def labelProduct : R := ∏ e, α e

 theorem labelProduct_ne_zero [IsDomain R] (hα : ∀ e, α e ≠ 0) : labelProduct α ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => hα e)

 theorem labelProduct_annihilates (hα : ∀ e (v : B.edge e), α e • v = 0)
    (e : E) (v : B.edge e) : labelProduct α • v = 0 := by
  obtain ⟨r,hr⟩ := Finset.dvd_prod_of_mem α (Finset.mem_univ e)
  change (∏ e, α e) • v = 0
  rw [hr,mul_comm, mul_smul,hα,smul_zero]

omit [Fintype E] in
 theorem projection_surjective (hg : B.Generated) (x : V) :
    Function.Surjective (IntegralSupport.projection (B.sections Set.univ) x) := by
  intro a
  obtain ⟨m,hm,hx⟩ := hg x a
  exact ⟨⟨m,hm⟩,hx⟩

variable [DecidableEq V] [IsDomain R] [∀ x, Module.IsTorsionFree R (B.vertex x)]
  (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (d : B.sections Set.univ ≃ₗ[R] Module.Dual R (B.sections Set.univ))
  (hbalanced : ∀ x m n,
    d (IntegralSupport.cut (B.sections Set.univ) (labelProduct α)
      (B.scaled_single_section (B.labelProduct_annihilates α ha)) x m) n =
    d m (IntegralSupport.cut (B.sections Set.univ) (labelProduct α)
      (B.scaled_single_section (B.labelProduct_annihilates α ha)) x n))


@[expose] noncomputable def singleSupportEquivDual (hg : B.Generated) (x : V) :
    IntegralSupport.supported (B.sections Set.univ) x ≃ₗ[R] Module.Dual R (B.vertex x) :=
  IntegralSupport.supportEquivDual (B.sections Set.univ) (labelProduct α)
    (B.scaled_single_section (B.labelProduct_annihilates α ha))
    (labelProduct_ne_zero α hα) d hbalanced x (B.projection_surjective hg x)

end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um ui
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem stalkMap_eq_zero_iff (x : V) (v : B.vertex x) :
    B.stalkMap x v = 0 ↔ ∀ e (h : G.source e = x), B.lower e (h.symm ▸ v) = 0 := by
  constructor
  · intro hv e he
    exact congrFun hv ⟨e,he⟩
  · intro hv
    funext e
    exact hv e.val e.property

 theorem single_section_iff [DecidableEq V] (x : V) (v : B.vertex x) :
    Pi.single x v ∈ B.sections Set.univ ↔
      B.stalkMap x v = 0 ∧ ∀ e (h : G.target e = x), B.upper e (h.symm ▸ v) = 0 := by
  constructor
  · intro hv
    constructor
    · apply (B.stalkMap_eq_zero_iff x v).mpr
      intro e he
      subst x
      have hc := hv e (Set.mem_univ _) (Set.mem_univ _)
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_gt (G.increasing e)),map_zero] using hc
    · intro e he
      subst x
      have hc := hv e (Set.mem_univ _) (Set.mem_univ _)
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt (G.increasing e)),map_zero] using hc.symm
  · rintro ⟨hu,hd⟩ e _ _
    by_cases hs : G.source e = x
    · subst x
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_gt (G.increasing e)),map_zero]
        using (B.stalkMap_eq_zero_iff _ _).mp hu e rfl
    · by_cases ht : G.target e = x
      · subst x
        simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt (G.increasing e)),map_zero]
          using (hd e rfl).symm
      · simp only [Pi.single_eq_of_ne hs,Pi.single_eq_of_ne ht,map_zero]

variable [Fintype E] [DecidableEq V]

@[expose] def incoming (x : V) : Finset E := Finset.univ.filter (fun e => G.target e = x)

@[simp] theorem mem_incoming (x : V) (e : E) : e ∈ incoming (G := G) x ↔ G.target e = x := by
  simp [incoming]

@[expose] def incomingProduct (α : E → R) (x : V) : R := ∏ e ∈ incoming (G := G) x, α e

variable [IsDomain R] (α : E → R)
  (hα : ∀ e, Prime (α e))
  (hq : ∀ e, Function.Surjective (B.upper e))
  (hk : ∀ e v, B.upper e v = 0 ↔ ∃ w, v = α e • w)
  {ι : V → Type ui} [∀ x, Fintype (ι x)] (bs : ∀ x, Module.Basis (ι x) R (B.vertex x))

include hα in
 theorem incomingProduct_ne_zero (x : V) : incomingProduct (G := G) α x ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => (hα e).ne_zero)

omit [IsDomain R] in
include hα hq hk bs in
 theorem outgoing_product_regular (x : V)
    (hsep : ∀ e f, G.source e = x → G.target f = x → ¬ α e ∣ α f)
    (e : E) (he : G.source e = x) :
    Function.Injective (fun v : B.edge e => incomingProduct (G := G) α x • v) := by
  apply FiniteFreeScalar.scalar_quotient_regular (bs (G.target e)) (B.upper e) (hq e)
    (α e) (incomingProduct (G := G) α x) (hα e) _ (hk e)
  intro hdiv
  obtain ⟨f,hf,hfdiv⟩ := ((hα e).dvd_finsetProd_iff α).mp hdiv
  exact hsep e f he ((mem_incoming (G := G) x f).mp hf) hfdiv

omit [IsDomain R] in
include hk bs in
/-- The actual integral single-support conditions. Downward labels impose
product divisibility, and they are regular at every upward edge. -/
 theorem single_section_iff_prod [DecompositionMonoid R] (x : V)
    (hrel : (incoming (G := G) x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hreg : ∀ e, G.source e = x → Function.Injective
      (fun v : B.edge e => incomingProduct (G := G) α x • v)) (v : B.vertex x) :
    Pi.single x v ∈ B.sections Set.univ ↔
      ∃ w : B.vertex x, v = incomingProduct (G := G) α x • w ∧ B.stalkMap x w = 0 := by
  constructor
  · intro hv
    obtain ⟨hu,hd⟩ := (B.single_section_iff x v).mp hv
    have hdiv : ∀ e ∈ incoming (G := G) x, ∃ w : B.vertex x, α e • w = v := by
      intro e he
      have ht := (mem_incoming (G := G) x e).mp he
      subst x
      obtain ⟨w,hw⟩ := (hk e v).mp (hd e rfl)
      exact ⟨w,hw.symm⟩
    obtain ⟨w,hw⟩ := FiniteFreeScalar.exists_prod_smul (bs x) (incoming (G := G) x) α hrel v hdiv
    refine ⟨w,hw.symm,?_⟩
    apply (B.stalkMap_eq_zero_iff x w).mpr
    intro e he
    apply hreg e he
    change incomingProduct (G := G) α x • _ = incomingProduct (G := G) α x • (0 : B.edge e)
    rw [smul_zero]
    have hz := (B.stalkMap_eq_zero_iff x v).mp hu e he
    subst x
    rw [← hw,map_smul] at hz
    exact hz
  · rintro ⟨w,rfl,hw⟩
    apply (B.single_section_iff x _).mpr
    constructor
    · rw [map_smul,hw,smul_zero]
    · intro e he
      subst x
      obtain ⟨r,hr⟩ := Finset.dvd_prod_of_mem α ((mem_incoming (G := G) _ e).mpr rfl)
      apply (hk e _).mpr
      exact ⟨r • w, by rw [incomingProduct,hr,mul_smul]⟩

/-- The single-support part as an actual submodule of its stalk. -/
@[expose] def singleStalk (x : V) : Submodule R (B.vertex x) :=
  (B.sections Set.univ).comap (LinearMap.single R (fun y => B.vertex y) x)

@[expose] noncomputable def singleStalkEquivSupport (x : V) :
    B.singleStalk x ≃ₗ[R] IntegralSupport.supported (B.sections Set.univ) x := by
  let f : B.singleStalk x →ₗ[R] IntegralSupport.supported (B.sections Set.univ) x :=
    { toFun := fun v => ⟨⟨Pi.single x v.val,v.property⟩,by
                        intro y hy; exact Pi.single_eq_of_ne hy _⟩
      map_add' := by intro v w; apply Subtype.ext; apply Subtype.ext; exact Pi.single_add _ _ _
      map_smul' := by intro r v; apply Subtype.ext; apply Subtype.ext; exact Pi.single_smul _ _ _ }
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w hvw
    apply Subtype.ext
    have hv := congrArg (fun s : IntegralSupport.supported (B.sections Set.univ) x => s.val.val x) hvw
    change (Pi.single x v.val : B.Assignment) x = (Pi.single x w.val : B.Assignment) x at hv
    simpa only [Pi.single_eq_same] using hv
  · intro m
    have he : Pi.single x (m.val.val x) = m.val.val := by
      funext y
      by_cases hy : y=x
      · subst y; simp only [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hy, m.property y hy]
    refine ⟨⟨m.val.val x,?_⟩,?_⟩
    · change Pi.single x (m.val.val x) ∈ B.sections Set.univ
      rw [he]; exact m.val.property
    · apply Subtype.ext; apply Subtype.ext; exact he


@[expose] noncomputable def kernelEquivSingleStalk [DecompositionMonoid R] (x : V)
    (hrel : (incoming (G := G) x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hreg : ∀ e, G.source e = x → Function.Injective
      (fun v : B.edge e => incomingProduct (G := G) α x • v)) :
    LinearMap.ker (B.stalkMap x) ≃ₗ[R] B.singleStalk x := by
  let p := incomingProduct (G := G) α x
  let f : LinearMap.ker (B.stalkMap x) →ₗ[R] B.singleStalk x :=
    (p • (LinearMap.ker (B.stalkMap x)).subtype).codRestrict (B.singleStalk x) (by
      intro v
      exact (B.single_section_iff_prod α hk bs x hrel hreg _).mpr ⟨v.val,rfl,v.property⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w hvw
    apply Subtype.ext
    let : Module.Free R (B.vertex x) := Module.Free.of_basis (bs x)
    exact smul_right_injective (B.vertex x) (incomingProduct_ne_zero α hα x)
      (congrArg Subtype.val hvw)
  · intro v
    obtain ⟨w,hw,hz⟩ := (B.single_section_iff_prod α hk bs x hrel hreg v.val).mp v.property
    exact ⟨⟨w,hz⟩,Subtype.ext hw.symm⟩

end KLInvariance.MomentGraph.Sheaf
end

end OAI
