import Mathlib
import ForMathlib.Algebra.Module.Graded.HomogeneousDual
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality
import ForMathlib.GroupTheory.Coxeter.Roots.Order
import OAI.KL.Sheaves.Boundary

/-! Semantic home: OAI.KL.Sheaves.Support. Source spans: Support:27, Support:18, Support:22, Support:23, Support:26, Support:28.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
noncomputable section

 def incomingEquivInversions (x : Interval cs 1 b) :
    {e : Edge cs 1 b // target cs 1 b e = x} ≃ {t : W // cs.IsLeftInversion x.val t} where
  toFun e := ⟨label cs 1 b e.val, label_isReflection cs 1 b e.val, by
    have hx : (target cs 1 b e.val).val = x.val := congrArg Subtype.val e.property
    have he := label_mul_target cs 1 b e.val
    rw [hx] at he
    rw [he]
    have h := e.val.property.1
    change cs.length (source cs 1 b e.val).val < cs.length (target cs 1 b e.val).val at h
    simpa only [hx] using h⟩
  invFun t := by
    have hstep : BruhatStep cs (t.val*x.val) x.val := by
      refine ⟨t.property.2,t.val,t.property.1,?_⟩
      rw [← mul_assoc,t.property.1.mul_self,one_mul]
    let y : Interval cs 1 b := ⟨t.val*x.val,one_bruhat cs _,
      (Relation.ReflTransGen.single hstep).trans x.property.2⟩
    exact ⟨⟨(y,x),hstep⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply eq_of_label_target_eq cs 1 b
    · change x.val * (label cs 1 b e.val*x.val)⁻¹ = label cs 1 b e.val
      rw [mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul,
        (label_isReflection cs 1 b e.val).inv]
    · exact e.property.symm
  right_inv t := by
    apply Subtype.ext
    change x.val * (t.val*x.val)⁻¹=t.val
    rw [mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul,t.property.1.inv]

 theorem incoming_card [Fintype (Edge cs 1 b)] [DecidableEq (Interval cs 1 b)]
    (x : Interval cs 1 b) : (Sheaf.incoming (G := graph cs 1 b) x).card = cs.length x.val := by
  classical
  calc
    _ = Nat.card {e : Edge cs 1 b // target cs 1 b e = x} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    _ = Nat.card {t : W // cs.IsLeftInversion x.val t} := Nat.card_congr (incomingEquivInversions cs b x)
    _ = Nat.card (RootInversions M cs x.val) := Nat.card_congr (rootInversionEquiv M cs x.val).symm
    _ = cs.length x.val := card_rootInversions M cs x.val

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem root_injective_on_labels {e f : Edge cs u b} (h : root cs u b e = root cs u b f) :
    label cs u b e = label cs u b f := by
  exact congrArg Subtype.val ((positiveRootEquiv M cs).injective h)

 theorem polynomialLabel_prime (e : Edge cs u b) : Prime (polynomialLabel cs u b basis e) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact (root cs u b e).property.1.ne_zero (congrArg Prod.fst h)

 theorem label_eq_of_polynomialLabel_dvd {e f : Edge cs u b}
    (h : polynomialLabel cs u b basis e ∣ polynomialLabel cs u b basis f) :
    label cs u b e = label cs u b f := by
  apply root_injective_on_labels cs u b
  by_contra hn
  have hd : SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b f).val) := by
    obtain ⟨z,hz⟩ := h
    exact ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z, by
      apply (SymmetricAlgebra.equivMvPolynomial basis).injective
      simpa only [map_mul,AlgEquiv.apply_symm_apply,polynomialLabel] using hz⟩
  have hm := (EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp hd
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hm
  have he : r • (root cs u b e).val = (1 : ℝ) • (root cs u b f).val := by
    have hfst := congrArg Prod.fst hr
    change r • (root cs u b e).val = (root cs u b f).val at hfst
    simpa only [one_smul] using hfst
  exact one_ne_zero ((positiveRoots_independent _ _ hn).eq_zero_of_pair' he).2

 theorem incoming_pairwise_relPrime [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)] (x : Interval cs u b) :
    (Sheaf.incoming (G := graph cs u b) x : Set (Edge cs u b)).Pairwise
      (Function.onFun IsRelPrime (polynomialLabel cs u b basis)) := by
  intro e he f hf hne
  apply ((polynomialLabel_prime cs u b basis e).irreducible.isRelPrime_iff_not_dvd).mpr
  intro hdiv
  apply hne
  apply eq_of_label_target_eq cs u b (label_eq_of_polynomialLabel_dvd cs u b basis hdiv)
  exact ((Sheaf.mem_incoming x e).mp he).trans ((Sheaf.mem_incoming x f).mp hf).symm

 theorem outgoing_incoming_not_dvd (x : Interval cs u b) (e f : Edge cs u b)
    (he : (graph cs u b).source e = x) (hf : (graph cs u b).target f = x) :
    ¬ polynomialLabel cs u b basis e ∣ polynomialLabel cs u b basis f := by
  intro h
  apply source_ne_target_of_label_eq cs u b (label_eq_of_polynomialLabel_dvd cs u b basis h)
  exact he.trans hf.symm

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem label_regular_stalk (e : Edge cs u b) (x : Interval cs u b) :
    Function.Injective (fun v : B.sheaf.vertex x => polynomialLabel cs u b basis e • v) := by
  let := B.free x
  exact smul_right_injective _ (polynomialLabel_ne_zero cs u b basis e)

omit [Fintype σ] in


 theorem incoming_label_regular_outgoing (e f : Edge cs u b)
    (h : (graph cs u b).source f = (graph cs u b).target e) :
    Function.Injective (fun v : B.sheaf.edge f => polynomialLabel cs u b basis e • v) := by
  let := B.free ((graph cs u b).target f)
  exact FiniteFreeScalar.scalar_quotient_regular
    (Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.vertex ((graph cs u b).target f)))
    (B.sheaf.upper f).map (B.quotient f).1
    (polynomialLabel cs u b basis f) (polynomialLabel cs u b basis e)
    (polynomialLabel_prime cs u b basis f)
    (outgoing_incoming_not_dvd cs u b basis _ f e h rfl) (B.quotient f).2

 theorem upper_image_hilbert (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) ((graph cs u b).target e)))
    [∀ n, Module.Finite ℝ ((B.sheaf.vertex ((graph cs u b).target e)).piece n)]
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (Hilbert.term (B.sheaf.vertex ((graph cs u b).target e)).piece
      ((B.sheaf.upwardSubmodule ((graph cs u b).target e) F).restrictScalars ℝ) q)) :
    Hilbert.value (B.sheaf.edge e).piece
      (((B.sheaf.upwardSubmodule ((graph cs u b).target e) F).map
        (B.sheaf.upper e).map).restrictScalars ℝ) q =
      (1-q) * Hilbert.value (B.sheaf.vertex ((graph cs u b).target e)).piece
        ((B.sheaf.upwardSubmodule ((graph cs u b).target e) F).restrictScalars ℝ) q := by
  apply B.sheaf.upper_image_value (polynomialLabel cs u b basis) B.quotient e F
    (polynomialLabel_homogeneous cs u b basis e)
  · intro f _
    exact incoming_label_regular_outgoing cs u b basis hub B e f.val f.property
  · exact label_regular_stalk cs u b basis hub B e _
  · exact hq
  · exact hs

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 def kernelEquivSingleSupport (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      IntegralSupport.supported (B.sheaf.forget.sections Set.univ) x := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (x : Interval cs u b) : Module.Finite (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) :=
    (B.sheaf.vertex x).finite
  let _ (x : Interval cs u b) : Fintype (Module.Free.ChooseBasisIndex
      (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)) := Fintype.ofFinite _
  let bs := fun x : Interval cs u b =>
    Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)
  exact (B.sheaf.forget.kernelEquivSingleStalk (polynomialLabel cs u b basis)
    (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).2) bs x
    (incoming_pairwise_relPrime cs u b basis x)
    (B.sheaf.forget.outgoing_product_regular (polynomialLabel cs u b basis)
      (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).1)
      (fun e => (B.quotient e).2) bs x
      (outgoing_incoming_not_dvd cs u b basis x))).trans
        (B.sheaf.forget.singleStalkEquivSupport x)


structure SectionDuality where
  pairing : B.sheaf.forget.sections Set.univ ≃ₗ[Coefficient (σ := σ)]
    Dual (Coefficient (σ := σ)) (B.sheaf.forget.sections Set.univ)
  balanced : ∀ x m n,
    pairing (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m) n =
    pairing m (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x n)

 def costalkEquivDual (d : SectionDuality cs u b basis hub B) (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  exact (kernelEquivSingleSupport cs u b basis hub B x).trans
    (B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced B.generated x)

 theorem costalk_free_of_duality (d : SectionDuality cs u b basis hub B)
    (x : Interval cs u b) :
    Module.Free (Coefficient (σ := σ)) (LinearMap.ker (B.sheaf.forget.stalkMap x)) := by
  let _ := B.free x
  exact Module.Free.of_equiv (costalkEquivDual cs u b basis hub B d x).symm

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

omit [Fintype (Interval cs u b)] in
 theorem incomingProduct_homogeneous (x : Interval cs u b) :
    Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x ∈
      polynomialGrading ℝ σ ((Sheaf.incoming (G := graph cs u b) x).card : ℤ) := by
  simpa only [Sheaf.incomingProduct,Finset.sum_const,Int.natCast_one,mul_one,nsmul_eq_mul] using
    SetLike.prod_mem_graded (polynomialGrading ℝ σ) (fun _ : Edge cs u b => (1 : ℤ))
      (polynomialLabel cs u b basis)
      (F := Sheaf.incoming (G := graph cs u b) x)
      (fun e _ => polynomialLabel_homogeneous cs u b basis e)

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis hub B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis hub B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis hub B d x).symm lam).val ∈
      (B.sheaf.vertex x).piece
        (r+l-(Sheaf.incoming (G := graph cs u b) x).card) := by
  let _ (y : Interval cs u b) : Module.Free (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := B.free y
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  let S := B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
    (polynomialLabel_ne_zero cs u b basis)
    (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
    d.pairing d.balanced B.generated x
  have hs : (S.symm lam).val ∈ (B.sheaf.sections Set.univ).piece (r+l) := by
    exact B.sheaf.dualToSupport_homogeneous (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced l hd x r lam hlam
  have hv := hs x (Set.mem_univ x)
  have he : (S.symm lam).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x •
      ((costalkEquivDual cs u b basis hub B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis hub B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis hub B x)
        ((kernelEquivSingleSupport cs u b basis hub B x).symm (S.symm lam))).val.val x
    rw [LinearEquiv.apply_symm_apply]
  change (S.symm lam).val.val x ∈ (B.sheaf.vertex x).piece (r+l) at hv
  rw [he] at hv
  apply mem_of_homogeneous_smul (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
    ((Sheaf.incoming (G := graph cs u b) x).card : ℤ)
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x)
    (incomingProduct_homogeneous cs u b basis x) _ (r+l) _ hv
  let _ := B.free x
  exact smul_right_injective _ (Sheaf.incomingProduct_ne_zero
    (polynomialLabel cs u b basis) (polynomialLabel_prime cs u b basis) x)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 def fullSubmodule (x : Interval cs u b) : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex x) :=
    LinearMap.ker (B.sheaf.forget.stalkMap x)

omit [Fintype σ] [Fintype (Edge cs u b)] [Fintype (Interval cs u b)]
  [DecidableEq (Interval cs u b)] in
 theorem fullKernel_eq (x : Interval cs u b) :
    B.sheaf.upwardSubmodule x Set.univ = fullSubmodule cs u b basis hub B x := by
  ext m
  change (∀ e ∈ Set.univ, B.sheaf.forget.stalkMap x m e = 0) ↔ B.sheaf.forget.stalkMap x m = 0
  simp only [Set.mem_univ,forall_const]
  exact funext_iff.symm

 def fullKernel (x : Interval cs u b) : ModuleData (polynomialGrading ℝ σ) :=
  ModuleData.sub (B.sheaf.vertex x) (fullSubmodule cs u b basis hub B x) (by
    simpa only [fullKernel_eq cs u b basis hub B x] using
      B.sheaf.upwardKernel_homogeneous x Set.univ)

 theorem costalk_hilbert_of_duality
    (d : SectionDuality cs u b basis hub B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (c : NonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Hilbert.value (B.sheaf.vertex x).piece
      ((fullSubmodule cs u b basis hub B x).restrictScalars ℝ) q =
      q^(l-(Sheaf.incoming (G := graph cs u b) x).card) *
        Polynomial.eval₂ (Int.castRingHom ℝ) q⁻¹ c.polynomial *
        (1-q)⁻¹ ^ Fintype.card σ := by
  classical
  let K := fullKernel cs u b basis hub B x
  let cb : Basis c.index (Coefficient (σ := σ)) K :=
    c.basis.dualBasis.map (costalkEquivDual cs u b basis hub B d x).symm
  have hcb (i : c.index) : cb i ∈ K.piece
      (l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) := by
    change ((costalkEquivDual cs u b basis hub B d x).symm (c.basis.dualBasis i)).val ∈
      (B.sheaf.vertex x).piece _
    have h := costalkEquivDual_inverse_homogeneous cs u b basis hub B d l hd x
      (-(c.degree i : ℤ)) (c.basis.dualBasis i)
      (dualBasis_homogeneous (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
        c.basis (fun i => (c.degree i : ℤ)) c.homogeneous i)
    simpa only [show -(c.degree i : ℤ)+l-(Sheaf.incoming (G := graph cs u b) x).card =
      l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ) by omega] using h
  have hs := Hilbert.hasSum_homogeneous_basis K.piece cb
    (fun i => l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) hcb hq hq1
  have hv : Hilbert.value K.piece ⊤ q =
      (∑ i, q^(l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ))) *
        (1-q)⁻¹ ^ Fintype.card σ := by
    simpa only [Hilbert.value,Hilbert.term_top] using hs.tsum_eq
  change Hilbert.value (B.sheaf.vertex x).piece
    ((fullSubmodule cs u b basis hub B x).restrictScalars ℝ) q = _
  rw [← Hilbert.value_subPiece]
  change Hilbert.value K.piece ⊤ q = _
  rw [hv,c.eval₂_eq,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hq.ne',zpow_natCast,div_eq_mul_inv,inv_pow]

end
end KLInvariance.BruhatGraph
end

end OAI
