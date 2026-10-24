module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.ModuleData.CharacterDual
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models
public import ForMathlib.RepresentationTheory.Hecke.OrdinaryR
public import OAI.KL.Sheaves.LowerCharacter
public import OAI.KL.Sheaves.Support

public section

/-! Semantic home: OAI.KL.Sheaves.FreeModel. Source spans: CharacterReciprocity:1, CharacterReciprocity:4, CharacterReciprocity:5, CharacterReciprocity:11, CharacterReciprocity:36, CharacterReciprocity:37.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
variable [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

@[expose] def SectionDualityObligation : Prop :=
  ∃ d : SectionDuality cs 1 b basis (one_bruhat cs b)
    (boundarySheaf cs 1 b basis (one_bruhat cs b)),
    ∀ i j (m n : (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ),
      m ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece i →
      n ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-(cs.length b : ℤ))

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 theorem sectionDualityObligation_of_perfectPairing
    (p : GradedSheaf.PerfectPairing
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf (cs.length b : ℤ)) :
    SectionDualityObligation cs b basis := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  refine ⟨⟨p.pairing,?_⟩,?_⟩
  · intro x m n
    exact p.cut_balanced (Sheaf.labelProduct (polynomialLabel cs 1 b basis))
      (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs 1 b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs 1 b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m n
  · intro i j m n hm hn
    exact p.homogeneous i j m n (fun x => hm x (Set.mem_univ x))
      (fun x => hn x (Set.mem_univ x))

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

structure FreeSheaf where
  sheaf : GradedSheaf (𝓐 := polynomialGrading ℝ σ) (graph cs u b)
  free : sheaf.FreeStalks
  quotient : sheaf.UpperQuotient (polynomialLabel cs u b basis)
  generated : sheaf.forget.Generated

namespace FreeSheaf
variable (B : FreeSheaf cs u b basis)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section
 @[expose] def kernelEquivSingleSupport (x : Interval cs u b) :
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

 @[expose] def costalkEquivDual (d : SectionDuality cs u b basis B) (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  exact (kernelEquivSingleSupport cs u b basis B x).trans
    (B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced B.generated x)

 theorem costalk_free_of_duality (d : SectionDuality cs u b basis B)
    (x : Interval cs u b) :
    Module.Free (Coefficient (σ := σ)) (LinearMap.ker (B.sheaf.forget.stalkMap x)) := by
  let _ := B.free x
  exact Module.Free.of_equiv (costalkEquivDual cs u b basis B d x).symm

 variable [Fintype σ] [Fintype (Interval cs u b)]

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis B d x).symm lam).val ∈
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
      ((costalkEquivDual cs u b basis B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis B x)
        ((kernelEquivSingleSupport cs u b basis B x).symm (S.symm lam))).val.val x
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

 @[expose] def fullSubmodule (x : Interval cs u b) : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex x) :=
    LinearMap.ker (B.sheaf.forget.stalkMap x)

omit [Fintype σ] [Fintype (Edge cs u b)] [Fintype (Interval cs u b)]
  [DecidableEq (Interval cs u b)] in
 theorem fullKernel_eq (x : Interval cs u b) :
    B.sheaf.upwardSubmodule x Set.univ = fullSubmodule cs u b basis B x := by
  ext m
  change (∀ e ∈ Set.univ, B.sheaf.forget.stalkMap x m e = 0) ↔ B.sheaf.forget.stalkMap x m = 0
  simp only [Set.mem_univ,forall_const]
  exact funext_iff.symm

 @[expose] def fullKernel (x : Interval cs u b) : ModuleData (polynomialGrading ℝ σ) :=
  ModuleData.sub (B.sheaf.vertex x) (fullSubmodule cs u b basis B x) (by
    simpa only [fullKernel_eq cs u b basis B x] using
      B.sheaf.upwardKernel_homogeneous x Set.univ)

 theorem costalk_hilbert_of_duality
    (d : SectionDuality cs u b basis B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (c : NonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Hilbert.value (B.sheaf.vertex x).piece
      ((fullSubmodule cs u b basis B x).restrictScalars ℝ) q =
      q^(l-(Sheaf.incoming (G := graph cs u b) x).card) *
        Polynomial.eval₂ (Int.castRingHom ℝ) q⁻¹ c.polynomial *
        (1-q)⁻¹ ^ Fintype.card σ := by
  classical
  let K := fullKernel cs u b basis B x
  let cb : Basis c.index (Coefficient (σ := σ)) K :=
    c.basis.dualBasis.map (costalkEquivDual cs u b basis B d x).symm
  have hcb (i : c.index) : cb i ∈ K.piece
      (l-(Sheaf.incoming (G := graph cs u b) x).card-(c.degree i : ℤ)) := by
    change ((costalkEquivDual cs u b basis B d x).symm (c.basis.dualBasis i)).val ∈
      (B.sheaf.vertex x).piece _
    have h := costalkEquivDual_inverse_homogeneous cs u b basis B d l hd x
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
    ((fullSubmodule cs u b basis B x).restrictScalars ℝ) q = _
  rw [← Hilbert.value_subPiece]
  change Hilbert.value K.piece ⊤ q = _
  rw [hv,c.eval₂_eq,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [zpow_sub₀ hq.ne',zpow_natCast,div_eq_mul_inv,inv_pow]


 @[expose] def dualityOfPairing {l : ℤ} (p : GradedSheaf.PerfectPairing B.sheaf l) :
    SectionDuality cs u b basis B where
  pairing := p.pairing
  balanced := p.cut_balanced
    (Sheaf.labelProduct (polynomialLabel cs u b basis))
    (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs u b basis))
    (B.sheaf.forget.scaled_single_section
      (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)))

end
end FreeSheaf
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph.FreeSheaf
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (B : FreeSheaf cs 1 b basis)
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 @[expose] def kernelDual (d : SectionDuality cs 1 b basis B) (x : Interval cs 1 b) :
    Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) ≃ₗ[Coefficient (σ := σ)]
      GradedSheaf.kernelData B.sheaf x :=
  (costalkEquivDual cs 1 b basis B d x).symm.trans (B.sheaf.kernelEquivFull x).symm

omit [Fintype (Interval cs 1 b)] in
 theorem kernel_free (d : SectionDuality cs 1 b basis B) (x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ)) (GradedSheaf.kernelData B.sheaf x) := by
  let := B.free x
  exact Module.Free.of_equiv (kernelDual cs b basis B d x)

 theorem kernelDual_homogeneous (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (x : Interval cs 1 b) (hn : cs.length x.val≤n) (r : ℤ)
    (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v∈(B.sheaf.vertex x).piece j →
      lam v∈polynomialGrading ℝ σ (j+r)) :
    kernelDual cs b basis B d x lam∈(GradedSheaf.kernelData B.sheaf x).piece
      (r+(n-cs.length x.val : ℕ)) := by
  have h := costalkEquivDual_inverse_homogeneous cs 1 b basis B d n hd x r lam hlam
  rw [incoming_card] at h
  change ((costalkEquivDual cs 1 b basis B d x).symm lam).val∈
    (B.sheaf.vertex x).piece (r+↑(n-cs.length x.val))
  have he : r+(n:ℤ)-cs.length x.val=r+↑(n-cs.length x.val) := by omega
  rwa [he] at h

 theorem kernel_character (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (hn : cs.length b≤n) (x : Interval cs 1 b) :
    GradedSheaf.freeKernelChar B.sheaf (kernel_free cs b basis B d) x=
      Polynomial.reflect (n-cs.length x.val) (GradedSheaf.freeStalkChar B.sheaf B.free x) := by
  let := B.free x
  let := kernel_free cs b basis B d x
  exact ModuleData.char_of_dual_equiv _ _ (kernelDual cs b basis B d x) _
    (kernelDual_homogeneous cs b basis B d n hd x ((length_le_of_bruhat cs x.property.2).trans hn))

end
end KLInvariance.BruhatGraph.FreeSheaf
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI_3 (p : Prop) : Decidable p := Classical.propDecidable p

 theorem stalkCharacter_top :
    stalkCharacter cs 1 b basis (one_bruhat cs b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩=1 := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let := B.free ⟨b,one_bruhat cs b,bruhat_refl cs b⟩
  change (B.sheaf.vertex ⟨b,one_bruhat cs b,bruhat_refl cs b⟩).char=1
  exact (ModuleData.character_eq_of_gradedEquiv (ModuleData.equivOfEq B.top)
    (ModuleData.equivOfEq_graded B.top)).trans ModuleData.char_unit

 theorem lowerCharacter_diagonal (c : Interval cs 1 b) : lowerCharacter cs b basis c c=1 := by
  rw [lowerCharacter,dite_eq_left le_rfl]
  exact stalkCharacter_top cs c.val basis

 theorem lowerCharacter_at_top (c : Interval cs 1 b) :
    lowerCharacter cs b basis c ⟨b,one_bruhat cs b,bruhat_refl cs b⟩=
      if c.val=b then 1 else 0 := by
  by_cases hc : c.val=b
  · have he : c=⟨b,one_bruhat cs b,bruhat_refl cs b⟩ := Subtype.ext hc
    rw [ite_eq_left hc,←he,lowerCharacter_diagonal]
  · rw [ite_eq_right hc]
    apply lowerCharacter_zero
    intro h
    exact hc (bruhat_antisymm cs c.property.2 h)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI_4 (p : Prop) : Decidable p := Classical.propDecidable p
local instance lowerConvInterval (c : W) : Fintype (Interval cs 1 c) := by
  let := interval_finite cs 1 c
  exact Fintype.ofFinite _

 @[expose] def lowerIntervalEquiv (c : Interval cs 1 b) : Set.Iic c ≃ Interval cs 1 c.val where
  toFun := (lowerIntervalMap cs b c).vertex
  invFun z := ⟨⟨z.val,z.property.1,bruhat_trans cs z.property.2 c.property.2⟩,z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem lowerCharacter_convolution (c x : Interval cs 1 b) :
    (∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z)=
      ∑ z : Interval cs 1 c.val, OrdinaryR.polynomial cs x.val z.val*
        stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z := by
  classical
  let f (z : Interval cs 1 b) := OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z
  have hf : ∀ z : Interval cs 1 b, ¬z≤c → f z=0 := by
    intro z hz
    simp only [f,lowerCharacter_zero cs b basis c z hz,mul_zero]
  have he : (∑ z : Interval cs 1 b, f z) = ∑ z ∈ Finset.univ.filter (fun z => z≤c), f z := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z _ hz
    exact hf z (by simpa using hz)
  change (∑ z, f z)=_
  rw [he,Finset.sum_subtype (p := fun z : Interval cs 1 b => z≤c) _ (by simp)]
  calc
    _ = ∑ z : Set.Iic c, OrdinaryR.polynomial cs x.val z.val.val*
        stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) ((lowerIntervalEquiv cs b c) z) := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [f,lowerCharacter,dite_eq_left z.property]
      rfl
    _ = _ := Equiv.sum_comp (lowerIntervalEquiv cs b c) (fun z => OrdinaryR.polynomial cs x.val z.val*
      stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z)

 theorem lowerCharacter_convolution_zero (c x : Interval cs 1 b) (hx : ¬x≤c) :
    (∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z)=0 := by
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z≤c
  · rw [OrdinaryR.polynomial_zero cs x.val z.val (fun h => hx (bruhat_trans cs h hz)),zero_mul]
  · rw [lowerCharacter_zero cs b basis c z hz,mul_zero]

 theorem lowerCharacter_reciprocity_lift (c : Interval cs 1 b)
    (h : ∀ x : Interval cs 1 c.val,
      reflect (rankDifference cs x.val c.val) (stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) x)=
        ∑ z : Interval cs 1 c.val, OrdinaryR.polynomial cs x.val z.val*
          stalkCharacter cs 1 c.val basis (one_bruhat cs c.val) z)
    (x : Interval cs 1 b) :
      reflect (rankDifference cs x.val c.val) (lowerCharacter cs b basis c x)=
        ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*lowerCharacter cs b basis c z := by
  by_cases hx : x≤c
  · rw [lowerCharacter_convolution,lowerCharacter,dite_eq_left hx]
    exact h ⟨x.val,x.property.1,hx⟩
  · rw [lowerCharacter_zero cs b basis c x hx,reflect_zero,lowerCharacter_convolution_zero cs b basis c x hx]

end
end KLInvariance.BruhatGraph
end

end OAI
