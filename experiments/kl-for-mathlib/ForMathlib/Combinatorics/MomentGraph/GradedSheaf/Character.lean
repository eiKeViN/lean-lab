module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.ModuleData.Character
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character. Source spans: Decomposition:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 @[expose] def freeStalkChar (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x)) (x : V) : Polynomial ℤ := by
  let := hf x
  exact (B.vertex x).char

 theorem ModelSum.character {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    [Fintype V] {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O.sheaf U B) :
    ∃ hmul : V → Polynomial ℤ,
      (∀ y n, 0 ≤ (hmul y).coeff n) ∧
      (∀ y, y ∉ U → hmul y=0) ∧
      ∀ x, freeStalkChar B (h.free O) x =
        ∑ y, hmul y*freeStalkChar (O.sheaf y) (O.free y) x := by
  classical
  induction h with
  | zero =>
    refine ⟨0,by simp,by simp,?_⟩
    intro x
    simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
    exact ModuleData.char_zero _
  | @add B h c hc n d ih =>
    obtain ⟨m,hm,hsupp,heq⟩ := ih
    let a : Polynomial ℤ := ∑ i, X^(d i)
    have ha (r : ℕ) : 0 ≤ a.coeff r := by
      simp only [a,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
      exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
    refine ⟨fun y => m y+if y=c then a else 0,?_,?_,?_⟩
    · intro y r
      rw [Polynomial.coeff_add]
      apply add_nonneg (hm y r)
      split
      · exact ha r
      · simp
    · intro y hy
      have hne : y≠c := fun hh => hy (hh ▸ hc)
      simp [hsupp y hy,hne]
    · intro x
      let _ := h.free O x
      let _ := O.free c x
      change ((B.vertex x).prod (ModuleData.pi (fun i => ((O.sheaf c).vertex x).shift (d i)))).char = _
      rw [ModuleData.char_prod,ModuleData.char_pi]
      simp only [ModuleData.char_shift]
      change freeStalkChar B (h.free O) x + _ = _
      rw [heq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl

 theorem exists_stalkCharacter_decomposition [Fintype V] [Fintype E]
    {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x))
    (hq : B.UpperQuotient α) (hfl : B.forget.Flabby) (hg : B.forget.Generated) :
    ∃ hmul : V → Polynomial ℤ, (∀ y n, 0 ≤ (hmul y).coeff n) ∧
      ∀ x, freeStalkChar B hf x =
        ∑ y, hmul y*freeStalkChar (O.sheaf y) (O.free y) x := by
  obtain ⟨C,hC,⟨j⟩⟩ := exists_modelSumIso (polynomialGrading_zero k σ) O B hf hq hfl hg
  obtain ⟨m,hm,_,heq⟩ := hC.character O
  refine ⟨m,hm,fun x => ?_⟩
  rw [← heq x]
  let _ := hf x
  let _ := hC.free O x
  exact ModuleData.character_eq_of_gradedEquiv (j.vertex x)
    (j.vertex_graded x)

end
end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
