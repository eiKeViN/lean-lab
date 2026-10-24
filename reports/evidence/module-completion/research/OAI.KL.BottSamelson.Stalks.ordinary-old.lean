import Lean
import Mathlib
import ForMathlib.Algebra.Module.Free.ScalarDivisibility
import ForMathlib.Algebra.Module.Graded.HomogeneousEquiv
import ForMathlib.Algebra.Module.Graded.FinitePieces
import ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection
import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic
import ForMathlib.Algebra.Module.Graded.NonnegativeBasis
import ForMathlib.Algebra.Module.ReflectionPair.TensorKernel
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties
import ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal
import ForMathlib.LinearAlgebra.TensorProduct.Coordinates
import ForMathlib.RepresentationTheory.BottSamelson.TitsWords
import OAI.KL.Compatibility.KernelTransport

/-! Semantic home: OAI.KL.BottSamelson.Stalks. Source spans: BottSamelson:2, BottSamelson:4, BottSamelson:11, BottSamelson:5, BottSamelson:15, BottSamelson:6, BottSamelson:3, BottSamelson:21, BottSamelson:9, BottSamelson:13, BottSamelson:16, BottSamelson:19, BottSamelson:17, BottSamelson:22, BottSamelson:23, BottSamelson:29, BottSamelson:30, BottSamelson:26.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v up
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite
 theorem bottWeightProjection_range_le (i : I) (l : List I) (x : W)
    {P : Type up} [AddCommGroup P] [Module (SymmetricCoefficient (M := M)) P]
    (G : P →ₗ[SymmetricCoefficient (M := M)]
      ({e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M)))
    (h : ∀ n : BottSamelsonModule cs l,
      bottWeightProjection cs (i::l) x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n) ∈ LinearMap.range G) :
    LinearMap.range (bottWeightProjection cs (i::l) x) ≤ LinearMap.range G := by
  exact tensor_range_le_of_one_tmul (C := simpleFixed cs i)
    (A := SymmetricCoefficient (M := M)) (N := BottSamelsonModule cs l)
    (bottWeightProjection cs (i::l) x) G h
 theorem bottTensor_maps_eq (i : I) (l : List I)
    {P : Type up} [AddCommGroup P] [Module (SymmetricCoefficient (M := M)) P]
    (F G : BottSamelsonModule cs (i::l) →ₗ[SymmetricCoefficient (M := M)] P)
    (h : ∀ n : BottSamelsonModule cs l,
      F ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      G ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)) : F=G :=
  tensor_maps_eq_of_one_tmul (C := simpleFixed cs i)
    (A := SymmetricCoefficient (M := M)) (N := BottSamelsonModule cs l) F G h

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottFullIndex : (l : List I) → BottIndex l
  | [] => PUnit.unit
  | _::l => (1,bottFullIndex l)

omit [Fintype I] in
 theorem bottWeight_full (l : List I) :
    bottWeight cs l (bottFullIndex l)=cs.wordProd l := by
  induction l with
  | nil => exact cs.wordProd_nil.symm
  | cons i l ih =>
    simp only [bottFullIndex,bottWeight,show (1:Fin 2) ≠ 0 by decide,ite_false,
      cs.wordProd_cons,ih]

omit [Fintype I] in
 theorem bottSubword_length_eq_full (l : List I) (e : BottIndex l)
    (h : (bottSubword l e).length=l.length) : e=bottFullIndex l := by
  induction l with
  | nil =>
    change PUnit at e
    change e=(PUnit.unit : PUnit)
    exact Subsingleton.elim _ _
  | cons i l ih =>
    change Fin 2 × BottIndex l at e
    by_cases he : e.1=0
    · simp only [bottSubword,ite_eq_left he,List.length_cons] at h
      have hn := (bottSubword_sublist l e.2).length_le
      omega
    · have he1 : e.1=1 := by omega
      simp only [bottSubword,ite_eq_right he,List.length_cons] at h
      exact Prod.ext he1 (ih e.2 (Nat.succ.inj h))

omit [Fintype I] in
 theorem bottWeight_eq_top (l : List I) (hl : cs.IsReduced l) (e : BottIndex l)
    (he : bottWeight cs l e=cs.wordProd l) : e=bottFullIndex l := by
  apply bottSubword_length_eq_full
  apply Nat.le_antisymm (bottSubword_sublist l e).length_le
  have hh := cs.length_wordProd_le (bottSubword l e)
  rwa [bottSubword_wordProd,he,hl.eq] at hh

 def bottUnit : (l : List I) → BottSamelsonModule cs l
  | [] => (1 : SymmetricCoefficient (M := M))
  | i::l => 1 ⊗ₜ[simpleFixed cs i] bottUnit l

 theorem bottEvaluation_unit (l : List I) (e : BottIndex l) :
    bottEvaluation cs l e (bottUnit cs l)=1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change bottEvaluation cs (i::l) e (1 ⊗ₜ[simpleFixed cs i] bottUnit cs l)=1
    rw [bottEvaluation_tmul,ih]
    split_ifs <;> simp only [map_one,mul_one]

 theorem bottEvaluation_surjective (l : List I) (e : BottIndex l) :
    Function.Surjective (bottEvaluation cs l e) := by
  intro a
  refine ⟨a • bottUnit cs l,?_⟩
  rw [map_smul,bottEvaluation_unit,smul_eq_mul,mul_one]

 def bottTopCoordinate (l : List I) : bottStalk cs l (cs.wordProd l) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M) :=
  (LinearMap.proj ⟨bottFullIndex l,bottWeight_full cs l⟩).comp
    (bottStalk cs l (cs.wordProd l)).subtype

 theorem bottTopCoordinate_bijective (l : List I) (hl : cs.IsReduced l) :
    Function.Bijective (bottTopCoordinate cs l) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext e
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact hab
  · intro a
    obtain ⟨m,hm⟩ := bottEvaluation_surjective cs l (bottFullIndex l) a
    exact ⟨bottStalkProjection cs l (cs.wordProd l) m,hm⟩

 def bottTopStalkEquiv (l : List I) (hl : cs.IsReduced l) :
    bottStalk cs l (cs.wordProd l) ≃ₗ[SymmetricCoefficient (M := M)]
      SymmetricCoefficient (M := M) :=
  LinearEquiv.ofBijective (bottTopCoordinate cs l) (bottTopCoordinate_bijective cs l hl)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def bottHeadTail (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)] BottSamelsonModule cs l :=
  tensorFirst (C := simpleFixed cs i)

 def bottHeadReflectedTail (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)] Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (BottSamelsonModule cs l) :=
  tensorSecond (C := simpleFixed cs i) (coefficientAction cs (cs.simple i)).toRingEquiv
    (fun c => c.property)

 theorem bottHeadTail_seed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadTail cs i l ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=n := by
  exact one_smul _ n

 theorem bottHeadReflectedTail_seed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadReflectedTail cs i l ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=Twist.mk n := by
  change Twist.mk ((coefficientAction cs (cs.simple i)) 1 • n)=Twist.mk n
  rw [map_one,one_smul]

 def bottHeadLocalPair (i : I) (l : List I) (x : W) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)]
    (bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) :=
  ((bottStalkProjection cs l x).comp (bottHeadTail cs i l)).prod
    ((twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalkProjection cs l (cs.simple i*x))).comp (bottHeadReflectedTail cs i l))

 theorem bottHeadLocalPair_seed (i : I) (l : List I) (x : W) (n : BottSamelsonModule cs l) :
    bottHeadLocalPair cs i l x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      (bottStalkProjection cs l x n,Twist.mk (bottStalkProjection cs l (cs.simple i*x) n)) := by
  change ((bottStalkProjection cs l x) (bottHeadTail cs i l _),
    (twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalkProjection cs l (cs.simple i*x))) (bottHeadReflectedTail cs i l _)) = _
  rw [bottHeadTail_seed,bottHeadReflectedTail_seed]
  rfl
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottEvaluation_basis_homogeneous (l : List I) (e f : BottIndex l) :
    bottEvaluationMatrix cs l e f ∈ symmetricGrading basis (bottDegree l f) := by
  induction l with
  | nil =>
    change PUnit at e f
    change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) f) ∈
      symmetricGrading basis 0
    simp only [Basis.singleton_apply]
    exact SetLike.one_mem_graded _
  | cons i l ih =>
    change Fin 2 × BottIndex l at e f
    rcases e with ⟨r,j⟩
    rcases f with ⟨c,k⟩
    rw [bottEvaluationMatrix_cons]
    by_cases hc : c=0
    · subst c
      simp only [ite_true,bottDegree,Fin.val_zero,Nat.cast_zero,zero_add]
      split_ifs
      · exact ih j k
      · exact coefficientAction_homogeneous cs basis _ _ _ (ih j k)
    · have hc1 : c=1 := by omega
      subst c
      simp only [show (1:Fin 2) ≠ 0 by decide,ite_false,bottDegree,Fin.val_one,Nat.cast_one]
      split_ifs
      · exact SetLike.GradedMul.mul_mem (simpleRoot_homogeneous basis i) (ih j k)
      · exact SetLike.GradedMul.mul_mem ((symmetricGrading basis 1).neg_mem
          (simpleRoot_homogeneous basis i))
          (coefficientAction_homogeneous cs basis _ _ _ (ih j k))

 theorem bottEvaluation_homogeneous (l : List I) (e : BottIndex l)
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottEvaluation cs l e m ∈ symmetricGrading basis n := by
  classical
  have hexp : bottEvaluation cs l e m = ∑ f : BottIndex l,
      (bottBasis cs l).repr m f * bottEvaluationMatrix cs l e f := by
    conv_lhs => rw [← (bottBasis cs l).sum_repr m]
    simp only [map_sum,map_smul,smul_eq_mul,bottEvaluationMatrix]
  rw [hexp]
  apply Submodule.sum_mem
  intro f _
  change ∀ f, (bottBasis cs l).repr m f ∈
    symmetricGrading basis (n-bottDegree l f) at hm
  have h := SetLike.GradedMul.mul_mem (hm f)
    (bottEvaluation_basis_homogeneous cs basis l e f)
  simpa only [sub_add_cancel] using h

 theorem bottEvaluation_component (l : List I) (e : BottIndex l)
    (n : ℤ) (m : BottSamelsonModule cs l) :
    component (symmetricGrading basis) n (bottEvaluation cs l e m) =
      bottEvaluation cs l e (component (bottPiece cs basis l) n m) := by
  simpa only [sub_zero] using map_component (bottPiece cs basis l) (symmetricGrading basis)
    (bottEvaluation cs l e) 0 (by simpa only [add_zero] using bottEvaluation_homogeneous cs basis l e) n m

 theorem bottUnit_homogeneous (l : List I) : bottUnit cs l ∈ bottPiece cs basis l 0 := by
  have he : component (bottPiece cs basis l) 0 (bottUnit cs l)=bottUnit cs l := by
    apply bottEvaluation_injective cs l
    funext e
    change bottEvaluation cs l e (component (bottPiece cs basis l) 0 (bottUnit cs l)) =
      bottEvaluation cs l e (bottUnit cs l)
    rw [← bottEvaluation_component,bottEvaluation_unit]
    exact DirectSum.decompose_of_mem_same (symmetricGrading basis) (SetLike.one_mem_graded _)
  rw [← he]
  exact (DirectSum.decompose (bottPiece cs basis l) (bottUnit cs l) 0).property

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def BottKernelExact (l : List I) : Prop :=
  ∀ (x t : W) (a : I → ℝ), Represents M cs t a →
    cs.length x < cs.length (t*x) →
    ∀ m : BottSamelsonModule cs l, bottStalkProjection cs l x m=0 →
      ∃ z : bottStalk cs l (t*x), bottStalkProjection cs l (t*x) m=
        SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z

 theorem simple_represents (i : I) : Represents M cs (cs.simple i) (root i) := by
  refine ⟨1,i,?_,?_⟩
  · simp
  · simp

 theorem represents_polynomial_prime {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    Prime (SymmetricAlgebra.ι ℝ (Extended M) (embed M a)) := by
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact ha.isRoot.ne_zero (congrArg Prod.fst h)

 theorem represents_polynomial_not_dvd {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hne : t≠s) :
    ¬ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M b) := by
  rw [EdgeAlgebra.symmetric_ι_dvd_iff]
  intro h
  have hi := hb.extended_independent_of_ne ha (Ne.symm hne)
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp h
  exact (linearIndependent_fin2.mp hi).2 r hr

 theorem bottStalk_smul_injective (l : List I) (x : W)
    {r : SymmetricCoefficient (M := M)} (hr : r≠0) :
    Function.Injective (fun z : bottStalk cs l x => r • z) :=
  smul_right_injective (bottStalk cs l x) hr

 instance bottStalkFinite (l : List I) (x : W) :
    Module.Finite (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  Module.Finite.of_surjective (bottStalkProjection cs l x) (bottStalkProjection_surjective cs l x)

 theorem bottReflectionEdge_annihilated (l : List I) (x t : W) {a : I → ℝ}
    (ha : Represents M cs t a)
    (z : PairProjection.Edge (bottStalkProjection cs l x) (bottStalkProjection cs l (t*x))) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z=0 := by
  obtain ⟨p,hp⟩ := reflectionCoefficient_difference cs ha x
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs _ _) (bottStalkProjection_surjective cs _ _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs _ _ p) (bottStalkProjection_right cs _ _ p) z

 theorem BottKernelExact.upper_kernel {l : List I} (H : BottKernelExact cs l)
    (x t : W) {a : I → ℝ} (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (z : bottStalk cs l (t*x)) :
    PairProjection.upper (bottStalkProjection cs l x) (bottStalkProjection cs l (t*x)) z=0 ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w :=
  PairProjection.upper_kernel_of_divisibility _ _ _ (H x t a ha hlt)
    (bottReflectionEdge_annihilated cs l x t ha) z

 theorem BottKernelExact.kernel_iff {l : List I} (H : BottKernelExact cs l)
    (x t : W) {a : I → ℝ} (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (z : bottStalk cs l (t*x)) :
    (∃ m, bottStalkProjection cs l x m=0 ∧ bottStalkProjection cs l (t*x) m=z) ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  rw [← PairProjection.kernel_upper]
  exact H.upper_kernel cs x t ha hlt z

 theorem BottKernelExact.kernel_iff_of_mul {l : List I} (H : BottKernelExact cs l)
    (x y t : W) {a : I → ℝ} (ha : Represents M cs t a) (hxy : t*x=y)
    (hlt : cs.length x < cs.length y) (z : bottStalk cs l y) :
    (∃ m, bottStalkProjection cs l x m=0 ∧ bottStalkProjection cs l y m=z) ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  subst y
  exact H.kernel_iff cs x t ha hlt z

 theorem BottKernelExact.projection_of_mul {l : List I} (H : BottKernelExact cs l)
    (x y t : W) {a : I → ℝ} (ha : Represents M cs t a) (hxy : t*x=y)
    (hlt : cs.length x < cs.length y) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x m=0) :
    ∃ z : bottStalk cs l y, bottStalkProjection cs l y m=
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z := by
  subst y
  exact H x t a ha hlt m hm

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottCoordinatePiece (l : List I) (x : W) : ℤ → Submodule ℝ
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  piPiece (fun _ => symmetricGrading basis)

 instance bottCoordinatePiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottCoordinatePiece cs basis l x) := by
  classical
  exact (pi_isInternal (fun _ : {e : BottIndex l // bottWeight cs l e=x} =>
    symmetricGrading basis)).chooseDecomposition

 instance bottCoordinatePiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottCoordinatePiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (piPiece (fun _ : {e : BottIndex l // bottWeight cs l e=x} => symmetricGrading basis)))

 theorem bottWeightProjection_homogeneous (l : List I) (x : W) (n : ℤ)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottWeightProjection cs l x m ∈ bottCoordinatePiece cs basis l x n := by
  intro e _
  exact bottEvaluation_homogeneous cs basis l e.val n m hm

 theorem bottStalk_homogeneous (l : List I) (x : W) :
    ∀ n f, f ∈ bottStalk cs l x →
      component (bottCoordinatePiece cs basis l x) n f ∈ bottStalk cs l x := by
  exact range_homogeneous (bottPiece cs basis l) (bottCoordinatePiece cs basis l x)
    (bottWeightProjection cs l x) 0 (by
      simpa only [add_zero] using bottWeightProjection_homogeneous cs basis l x)

 def bottStalkPiece (l : List I) (x : W) : ℤ → Submodule ℝ (bottStalk cs l x) :=
  subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x)

 instance bottStalkPiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottStalkPiece cs basis l x) :=
  (sub_isInternal (bottCoordinatePiece cs basis l x) (bottStalk cs l x)
    (bottStalk_homogeneous cs basis l x)).chooseDecomposition

 instance bottStalkPiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottStalkPiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x)))

 theorem bottStalkProjection_homogeneous (l : List I) (x : W) (n : ℤ)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottStalkProjection cs l x m ∈ bottStalkPiece cs basis l x n :=
  bottWeightProjection_homogeneous cs basis l x n m hm

 theorem bottStalk_homogeneous_lift (l : List I) (x : W) (n : ℤ)
    (s : bottStalk cs l x) (hs : s ∈ bottStalkPiece cs basis l x n) :
    ∃ m : BottSamelsonModule cs l, m ∈ bottPiece cs basis l n ∧
      bottStalkProjection cs l x m=s := by
  obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x s
  refine ⟨component (bottPiece cs basis l) n m,
    (DirectSum.decompose (bottPiece cs basis l) m n).property,?_⟩
  have he := map_component (bottPiece cs basis l) (bottStalkPiece cs basis l x)
    (bottStalkProjection cs l x) 0 (by
      simpa only [add_zero] using bottStalkProjection_homogeneous cs basis l x) n m
  rw [sub_zero,hm,show component (bottStalkPiece cs basis l x) n s=s from
    DirectSum.decompose_of_mem_same _ hs] at he
  exact he.symm

 theorem bottWeightSupported_homogeneous (l : List I) (x : W) :
    ∀ n m, m ∈ bottWeightSupported cs l x →
      component (bottPiece cs basis l) n m ∈ bottWeightSupported cs l x := by
  intro n m hm e he
  rw [← bottEvaluation_component,hm e he,map_zero]

 def bottSupportPiece (l : List I) (x : W) :
    ℤ → Submodule ℝ (bottWeightSupported cs l x) :=
  subPiece (bottPiece cs basis l) (bottWeightSupported cs l x)

 instance bottSupportPiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottSupportPiece cs basis l x) :=
  (sub_isInternal (bottPiece cs basis l) (bottWeightSupported cs l x)
    (bottWeightSupported_homogeneous cs basis l x)).chooseDecomposition

 instance bottSupportPiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottSupportPiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (subPiece (bottPiece cs basis l) (bottWeightSupported cs l x)))

omit [Fintype σ] in
 theorem bottTopStalkEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) :
    bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis n ↔
      s ∈ bottStalkPiece cs basis l (cs.wordProd l) n := by
  constructor
  · intro h e _
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact h
  · intro h
    exact h ⟨bottFullIndex l,bottWeight_full cs l⟩ (Set.mem_univ _)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 omit [Fintype I] in
 theorem bottWeight_tail_zero (i : I) (l : List I) (x : W)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) (h : e.val.1=0) :
    bottWeight cs l e.val.2=x := by
  simpa only [bottWeight,ite_eq_left h] using e.property

 omit [Fintype I] in
 theorem bottWeight_tail_one (i : I) (l : List I) (x : W)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) (h : e.val.1≠0) :
    bottWeight cs l e.val.2=cs.simple i*x := by
  have he : cs.simple i*bottWeight cs l e.val.2=x := by
    simpa only [bottWeight,ite_eq_right h] using e.property
  simpa only [cs.simple_mul_simple_cancel_left] using (congrArg (cs.simple i * ·) he)

 def bottHeadPairCoordinates (i : I) (l : List I) (x : W) :
    (bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) →ₗ[SymmetricCoefficient (M := M)]
      ({e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M)) where
  toFun p e := if h : e.val.1=0 then
      p.1.val ⟨e.val.2,bottWeight_tail_zero cs i l x e h⟩
    else coefficientAction cs (cs.simple i)
      (p.2.val.val ⟨e.val.2,bottWeight_tail_one cs i l x e h⟩)
  map_add' p q := by
    funext e
    by_cases h : e.val.1=0
    · simp only [Pi.add_apply,dite_eq_left h]; rfl
    · simp only [Pi.add_apply,dite_eq_right h]
      exact map_add (coefficientAction cs (cs.simple i)) _ _
  map_smul' r p := by
    funext e
    dsimp
    split_ifs with h
    · rfl
    · change coefficientAction cs (cs.simple i)
        (coefficientAction cs (cs.simple i) r * _) = r * coefficientAction cs (cs.simple i) _
      rw [map_mul,simple_involutive]; rfl

 theorem bottHeadPairCoordinates_injective (i : I) (l : List I) (x : W) :
    Function.Injective (bottHeadPairCoordinates cs i l x) := by
  rintro ⟨p,q⟩ ⟨p',q'⟩ h
  apply Prod.ext
  · apply Subtype.ext
    funext e
    have hh := congrFun h ⟨(0,e.val),by simpa only [bottWeight,ite_true] using e.property⟩
    simpa only [bottHeadPairCoordinates,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_left rfl,dite_true] using hh
  · apply Twist.ext
    apply Subtype.ext
    funext e
    have he : bottWeight cs (i::l) (1,e.val)=x := by
      change (if (1 : Fin 2)=0 then _ else cs.simple i*bottWeight cs l e.val)=x
      rw [ite_eq_right (by decide),e.property,cs.simple_mul_simple_cancel_left]
    have hh := congrFun h ⟨(1,e.val),he⟩
    have hh' : coefficientAction cs (cs.simple i) (q.val.val e) =
        coefficientAction cs (cs.simple i) (q'.val.val e) := by
      simpa only [bottHeadPairCoordinates,LinearMap.coe_mk,AddHom.coe_mk,
        dite_eq_right (show (1 : Fin 2)≠0 by decide)] using hh
    exact (coefficientAction cs (cs.simple i)).injective hh'

 theorem simpleReverseDivisibility (i : I) (a : SymmetricCoefficient (M := M)) :
    simpleRootPolynomial (M := M) i ∣ coefficientAction cs (cs.simple i) a-a :=
  (dvd_sub_comm).mpr (simple_divisible cs i a)

 variable (i : I) (l : List I) (x : W)

 def bottHeadPairLattice := lattice (bottStalkProjection cs l x)
    (bottStalkProjection cs l (cs.simple i*x)) (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial (M := M) i) (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)

 instance bottHeadPairAddCommGroup : AddCommGroup (bottHeadPairLattice cs i l x) :=
  Submodule.addCommGroup (bottHeadPairLattice cs i l x)

 instance bottHeadPairModule : Module (SymmetricCoefficient (M := M)) (bottHeadPairLattice cs i l x) :=
  Submodule.module (bottHeadPairLattice cs i l x)

 theorem bottHeadPairCoordinates_seed (n : BottSamelsonModule cs l) :
    bottHeadPairCoordinates cs i l x
      (bottStalkProjection cs l x n,⟨bottStalkProjection cs l (cs.simple i*x) n⟩) =
    bottWeightProjection cs (i::l) x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n) := by
  funext e
  change (if h : e.val.1=0 then _ else _) = (1 : SymmetricCoefficient (M := M))*(if e.val.1=0 then _ else _)
  rw [one_mul]
  split_ifs <;> rfl

 def bottHeadPairToStalk : bottHeadPairLattice cs i l x →ₗ[
     SymmetricCoefficient (M := M)] bottStalk cs (i::l) x :=
  LinearMap.codRestrict (bottStalk cs (i::l) x)
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype) (by
      rintro ⟨⟨p,q⟩,n,hn,hn'⟩
      refine ⟨(1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n,?_⟩
      change bottWeightProjection cs (i::l) x _=bottHeadPairCoordinates cs i l x (p,q)
      rw [← bottHeadPairCoordinates_seed]
      congr 1
      exact Prod.ext hn (Twist.ext hn'))

 theorem bottHeadPairToStalk_injective : Function.Injective (bottHeadPairToStalk cs i l x) := by
  intro p q h
  apply Subtype.ext
  exact bottHeadPairCoordinates_injective cs i l x (congrArg Subtype.val h)

 theorem bottHeadPair_range :
    LinearMap.range (bottWeightProjection cs (i::l) x) ≤
      LinearMap.range ((bottHeadPairCoordinates cs i l x).comp
        (bottHeadPairLattice cs i l x).subtype) := by
  refine bottWeightProjection_range_le cs i l x (P := bottHeadPairLattice cs i l x)
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype) ?_
  intro n
  refine ⟨⟨(bottStalkProjection cs l x n,⟨bottStalkProjection cs l (cs.simple i*x) n⟩),n,rfl,rfl⟩,?_⟩
  exact bottHeadPairCoordinates_seed cs i l x n

 theorem bottHeadPairToStalk_surjective : Function.Surjective (bottHeadPairToStalk cs i l x) := by
  exact codRestrict_surjective_of_range_le (A := SymmetricCoefficient (M := M))
    (P := bottHeadPairLattice cs i l x)
    (V := {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M))
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype)
    (bottStalk cs (i::l) x) _ (bottHeadPair_range cs i l x)

 def bottHeadPairEquiv : bottHeadPairLattice cs i l x ≃ₗ[
     SymmetricCoefficient (M := M)] bottStalk cs (i::l) x :=
  LinearEquiv.ofBijective (bottHeadPairToStalk cs i l x)
    ⟨bottHeadPairToStalk_injective cs i l x,bottHeadPairToStalk_surjective cs i l x⟩

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

omit [Fintype σ] in
 theorem bottStalkPiece_negative (l : List I) (x : W) (n : ℤ) (hn : n<0) :
    bottStalkPiece cs basis l x n=⊥ := by
  apply subPiece_eq_bot
  exact piPiece_eq_bot (fun _ => symmetricGrading basis) n
    (fun _ => symmetricGrading_negative basis n hn)

 def bottStalkData (l : List I) (x : W) : ModuleData.{0,u,u} (symmetricGrading basis) where
  obj := ModuleCat.of _ (bottStalk cs l x)
  kModule := inferInstance
  tower := inferInstance
  piece := bottStalkPiece cs basis l x
  decomposition := inferInstance
  graded := inferInstance
  nonneg := bottStalkPiece_negative cs basis l x
  finite := Module.Finite.of_surjective (bottStalkProjection cs l x)
    (bottStalkProjection_surjective cs l x)

 theorem bottPiece_negative (l : List I) (n : ℤ) (hn : n<0) :
    bottPiece cs basis l n=⊥ := by
  apply bot_unique
  intro m hm
  change m=0
  apply bottEvaluation_injective cs l
  funext e
  have h := bottEvaluation_homogeneous cs basis l e n m hm
  rw [symmetricGrading_negative basis n hn,Submodule.mem_bot] at h
  exact h.trans (map_zero (bottEvaluation cs l e)).symm

 def bottWordData (l : List I) : ModuleData.{0,u,u} (symmetricGrading basis) where
  obj := ModuleCat.of _ (BottSamelsonModule cs l)
  kModule := inferInstance
  tower := inferInstance
  piece := bottPiece cs basis l
  decomposition := inferInstance
  graded := inferInstance
  nonneg := bottPiece_negative cs basis l
  finite := inferInstance

 def bottStalkHom (l : List I) (x : W) :
    ModuleData.Hom (bottWordData cs basis l) (bottStalkData cs basis l x) where
  map := bottStalkProjection cs l x
  graded := bottStalkProjection_homogeneous cs basis l x

 theorem bottStalkHom_surjective (l : List I) (x : W) :
    Function.Surjective (bottStalkHom cs basis l x).map :=
  bottStalkProjection_surjective cs l x

 def bottEdgeData (l : List I) (x y : W) : ModuleData.{0,u,u} (symmetricGrading basis) :=
  ModuleData.pairEdge (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottLowerHom (l : List I) (x y : W) :
    ModuleData.Hom (bottStalkData cs basis l x) (bottEdgeData cs basis l x y) :=
  ModuleData.pairLower (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottUpperHom (l : List I) (x y : W) :
    ModuleData.Hom (bottStalkData cs basis l y) (bottEdgeData cs basis l x y) :=
  ModuleData.pairUpper (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottGradedProjectionSheaf (l : List I) (u b : W) :
    GradedSheaf (𝓐 := symmetricGrading basis) (graph cs u b) where
  vertex x := bottStalkData cs basis l x.val
  edge e := bottEdgeData cs basis l (source cs u b e).val (target cs u b e).val
  lower e := bottLowerHom cs basis l (source cs u b e).val (target cs u b e).val
  upper e := bottUpperHom cs basis l (source cs u b e).val (target cs u b e).val

 theorem bottGradedProjectionSheaf_forget (l : List I) (u b : W) :
    (bottGradedProjectionSheaf cs basis l u b).forget=bottProjectionSheaf cs l u b := rfl

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottHeadLeft (i : I) (l : List I) (x : W) :
    bottStalk cs (i::l) x →ₗ[SymmetricCoefficient (M := M)] bottStalk cs l x :=
  (ReflectionPairTranslation.left (bottStalkProjection cs l x)
    (bottStalkProjection cs l (cs.simple i*x)) (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial (M := M) i) (simpleReverseDivisibility cs i)
    (bottSimpleEdge_kernel_inclusion cs i l x)).comp (bottHeadPairEquiv cs i l x).symm.toLinearMap

 def bottHeadRight (i : I) (l : List I) (x : W) :
    bottStalk cs (i::l) x →ₗ[ℝ] bottStalk cs l (cs.simple i*x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).toLinearMap.comp
    (((LinearMap.snd (SymmetricCoefficient (M := M)) (bottStalk cs l x)
      (Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottStalk cs l (cs.simple i*x)))).comp
        ((bottHeadPairLattice cs i l x).subtype.comp
          (bottHeadPairEquiv cs i l x).symm.toLinearMap)).restrictScalars ℝ)

 theorem bottHeadLeft_surjective (i : I) (l : List I) (x : W) :
    Function.Surjective (bottHeadLeft cs i l x) :=
  (left_surjective _ _ _ _ _ _ (bottStalkProjection_surjective cs l x)).comp
    (bottHeadPairEquiv cs i l x).symm.surjective

 theorem bottHeadPairEquiv_coordinates (i : I) (l : List I) (x : W)
    (m : bottStalk cs (i::l) x) :
    bottHeadPairCoordinates cs i l x ((bottHeadPairEquiv cs i l x).symm m).val=m.val :=
  congrArg Subtype.val ((bottHeadPairEquiv cs i l x).apply_symm_apply m)

omit [Fintype σ] in
 theorem bottHeadLeft_homogeneous (i : I) (l : List I) (x : W) (n : ℤ)
    (m : bottStalk cs (i::l) x) (hm : m ∈ bottStalkPiece cs basis (i::l) x n) :
    bottHeadLeft cs i l x m ∈ bottStalkPiece cs basis l x n := by
  intro e _
  change (bottHeadLeft cs i l x m).val e ∈ symmetricGrading basis n
  let E : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} :=
    ⟨(0,e.val),by simpa only [bottWeight,ite_true] using e.property⟩
  have he := congrFun (bottHeadPairEquiv_coordinates cs i l x m) E
  have hh : (bottHeadLeft cs i l x m).val e=m.val E := by
    change ((bottHeadPairEquiv cs i l x).symm m).val.1.val e=m.val E at he
    exact he
  rw [hh]
  exact hm E (Set.mem_univ E)

 theorem bottHeadRight_homogeneous (i : I) (l : List I) (x : W) (n : ℤ)
    (m : bottStalk cs (i::l) x) (hm : m ∈ bottStalkPiece cs basis (i::l) x n) :
    bottHeadRight cs i l x m ∈ bottStalkPiece cs basis l (cs.simple i*x) n := by
  intro e _
  change (bottHeadRight cs i l x m).val e ∈ symmetricGrading basis n
  let E : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} :=
    ⟨(1,e.val),by simp only [bottWeight,ite_eq_right (show (1:Fin 2)≠0 by decide),
      e.property,cs.simple_mul_simple_cancel_left]⟩
  have he := congrFun (bottHeadPairEquiv_coordinates cs i l x m) E
  have hh : coefficientAction cs (cs.simple i) ((bottHeadRight cs i l x m).val e)=m.val E := by
    change coefficientAction cs (cs.simple i)
      (((bottHeadPairEquiv cs i l x).symm m).val.2.val.val e)=m.val E at he
    exact he
  have h := coefficientAction_homogeneous cs basis (cs.simple i) n (m.val E)
    (hm E (Set.mem_univ E))
  rw [← hh,simple_involutive] at h
  exact h

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHeadLocalPair_coordinates (i : I) (l : List I) (x : W) :
    (bottHeadPairCoordinates cs i l x).comp (bottHeadLocalPair cs i l x) =
      bottWeightProjection cs (i::l) x := by
  apply bottTensor_maps_eq cs i l
  intro n
  change bottHeadPairCoordinates cs i l x (bottHeadLocalPair cs i l x _) = _
  rw [bottHeadLocalPair_seed,bottHeadPairCoordinates_seed]

 theorem bottHeadLocalPair_mem (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadLocalPair cs i l x m ∈ bottHeadPairLattice cs i l x := by
  exact linearMap_mem_of_coordinates (bottHeadPairLattice cs i l x)
    (bottHeadPairCoordinates cs i l x) (bottHeadLocalPair cs i l x)
    (bottWeightProjection cs (i::l) x) (bottHeadPairCoordinates_injective cs i l x)
    (bottHeadLocalPair_coordinates cs i l x) (bottHeadPair_range cs i l x) m

 theorem bottHeadLocalPair_zero_iff (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottStalkProjection cs (i::l) x m=0 ↔ bottHeadLocalPair cs i l x m=0 := by
  constructor
  · intro h
    apply bottHeadPairCoordinates_injective cs i l x
    rw [map_zero]
    have hh := congrArg Subtype.val h
    change bottWeightProjection cs (i::l) x m=0 at hh
    exact (LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m).trans hh
  · intro h
    apply Subtype.ext
    change bottWeightProjection cs (i::l) x m=0
    rw [← LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m]
    change bottHeadPairCoordinates cs i l x (bottHeadLocalPair cs i l x m)=0
    rw [h,map_zero]

 theorem bottHeadLocalPair_value (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadLocalPair cs i l x m =
      (bottStalkProjection cs l x (bottHeadTail cs i l m),
       Twist.mk (bottStalkProjection cs l (cs.simple i*x) (bottHeadReflectedTail cs i l m).val)) := rfl

 theorem bottHeadLocalPair_toStalk (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadPairToStalk cs i l x ⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ =
      bottStalkProjection cs (i::l) x m := by
  apply Subtype.ext
  exact LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m

 theorem bottHeadStalk_divisible_of_pair (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) (β : SymmetricCoefficient (M := M))
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x)))
    (hm : bottHeadLocalPair cs i l x m=β • p) (hp : p ∈ bottHeadPairLattice cs i l x) :
    ∃ z : bottStalk cs (i::l) x, bottStalkProjection cs (i::l) x m=β • z := by
  let z : bottHeadPairLattice cs i l x := ⟨p,hp⟩
  refine ⟨bottHeadPairToStalk cs i l x z,?_⟩
  have he : (⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ :
      bottHeadPairLattice cs i l x) = β • z := Subtype.ext hm
  calc
    bottStalkProjection cs (i::l) x m =
        bottHeadPairToStalk cs i l x ⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ :=
      (bottHeadLocalPair_toStalk cs i l x m).symm
    _ = bottHeadPairToStalk cs i l x (β • z) := congrArg (bottHeadPairToStalk cs i l x) he
    _ = β • bottHeadPairToStalk cs i l x z := map_smul _ _ _

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSimpleEdge_regular (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (β : SymmetricCoefficient (M := M)) (hβ : ¬simpleRootPolynomial (M := M) i ∣ β) :
    Function.Injective (fun e : PairProjection.Edge (bottStalkProjection cs l x)
      (bottStalkProjection cs l (cs.simple i*x)) => β • e) := by
  have hα : Prime (simpleRootPolynomial (M := M) i) :=
    represents_polynomial_prime cs (simple_represents cs i)
  rcases lt_or_gt_of_ne (cs.length_simple_mul_ne x i) with hdesc | hasc
  · let := F x
    apply FiniteFreeScalar.scalar_quotient_regular
      (Module.Free.chooseBasis (SymmetricCoefficient (M := M)) (bottStalk cs l x))
      (PairProjection.lower (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x)))
      (PairProjection.lower_surjective _ _ (bottStalkProjection_surjective cs l (cs.simple i*x)))
      (simpleRootPolynomial (M := M) i) β hα hβ
    intro z
    rw [PairProjection.kernel_lower]
    have hh := H.kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
      (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) hdesc z
    simpa only [and_comm,simpleRootPolynomial,extendedRoot] using hh
  · let := F (cs.simple i*x)
    exact FiniteFreeScalar.scalar_quotient_regular
      (Module.Free.chooseBasis (SymmetricCoefficient (M := M)) (bottStalk cs l (cs.simple i*x)))
      (PairProjection.upper (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x)))
      (PairProjection.upper_surjective _ _ (bottStalkProjection_surjective cs l x))
      (simpleRootPolynomial (M := M) i) β hα hβ
      (H.upper_kernel cs x (cs.simple i) (simple_represents cs i) hasc)

 theorem bottHeadPairLattice_saturated (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (β : SymmetricCoefficient (M := M)) (hβ : ¬simpleRootPolynomial (M := M) i ∣ β)
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) :
    β • p ∈ bottHeadPairLattice cs i l x ↔ p ∈ bottHeadPairLattice cs i l x :=
  lattice_saturated (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
    (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
    (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
    β (bottSimpleEdge_annihilated cs i l x) (bottSimpleEdge_regular cs i l H F x β hβ) p

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_free_cons (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) : Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs (i::l) x) := by
  let := F x
  let := F (cs.simple i*x)
  have hα : simpleRootPolynomial (M := M) i ≠ 0 :=
    (represents_polynomial_prime cs (simple_represents cs i)).ne_zero
  have hlattice : Module.Free (SymmetricCoefficient (M := M)) (bottHeadPairLattice cs i l x) := by
    rcases lt_or_gt_of_ne (cs.length_simple_mul_ne x i) with hdesc | hasc
    · apply lattice_free_right
        (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
        (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
        (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      · intro z
        have hh := H.kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
          (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) hdesc z
        simpa only [and_comm,simpleRootPolynomial,extendedRoot] using hh
      · exact bottStalkProjection_surjective cs l (cs.simple i*x)
      · exact bottStalk_smul_injective cs l x hα
    · exact lattice_free (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
        (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
        (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
        (H.kernel_iff cs x (cs.simple i) (simple_represents cs i) hasc)
        (bottStalkProjection_surjective cs l x)
        (bottStalk_smul_injective cs l (cs.simple i*x) hα)
  let := hlattice
  exact Module.Free.of_equiv (bottHeadPairEquiv cs i l x)

 theorem bottStalk_nil_subsingleton (x : W) (hx : x≠1) : Subsingleton (bottStalk cs [] x) := by
  constructor
  intro p q
  apply Subtype.ext
  funext e
  exact False.elim (hx e.property.symm)

 theorem bottStalk_nil_free (x : W) :
    Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs [] x) := by
  by_cases hx : x=1
  · subst x
    exact Module.Free.of_equiv (bottTopStalkEquiv cs [] (by simp [CoxeterSystem.IsReduced])).symm
  · let := bottStalk_nil_subsingleton cs x hx
    infer_instance

 theorem bottKernelExact_nil : BottKernelExact cs [] := by
  intro x t a ha hlt m hm
  have hx : t*x≠1 := by
    intro h
    rw [h] at hlt
    rw [cs.length_one] at hlt
    exact Nat.not_lt_zero _ hlt
  let := bottStalk_nil_subsingleton cs (t*x) hx
  exact ⟨0,Subsingleton.elim _ _⟩

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottHeadStalk_divisible (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (m : BottSamelsonModule cs (i::l)) (β : SymmetricCoefficient (M := M))
    (hβ : ¬simpleRootPolynomial (M := M) i ∣ β)
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x)))
    (hm : bottHeadLocalPair cs i l x m=β • p) :
    ∃ z : bottStalk cs (i::l) x, bottStalkProjection cs (i::l) x m=β • z := by
  have hp := bottHeadLocalPair_mem cs i l x m
  have hp' : β • p ∈ bottHeadPairLattice cs i l x := hm ▸ hp
  exact bottHeadStalk_divisible_of_pair cs i l x m β p hm
    ((bottHeadPairLattice_saturated cs i l H F x β hβ p).mp hp')

 theorem bottKernelExact_cons_nonhead (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x t : W) (a : I → ℝ) (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (hts : t≠cs.simple i)
    (m : BottSamelsonModule cs (i::l)) (hm : bottStalkProjection cs (i::l) x m=0) :
    ∃ z : bottStalk cs (i::l) (t*x), bottStalkProjection cs (i::l) (t*x) m=
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z := by
  have he : t*x≠cs.simple i*x := fun h => hts (mul_right_cancel h)
  have hstep : BruhatStep cs x (t*x) := ⟨hlt,t,ha.isReflection,rfl⟩
  have hstep' := bruhatStep_simple_mul cs hstep i he
  have hconj : (cs.simple i*t*(cs.simple i)⁻¹)*(cs.simple i*x)=cs.simple i*(t*x) := by group
  have hzero := (bottHeadLocalPair_zero_iff cs i l x m).mp hm
  have hμ : bottStalkProjection cs l x (bottHeadTail cs i l m)=0 := congrArg Prod.fst hzero
  have hν : bottStalkProjection cs l (cs.simple i*x) (bottHeadReflectedTail cs i l m).val=0 :=
    congrArg (fun p => p.2.val) hzero
  obtain ⟨p,hp⟩ := H x t a ha hlt (bottHeadTail cs i l m) hμ
  obtain ⟨q,hq⟩ := H.projection_of_mul cs (cs.simple i*x) (cs.simple i*(t*x))
    (cs.simple i*t*(cs.simple i)⁻¹) (ha.act (cs.simple i)) hconj hstep'.1
    (bottHeadReflectedTail cs i l m).val hν
  let β : SymmetricCoefficient (M := M) := SymmetricAlgebra.ι ℝ (Extended M) (embed M a)
  let p' : bottStalk cs l (t*x) × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*(t*x))) := (p,⟨q⟩)
  have hβ' : coefficientAction cs (cs.simple i) β =
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (action M cs (cs.simple i) a)) := by
    rw [coefficientAction_ι,extendedAction_restrict]
  have heq : bottHeadLocalPair cs i l (t*x) m=β • p' := by
    apply Prod.ext
    · exact hp
    · apply Twist.ext
      change bottStalkProjection cs l (cs.simple i*(t*x))
        (bottHeadReflectedTail cs i l m).val = coefficientAction cs (cs.simple i) β • q
      rw [hβ']
      exact hq
  have hn : ¬simpleRootPolynomial (M := M) i ∣ β :=
    represents_polynomial_not_dvd cs (simple_represents cs i) ha (Ne.symm hts)
  exact bottHeadStalk_divisible cs i l H F (t*x) m β hn p' heq

 theorem bottKernelExact_cons (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x)) :
    BottKernelExact cs (i::l) := by
  intro x t a ha hlt m hm
  by_cases hts : t=cs.simple i
  · subst t
    obtain ⟨z,hz⟩ := bottSimpleWall_kernel_projection cs i l x hm
    rcases ha.unique_up_to_sign (simple_represents cs i) with h|h
    · subst a
      exact ⟨z,hz⟩
    · subst a
      refine ⟨-z,?_⟩
      rw [hz]
      change simpleRootPolynomial (M := M) i • z =
        SymmetricAlgebra.ι ℝ (Extended M) (embed M (-root i)) • (-z)
      have he : embed M (-root i) = -embed M (root i) := by simp [embed]
      have hn : SymmetricAlgebra.ι ℝ (Extended M) (embed M (-root i)) =
          -simpleRootPolynomial (M := M) i := by
        rw [he]
        exact (SymmetricAlgebra.ι ℝ (Extended M)).map_neg _
      rw [hn]
      exact (neg_smul_neg _ z).symm
  · exact bottKernelExact_cons_nonhead cs i l H F x t a ha hlt hts m hm

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStandardStalks (l : List I) :
    BottKernelExact cs l ∧ ∀ x : W,
      Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x) := by
  induction l with
  | nil => exact ⟨bottKernelExact_nil cs,bottStalk_nil_free cs⟩
  | cons i l h => exact ⟨bottKernelExact_cons cs i l h.1 h.2,
      bottStalk_free_cons cs i l h.1 h.2⟩

 theorem bottKernelExact (l : List I) : BottKernelExact cs l := (bottStandardStalks cs l).1

 instance bottStalkFree (l : List I) (x : W) :
    Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  (bottStandardStalks cs l).2 x

 theorem bottProjectionSheaf_upper_kernel (l : List I) (u b : W) (e : Edge cs u b)
    {a : I → ℝ} (ha : Represents M cs (label cs u b e) a)
    (z : (bottProjectionSheaf cs l u b).vertex (target cs u b e)) :
    (bottProjectionSheaf cs l u b).upper e z=0 ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  change PairProjection.upper (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val) z=0 ↔ _
  exact (PairProjection.kernel_upper _ _ z).trans
    ((bottKernelExact cs l).kernel_iff_of_mul cs _ _ _ ha
      (label_mul_source cs u b e) e.property.1 z)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottHeadKernelEquiv (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) :
    bottStalk cs l (cs.simple i*x) ≃ₗ[ℝ] LinearMap.ker (bottHeadLeft cs i l x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).symm.trans
    (((kernelEquiv (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
      (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
      (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      ((bottKernelExact cs l).kernel_iff cs x (cs.simple i) (simple_represents cs i) h)
      (bottStalk_smul_injective cs l (cs.simple i*x) (simpleRootPolynomial_ne_zero i))).trans
      (kernelSourceEquiv _ (bottHeadPairEquiv cs i l x))).restrictScalars ℝ)

 theorem bottHeadKernelEquiv_eval (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x))
    (y : bottStalk cs l (cs.simple i*x))
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) :
    (bottHeadKernelEquiv cs i l x h y).val.val e=
      if he : e.val.1=0 then 0 else coefficientAction cs (cs.simple i)
        (simpleRootPolynomial (M := M) i * y.val ⟨e.val.2,bottWeight_tail_one cs i l x e he⟩) := rfl

 def bottHeadKernelPiece (i : I) (l : List I) (x : W) :
    ℤ → Submodule ℝ (LinearMap.ker (bottHeadLeft cs i l x)) :=
  subPiece (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadLeft cs i l x))

 theorem bottHeadLeft_kernel_homogeneous (i : I) (l : List I) (x : W) :
    ∀ n m, m ∈ LinearMap.ker (bottHeadLeft cs i l x) →
      component (bottStalkPiece cs basis (i::l) x) n m ∈ LinearMap.ker (bottHeadLeft cs i l x) := by
  intro n m hm
  have h := map_component (bottStalkPiece cs basis (i::l) x) (bottStalkPiece cs basis l x)
    (bottHeadLeft cs i l x) 0 (by
      intro j z hz
      simpa only [add_zero] using (bottHeadLeft_homogeneous cs basis i l x j z hz)) n m
  change bottHeadLeft cs i l x _=0
  rw [sub_zero] at h
  rw [← h,LinearMap.mem_ker.mp hm,map_zero]

 instance bottHeadKernelPiece_decomposition (i : I) (l : List I) (x : W) :
    DirectSum.Decomposition (bottHeadKernelPiece cs basis i l x) :=
  (sub_isInternal (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadLeft cs i l x))
    (bottHeadLeft_kernel_homogeneous cs basis i l x)).chooseDecomposition

 theorem bottHeadKernelEquiv_homogeneous (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) (n : ℤ)
    (y : bottStalk cs l (cs.simple i*x)) (hy : y ∈ bottStalkPiece cs basis l (cs.simple i*x) n) :
    bottHeadKernelEquiv cs i l x h y ∈ bottHeadKernelPiece cs basis i l x (n+1) := by
  intro e _
  change (bottHeadKernelEquiv cs i l x h y).val.val e ∈ symmetricGrading basis (n+1)
  rw [bottHeadKernelEquiv_eval]
  split_ifs with he
  · exact Submodule.zero_mem _
  · apply coefficientAction_homogeneous cs basis
    have hy' : y.val ⟨e.val.2,bottWeight_tail_one cs i l x e he⟩ ∈ symmetricGrading basis n :=
      hy ⟨e.val.2,bottWeight_tail_one cs i l x e he⟩ (Set.mem_univ _)
    have hp := SetLike.GradedMul.mul_mem (simpleRoot_homogeneous basis i) hy'
    simpa only [add_comm] using hp

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottPolynomialStalkData (l : List I) (x : W) :
    ModuleData.{0,u,u} (polynomialGrading ℝ σ) :=
  ModuleData.change (SymmetricAlgebra.equivMvPolynomial basis) (mem_symmetricGrading basis)
    (bottStalkData cs basis l x)

 instance bottPolynomialStalkFree (l : List I) (x : W) :
    Module.Free (MvPolynomial σ ℝ) (bottPolynomialStalkData cs basis l x) :=
  inferInstanceAs (Module.Free (MvPolynomial σ ℝ)
    (CoefficientChange (SymmetricAlgebra.equivMvPolynomial basis) (bottStalk cs l x)))

 def bottStalkCharacter (l : List I) (x : W) : Polynomial ℤ :=
  Graded.character (σ := σ) (bottPolynomialStalkData cs basis l x).piece
    (bottPolynomialStalkData cs basis l x).nonneg

 theorem bottPolynomialStalk_finrank (l : List I) (x : W) (n : ℤ) :
    Module.finrank ℝ ((bottPolynomialStalkData cs basis l x).piece n)=
      Module.finrank ℝ (bottStalkPiece cs basis l x n) :=
  LinearEquiv.finrank_map_eq
    (CoefficientChange.kEquiv (SymmetricAlgebra.equivMvPolynomial basis)
      (bottStalkData cs basis l x)) _

 theorem bottStalkCharacter_hasSum (l : List I) (x : W) {q : ℝ}
    (hq : 0<q) (hq1 : q<1) :
    HasSum (fun n : ℤ => (Module.finrank ℝ (bottStalkPiece cs basis l x n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q (bottStalkCharacter cs basis l x) *
        (1-q)⁻¹ ^ Fintype.card σ) := by
  have hh := (exists_nonnegativeBasis (k := ℝ) (σ := σ) (𝓜 := (bottPolynomialStalkData cs basis l x).piece)
    (bottPolynomialStalkData cs basis l x).nonneg).some.hasSum hq hq1
  apply hh.congr_fun
  intro n
  rw [bottPolynomialStalk_finrank]

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottHeadRight_surjective (i : I) (l : List I) (x : W) :
    Function.Surjective (bottHeadRight cs i l x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).surjective.comp
    ((right_surjective _ _ _ _ _ _ (bottStalkProjection_surjective cs l (cs.simple i*x))).comp
      (bottHeadPairEquiv cs i l x).symm.surjective)

 theorem bottDescentKernel (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (z : bottStalk cs l x) :
    (∃ n, bottStalkProjection cs l x n=z ∧ bottStalkProjection cs l (cs.simple i*x) n=0) ↔
      ∃ w, z=simpleRootPolynomial (M := M) i • w := by
  have hh := (bottKernelExact cs l).kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
    (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) h z
  simpa only [and_comm,simpleRootPolynomial,embed,extendedRoot] using hh

 def bottHeadRightKernelEquiv (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) :
    bottStalk cs l x ≃ₗ[ℝ] LinearMap.ker (bottHeadRight cs i l x) :=
  ((rightKernelEquiv (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
      (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
      (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      (bottDescentKernel cs i l x h)
      (bottStalk_smul_injective cs l x (simpleRootPolynomial_ne_zero i))).restrictScalars ℝ).trans
    (kernelMixedEquiv _ (bottHeadPairEquiv cs i l x)
      (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _))

 theorem bottHeadRightKernelEquiv_eval (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (y : bottStalk cs l x)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) :
    (bottHeadRightKernelEquiv cs i l x h y).val.val e=
      if he : e.val.1=0 then simpleRootPolynomial (M := M) i *
        y.val ⟨e.val.2,bottWeight_tail_zero cs i l x e he⟩ else 0 := by
  change (if he : e.val.1=0 then _ else coefficientAction cs (cs.simple i) 0)=_
  split_ifs
  · rfl
  · exact map_zero _

 def bottHeadRightKernelPiece (i : I) (l : List I) (x : W) :
    ℤ → Submodule ℝ (LinearMap.ker (bottHeadRight cs i l x)) :=
  subPiece (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadRight cs i l x))

 theorem bottHeadRight_kernel_homogeneous (i : I) (l : List I) (x : W) :
    ∀ n m, m ∈ LinearMap.ker (bottHeadRight cs i l x) →
      component (bottStalkPiece cs basis (i::l) x) n m ∈ LinearMap.ker (bottHeadRight cs i l x) := by
  exact kernel_homogeneous (A := ℝ) (bottStalkPiece cs basis (i::l) x)
    (bottStalkPiece cs basis l (cs.simple i*x)) (bottHeadRight cs i l x) 0 (by
      intro j z hz
      simpa only [add_zero] using (bottHeadRight_homogeneous cs basis i l x j z hz))

 instance bottHeadRightKernelPiece_decomposition (i : I) (l : List I) (x : W) :
    DirectSum.Decomposition (bottHeadRightKernelPiece cs basis i l x) :=
  (sub_isInternal (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadRight cs i l x))
    (bottHeadRight_kernel_homogeneous cs basis i l x)).chooseDecomposition

 theorem bottHeadRightKernelEquiv_homogeneous (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (n : ℤ)
    (y : bottStalk cs l x) (hy : y ∈ bottStalkPiece cs basis l x n) :
    bottHeadRightKernelEquiv cs i l x h y ∈ bottHeadRightKernelPiece cs basis i l x (n+1) := by
  intro e _
  change (bottHeadRightKernelEquiv cs i l x h y).val.val e ∈ symmetricGrading basis (n+1)
  rw [bottHeadRightKernelEquiv_eval]
  split_ifs with he
  · have hy' : y.val ⟨e.val.2,bottWeight_tail_zero cs i l x e he⟩ ∈ symmetricGrading basis n :=
      hy ⟨e.val.2,bottWeight_tail_zero cs i l x e he⟩ (Set.mem_univ _)
    have hp := SetLike.GradedMul.mul_mem (simpleRoot_homogeneous basis i) hy'
    simpa only [add_comm] using hp
  · exact Submodule.zero_mem _

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance symmetricGrading_finite (n : ℤ) : Module.Finite ℝ (symmetricGrading basis n) :=
  inferInstanceAs (Module.Finite ℝ ((polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap))

 instance bottCoordinatePiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottCoordinatePiece cs basis l x n) := by
  classical
  exact piPiece_finite _ n

 instance bottStalkPiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottStalkPiece cs basis l x n) :=
  inferInstanceAs (Module.Finite ℝ (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x) n))

 theorem bottStalk_finrank_ascent (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) (n : ℤ) :
    Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
      Module.finrank ℝ (bottStalkPiece cs basis l x n)+
      Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) (n-1)) := by
  have hdim := Hilbert.finrank_exact (bottStalkPiece cs basis (i::l) x)
    (bottStalkPiece cs basis l x) (bottHeadLeft cs i l x)
    (bottHeadLeft_homogeneous cs basis i l x) (bottHeadLeft_surjective cs i l x) n
  have hk := finrank_homogeneousEquiv (k := ℝ)
    (N := LinearMap.ker (bottHeadLeft cs i l x)) (bottStalkPiece cs basis l (cs.simple i*x))
    (bottHeadKernelPiece cs basis i l x) (bottHeadKernelEquiv cs i l x h) 1
    (bottHeadKernelEquiv_homogeneous cs basis i l x h) n
  change Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
    Module.finrank ℝ (bottHeadKernelPiece cs basis i l x n)+
      Module.finrank ℝ (bottStalkPiece cs basis l x n) at hdim
  rw [hk] at hdim
  omega

end
end KLInvariance.TitsSpace
end

end OAI

open Lean
namespace BoundaryCodec
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => toJson (#[nameJson p, toJson s])
  | .num p n => toJson (#[nameJson p, toJson n, Json.null])
partial def levelJson : Level → Json
  | .zero => toJson (#[toJson "zero"])
  | .succ u => toJson (#[toJson "succ", levelJson u])
  | .max u v => toJson (#[toJson "max", levelJson u, levelJson v])
  | .imax u v => toJson (#[toJson "imax", levelJson u, levelJson v])
  | .param n => toJson (#[toJson "param", nameJson n])
  | .mvar _ => panic! "unclosed level"
structure Dump where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def encode (e : Expr) : StateM Dump Nat := do
  if let .mdata _ b := e then return ← encode b
  if let some i := (← get).ids[ExprStructEq.mk e]? then return i
  let node : Array Json ← match e with
    | .bvar n => pure #[toJson "bvar", toJson n]
    | .sort u => pure #[toJson "sort", levelJson u]
    | .const n us => pure #[toJson "const", nameJson n, toJson (us.map levelJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi | .forallE n t b bi => do
      let tag := if e.isLambda then "lam" else "forall"
      let bi := match bi with | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
      pure #[toJson tag, nameJson n, toJson (← encode t), toJson (← encode b), toJson bi]
    | .letE n t v b nondep => do pure #[toJson "let", nameJson n, toJson (← encode t), toJson (← encode v), toJson (← encode b), toJson nondep]
    | .lit (.natVal n) => pure #[toJson "nat", toJson n]
    | .lit (.strVal s) => pure #[toJson "str", toJson s]
    | .proj n i b => do pure #[toJson "proj", nameJson n, toJson i, toJson (← encode b)]
    | _ => panic! "unclosed expression"
  let s ← get
  set ({ids := s.ids.insert (ExprStructEq.mk e) s.nodes.size, nodes := s.nodes.push (toJson node)} : Dump)
  return s.nodes.size
partial def readName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size == 2 then return .str (← readName a[0]!) (← a[1]!.getStr?)
  if a.size == 3 then return .num (← readName a[0]!) (← fromJson? a[1]!)
  throw "bad name"
partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => do pure (.zero)
  | "succ" => do pure (.succ (← readLevel a[1]!))
  | "max" => do pure (.max (← readLevel a[1]!) (← readLevel a[2]!))
  | "imax" => do pure (.imax (← readLevel a[1]!) (← readLevel a[2]!))
  | "param" => do pure (.param (← readName a[1]!))
  | _ => throw "bad level"
def decode (nodes : Array Json) : Except String (Array Expr) := do
  let mut es := #[]
  for j in nodes do
    let a ← j.getArr?
    let child := fun (i : Nat) => (show Except String Expr from do
      let n : Nat ← fromJson? a[i]!
      if n < es.size then return es[n]! else throw "non-topological DAG")
    let e : Expr ← match ← a[0]!.getStr? with
      | "bvar" => do pure (.bvar (← fromJson? a[1]!))
      | "sort" => do pure (.sort (← readLevel a[1]!))
      | "const" => do pure (.const (← readName a[1]!) (← (← a[2]!.getArr?).toList.mapM readLevel))
      | "app" => do pure (.app (← child 1) (← child 2))
      | "lam" | "forall" => do
        let bi : Nat ← fromJson? a[4]!
        let bi ← match bi with | 0 => pure BinderInfo.default | 1 => pure .implicit | 2 => pure .strictImplicit | 3 => pure .instImplicit | _ => throw "bad binder"
        if (← a[0]!.getStr?) == "lam" then pure (.lam (← readName a[1]!) (← child 2) (← child 3) bi)
        else pure (.forallE (← readName a[1]!) (← child 2) (← child 3) bi)
      | "let" => do pure (.letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← fromJson? a[5]!))
      | "nat" => do pure (.lit (.natVal (← fromJson? a[1]!)))
      | "str" => do pure (.lit (.strVal (← fromJson? a[1]!)))
      | "proj" => do pure (.proj (← readName a[1]!) (← fromJson? a[2]!) (← child 3))
      | _ => throw "bad expression"
    es := es.push e
  return es
end BoundaryCodec

open Lean Meta Elab Command BoundaryCodec
run_elab do
  let names : Array Name := #[`OAI.KLInvariance.TitsSpace.bottHeadPairCoordinates.eq_1]
  let env := (← Lean.getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending : Array Name := names
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson (Lean.defeqAttr.hasTag env n), toJson (Lean.backwardDefeqAttr.hasTag env n)])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/OAI.KL.BottSamelson.Stalks.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."

open Lean

structure TypeDumpState where
  ids : ExprStructMap Nat := {}
  proofIds : ExprStructMap Nat := {}
  next : Nat := 0
  privateOwners : Std.HashMap Name Name := {}
  proofAliases : NameHashSet := {}
  unrenamed : NameHashSet := {}

-- Alpha equivalence ignores binder display names. Only compiler-private OAI
-- owner prefixes are erased from constant names; their user names stay exact.
-- There are no duplicate private user names in the pinned source.
private def canonicalConstant (n : Name) : Name :=
  if n.toString.startsWith "_private.OAI." then
    (privateToUserName? n).getD n
  else n

-- Keep every mathematical expression constructor, universe, binder info,
-- constant, application and de Bruijn index. Metadata and binder display names
-- have no effect on the mathematical type. A local compiler theorem auxiliary
-- is represented by its full proposition, using kernel proof irrelevance.
-- No proof body, general definition, data instance or user theorem is unfolded.
partial def dumpType (env : Environment) (out : IO.FS.Handle) (e : Expr)
    (proofContext := false) : StateT TypeDumpState IO Nat := do
  let cached : TypeDumpState ← get
  let cache := if proofContext then cached.proofIds else cached.ids
  if let some id := cache[ExprStructEq.mk e]? then return id
  if let .mdata _ body := e then return ← dumpType env out body proofContext
  let fields ← match e with
    | .bvar i => pure ["bvar", toString i]
    | .sort u => pure ["sort", reprStr u]
    | .const n us =>
      let proofName := match n with
        | .str _ s => s.startsWith "_proof_"
        | _ => false
      if n.isInternal && n.toString.startsWith "OAI." && proofName then
        if let some (.thmInfo info) := env.find? n then
          -- Kernel theorem declarations prove propositions. Their full
          -- proposition, including parameters, is retained; only its binder
          -- display/implicitness metadata is irrelevant to the proof value.
          let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
          modify fun st => { st with proofAliases := st.proofAliases.insert n }
          pure ["proof", toString proposition]
        else pure ["const", reprStr n, reprStr us]
      else
        let canonical := canonicalConstant n
        if canonical != n then
          if env.contains canonical then
            throw <| IO.userError "Private canonical name collides with an unrenamed global constant"
          if let some previous := (← get).privateOwners[canonical]? then
            if previous != n then throw <| IO.userError "Ambiguous private type constant"
          modify fun st => { st with privateOwners := st.privateOwners.insert canonical n }
        pure ["const", reprStr canonical, reprStr us]
    | .app f a => do
      let f ← dumpType env out f proofContext; let a ← dumpType env out a proofContext
      pure ["app", toString f, toString a]
    | .lam _ t b bi | .forallE _ t b bi => do
      let t ← dumpType env out t proofContext; let b ← dumpType env out b proofContext
      pure [if e.isLambda then "lam" else "forall", "_", if proofContext then "kernel" else reprStr bi, toString t, toString b]
    | .letE _ t v b nondep => do
      let t ← dumpType env out t proofContext; let v ← dumpType env out v proofContext; let b ← dumpType env out b proofContext
      pure ["let", "_", toString t, toString v, toString b, toString nondep]
    | .lit v => pure ["lit", reprStr v]
    | .proj n i b => do
      let b ← dumpType env out b proofContext
      pure ["proj", reprStr n, toString i, toString b]
    | .fvar _ | .mvar _ => throw <| IO.userError "Non-closed declaration type"
    | .mdata _ _ => unreachable!
  match e with
  | .const n _ =>
    if fields.head! == "const" && canonicalConstant n == n then
      modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | .proj n _ _ => modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | _ => pure ()
  let state : TypeDumpState ← get
  if proofContext then
    set { state with proofIds := state.proofIds.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  else
    set { state with ids := state.ids.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  out.putStrLn s!"NODE\t{state.next}\t{(toJson fields).compress}"
  return state.next

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

-- This experiment accepts duplicate serialized theorem records only.
-- Other ConstantInfo variants fail closed; their safety/hints are not omitted
-- from a purported full-record comparison. ExprStructEq retains binder names
-- and annotations, unlike BEq Expr (Expr.eqv).
private def sameSerializedTheorem (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams &&
      ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
      ExprStructEq.mk a.value == ExprStructEq.mk b.value && a.all == b.all
  | _, _ => false


run_elab do
  let env := (← Lean.getEnv).setExporting false
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/OAI.KL.BottSamelson.Stalks.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.TitsSpace.bottHeadPairCoordinates.eq_1] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tOAI.KL.BottSamelson.Stalks"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t1\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
