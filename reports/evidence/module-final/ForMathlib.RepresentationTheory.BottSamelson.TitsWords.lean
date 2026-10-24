import Lean
import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic
import ForMathlib.GroupTheory.Coxeter.Bruhat.Descent
import ForMathlib.GroupTheory.Coxeter.Roots.Basic
import ForMathlib.LinearAlgebra.Dual.Frobenius
import ForMathlib.LinearAlgebra.PairProjection

/-! Semantic home: ForMathlib.RepresentationTheory.BottSamelson.TitsWords. Source spans: Frobenius:1, Frobenius:6, Frobenius:20, Frobenius:13, Frobenius:15, Frobenius:23, Frobenius:16, Frobenius:18, Frobenius:24, Frobenius:19, Frobenius:21, Frobenius:22, Frobenius:25, Frobenius:27.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 abbrev SymmetricCoefficient := SymmetricAlgebra ℝ (Extended M)

 def coefficientAction (w : W) : SymmetricCoefficient (M := M) ≃ₐ[ℝ]
    SymmetricCoefficient (M := M) := symmetricAction (extendedAction M cs w)

@[simp] theorem coefficientAction_ι (w : W) (v : Extended M) :
    coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) v) =
      SymmetricAlgebra.ι ℝ (Extended M) (extendedAction M cs w v) :=
  symmetricAction_ι _ _

 theorem coefficientAction_simple (i : I) : coefficientAction cs (cs.simple i) =
    reflectionAction (extendedRoot M i) (extendedForm M (extendedRoot M i))
      (extendedForm_root_self M i) := by
  rw [coefficientAction,extendedAction_simple_eq]

 theorem coefficientAction_mul (w z : W) (a : SymmetricCoefficient (M := M)) :
    coefficientAction cs (w*z) a = coefficientAction cs w (coefficientAction cs z a) := by
  have he : (coefficientAction cs (w*z)).toAlgHom =
      (coefficientAction cs w).toAlgHom.comp (coefficientAction cs z).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change coefficientAction cs (w*z) (SymmetricAlgebra.ι ℝ (Extended M) x) =
      coefficientAction cs w (coefficientAction cs z (SymmetricAlgebra.ι ℝ (Extended M) x))
    simp only [coefficientAction_ι,map_mul,LinearEquiv.mul_apply]
  exact congrArg (fun f : SymmetricCoefficient (M := M) →ₐ[ℝ] SymmetricCoefficient (M := M) => f a) he

 def simpleFixed (i : I) : Subalgebra ℝ (SymmetricCoefficient (M := M)) :=
  fixed (coefficientAction cs (cs.simple i))

 abbrev simpleRootPolynomial (i : I) : SymmetricCoefficient (M := M) :=
  SymmetricAlgebra.ι ℝ (Extended M) (extendedRoot M i)

 theorem simple_involutive (i : I) : Function.Involutive (coefficientAction cs (cs.simple i)) := by
  rw [coefficientAction_simple]
  exact reflectionAction_involutive _ _ _

 theorem simpleRootPolynomial_ne_zero (i : I) : simpleRootPolynomial (M := M) i ≠ 0 :=
  reflectionRoot_ne_zero _ _ (extendedForm_root_self M i)

 theorem simple_anti (i : I) : coefficientAction cs (cs.simple i)
    (simpleRootPolynomial (M := M) i) = -simpleRootPolynomial (M := M) i := by
  rw [coefficientAction_simple]
  exact reflectionAction_anti _ _ _

 theorem simple_divisible (i : I) (a : SymmetricCoefficient (M := M)) :
    simpleRootPolynomial (M := M) i ∣ a-coefficientAction cs (cs.simple i) a := by
  rw [coefficientAction_simple]
  exact reflectionAction_divisible _ _ _ a

 def simpleCoordinates (i : I) : SymmetricCoefficient (M := M) ≃ₗ[simpleFixed cs i]
    (simpleFixed cs i × simpleFixed cs i) :=
  coordinates _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 instance simpleFixed_free (i : I) : Module.Free (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  Module.Free.of_equiv (simpleCoordinates cs i).symm

 instance simpleFixed_finite (i : I) : Module.Finite (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  Module.Finite.equiv (simpleCoordinates cs i).symm

 def simpleTrace (i : I) : SymmetricCoefficient (M := M) →ₗ[simpleFixed cs i] simpleFixed cs i :=
  trace _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 def simpleDuality (i : I) : SymmetricCoefficient (M := M) ≃ₗ[simpleFixed cs i]
    Dual (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  duality _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 theorem simpleDuality_apply (i : I) (a b : SymmetricCoefficient (M := M)) :
    simpleDuality cs i a b = simpleTrace cs i (a*b) :=
  duality_apply _ _ _ _ _ _ a b

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSamelson : List I → PairedBimodule.{u,u} (SymmetricCoefficient (M := M))
  | [] => unitBimodule _
  | i :: l => inducedBimodule (simpleTrace cs i) (simpleDuality cs i)
    (simpleDuality_apply cs i) (bottSamelson l)

 abbrev BottSamelsonModule (l : List I) := (bottSamelson cs l).obj

 def bottSamelsonDuality (l : List I) : BottSamelsonModule cs l ≃ₗ[SymmetricCoefficient (M := M)]
    Dual (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSamelson cs l).obj.pairing

 def bottSamelsonRight (l : List I) : SymmetricCoefficient (M := M) →+*
    End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSamelson cs l).right

 theorem bottSamelson_balanced (l : List I) (a : SymmetricCoefficient (M := M))
    (m n : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l (bottSamelsonRight cs l a m) n =
      bottSamelsonDuality cs l m (bottSamelsonRight cs l a n) :=
  (bottSamelson cs l).balanced a m n

 theorem bottSamelson_symmetric (l : List I) (m n : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l m n = bottSamelsonDuality cs l n m :=
  (bottSamelson cs l).symmetric m n

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem symmetricCoefficient_ι_injective :
    Function.Injective (SymmetricAlgebra.ι ℝ (Extended M)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℝ (x-y)).mp
  intro f
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he := congrArg (SymmetricAlgebra.lift f) h
  simpa only [SymmetricAlgebra.lift_ι_apply] using he

 theorem coefficientAction_injective : Function.Injective (coefficientAction cs) := by
  intro x y h
  apply extendedAction_injective M cs
  apply LinearEquiv.ext
  intro v
  apply symmetricCoefficient_ι_injective (M := M)
  have he := congrArg (fun g : SymmetricCoefficient (M := M) ≃ₐ[ℝ]
    SymmetricCoefficient (M := M) => g (SymmetricAlgebra.ι ℝ (Extended M) v)) h
  simpa only [coefficientAction_ι] using he

 theorem coefficientAction_separates {x y : W} (hxy : x ≠ y) :
    ∃ a : SymmetricCoefficient (M := M), coefficientAction cs x a ≠ coefficientAction cs y a := by
  by_contra! h
  apply hxy
  apply coefficientAction_injective cs
  exact AlgEquiv.ext h

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionFrobenius
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def symmetricGrading : ℤ → Submodule ℝ (SymmetricCoefficient (M := M)) :=
  fun n => (polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap

omit [Fintype σ] in
 theorem mem_symmetricGrading (n : ℤ) (a : SymmetricCoefficient (M := M)) :
    a ∈ symmetricGrading basis n ↔
      SymmetricAlgebra.equivMvPolynomial basis a ∈ polynomialGrading ℝ σ n := by
  constructor
  · rintro ⟨p,hp,hpa⟩
    rw [← hpa]
    simpa using hp
  · intro h
    exact ⟨_,h,(SymmetricAlgebra.equivMvPolynomial basis).symm_apply_apply a⟩

 instance symmetricGrading_decomposition : DirectSum.Decomposition (symmetricGrading basis) := by
  apply DirectSum.IsInternal.chooseDecomposition
  apply image_isInternal (polynomialGrading ℝ σ)
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap
    (SymmetricAlgebra.equivMvPolynomial basis).symm.surjective
  intro n p hp
  have hz : p=0 := (SymmetricAlgebra.equivMvPolynomial basis).symm.injective
    (by simpa using hp)
  subst p
  simp

 instance symmetricGrading_graded : SetLike.GradedMonoid (symmetricGrading basis) where
  one_mem := (mem_symmetricGrading basis 0 1).mpr (by
    rw [map_one]
    exact SetLike.one_mem_graded (polynomialGrading ℝ σ))
  mul_mem := by
    intro n m a b ha hb
    apply (mem_symmetricGrading basis (n+m) (a*b)).mpr
    rw [map_mul]
    exact SetLike.GradedMul.mul_mem ((mem_symmetricGrading basis n a).mp ha)
      ((mem_symmetricGrading basis m b).mp hb)

omit [Fintype σ] in
 theorem symmetricGrading_negative (n : ℤ) (hn : n<0) :
    symmetricGrading basis n = ⊥ := by
  simp [symmetricGrading,polynomialGrading_negative ℝ σ n hn]

 theorem simpleRoot_homogeneous (i : I) :
    simpleRootPolynomial (M := M) i ∈ symmetricGrading basis 1 := by
  apply (mem_symmetricGrading basis 1 _).mpr
  exact polynomialLinear_homogeneous basis _

 theorem coefficientAction_homogeneous (w : W) (n : ℤ)
    (a : SymmetricCoefficient (M := M)) (ha : a ∈ symmetricGrading basis n) :
    coefficientAction cs w a ∈ symmetricGrading basis n := by
  apply (mem_symmetricGrading basis n _).mpr
  have h := polynomialAction_homogeneous basis (extendedAction M cs w)
    ((mem_symmetricGrading basis n a).mp ha)
  simpa only [polynomialAction,AlgEquiv.trans_apply,AlgEquiv.symm_apply_apply,
    coefficientAction] using h

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
open _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def BottIndex : List I → Type u
  | [] => PUnit
  | _ :: l => Fin 2 × BottIndex l

 instance bottIndex_fintype : (l : List I) → Fintype (BottIndex l)
  | [] => inferInstanceAs (Fintype PUnit)
  | _ :: l => by
      let _ := bottIndex_fintype l
      exact inferInstanceAs (Fintype (Fin 2 × BottIndex l))

 def bottDegree : (l : List I) → BottIndex l → ℤ
  | [], _ => 0
  | _ :: l, e => e.1.val + bottDegree l e.2

omit [Fintype I] in
 theorem bottDegree_nonneg (l : List I) (e : BottIndex l) : 0 ≤ bottDegree l e := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact add_nonneg (Int.natCast_nonneg _) (ih e.2)

 def bottBasis : (l : List I) → Basis (BottIndex l) (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l)
  | [] => Basis.singleton PUnit _
  | i :: l => by
      let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
        simpleFixed_free cs i
      let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
        simpleFixed_finite cs i
      exact inducedBasis (coefficientAction cs (cs.simple i))
        (simpleRootPolynomial i) (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
        (simple_anti cs i) (simple_divisible cs i) (bottSamelson cs l).obj (bottBasis l)

 theorem bottBasis_pairing_homogeneous (l : List I) (e f : BottIndex l) :
    bottSamelsonDuality cs l (bottBasis cs l e) (bottBasis cs l f) ∈
      symmetricGrading basis (bottDegree l e+bottDegree l f-l.length) := by
  induction l with
  | nil =>
    change PUnit at e f
    change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) e) *
      (Basis.singleton PUnit (SymmetricCoefficient (M := M)) f) ∈ symmetricGrading basis 0
    simp only [Basis.singleton_apply, one_mul]
    exact SetLike.one_mem_graded _
  | cons i l ih =>
    change (Fin 2 × BottIndex l) at e f
    rcases e with ⟨ei, ej⟩
    rcases f with ⟨fi, fj⟩
    let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
      simpleFixed_free cs i
    let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
      simpleFixed_finite cs i
    have h := inducedPairing_basis_homogeneous
      (coefficientAction cs (cs.simple i)) (simpleRootPolynomial i)
      (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
      (simple_anti cs i) (simple_divisible cs i) (bottSamelson cs l).obj
      (bottBasis cs l) (symmetricGrading basis) (simpleRoot_homogeneous basis i)
      (coefficientAction_homogeneous cs basis (cs.simple i))
      (bottDegree l) l.length ih ei fi ej fj
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,bottDegree]
    convert h using 1; rfl

 instance bottRealModule (l : List I) : Module ℝ (BottSamelsonModule cs l) :=
  Module.compHom _ (algebraMap ℝ (SymmetricCoefficient (M := M)))

 instance bottRealTower (l : List I) :
    IsScalarTower ℝ (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

 def bottPiece (l : List I) : ℤ → Submodule ℝ (BottSamelsonModule cs l) :=
  basisPiece (symmetricGrading basis) (bottBasis cs l) (bottDegree l)

 instance bottPiece_decomposition (l : List I) : DirectSum.Decomposition (bottPiece cs basis l) :=
  basisPiece_decomposition _ _ _

 instance bottPiece_graded (l : List I) :
    SetLike.GradedSMul (symmetricGrading basis) (bottPiece cs basis l) :=
  basisPiece_graded _ _ _

 theorem bottDuality_homogeneous (l : List I) {n m : ℤ}
    {x y : BottSamelsonModule cs l} (hx : x ∈ bottPiece cs basis l n)
    (hy : y ∈ bottPiece cs basis l m) :
    bottSamelsonDuality cs l x y ∈ symmetricGrading basis (n+m-l.length) := by
  exact pairing_homogeneous (symmetricGrading basis) (bottBasis cs l) (bottDegree l)
    (bottSamelsonDuality cs l).toLinearMap l.length
    (bottBasis_pairing_homogeneous cs basis l) hx hy

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

 theorem coefficientAction_reflection {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t = reflectionAction (embed M a) (extendedForm M (embed M a))
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  rw [coefficientAction,ha.extendedAction_eq]

 theorem reflectionCoefficient_anti {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t (SymmetricAlgebra.ι ℝ (Extended M) (embed M a)) =
      -SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := by
  rw [coefficientAction_reflection cs ha]
  exact reflectionAction_anti _ _ _

 theorem reflectionCoefficient_divisible {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (p : SymmetricCoefficient (M := M)) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣ p-coefficientAction cs t p := by
  rw [coefficientAction_reflection cs ha]
  exact reflectionAction_divisible _ _ _ p

 theorem reflectionCoefficient_difference {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (x : W) : ∃ p : SymmetricCoefficient (M := M),
    coefficientAction cs x p-coefficientAction cs (t*x) p =
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := by
  let α := SymmetricAlgebra.ι ℝ (Extended M) (embed M a)
  let c : SymmetricCoefficient (M := M) := (1/2 : ℝ) • α
  refine ⟨(coefficientAction cs x).symm c,?_⟩
  rw [coefficientAction_mul,AlgEquiv.apply_symm_apply]
  change (1/2 : ℝ) • α - coefficientAction cs t ((1/2 : ℝ) • α) = α
  rw [map_smul,reflectionCoefficient_anti cs ha]
  module

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v un
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem coefficientAction_one (a : SymmetricCoefficient (M := M)) :
    coefficientAction cs 1 a = a := by
  have h := coefficientAction_mul cs 1 1 a
  rw [one_mul] at h
  exact (coefficientAction cs 1).injective h.symm

 def bottWeight : (l : List I) → BottIndex l → W
  | [], _ => 1
  | i::l, e => if e.1=0 then bottWeight l e.2 else cs.simple i*bottWeight l e.2

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def weightFunctional (i : I) (N : PairedModule.{u,un} (SymmetricCoefficient (M := M)))
    (f : N →ₗ[SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M))
    (ε : Fin 2) : N →ₗ[simpleFixed cs i] SymmetricCoefficient (M := M) where
  toFun m := if ε=0 then f m else coefficientAction cs (cs.simple i) (f m)
  map_add' m n := by split_ifs <;> simp only [map_add]
  map_smul' c m := by
    change (if ε=0 then f ((c:SymmetricCoefficient (M:=M)) • m) else
      coefficientAction cs (cs.simple i) (f ((c:SymmetricCoefficient (M:=M)) • m))) = _
    split_ifs
    · simp only [map_smul,Subalgebra.smul_def,RingHom.id_apply]
    · rw [map_smul]
      change coefficientAction cs (cs.simple i)
        ((c:SymmetricCoefficient (M:=M))*f m) =
        (c:SymmetricCoefficient (M:=M))*coefficientAction cs (cs.simple i) (f m)
      rw [map_mul, show coefficientAction cs (cs.simple i) (c:SymmetricCoefficient (M:=M)) = c from c.property]

 def inducedFunctional (i : I) (N : PairedModule.{u,un} (SymmetricCoefficient (M := M)))
    (f : N →ₗ[simpleFixed cs i] SymmetricCoefficient (M := M)) :
    (SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] N) →ₗ[SymmetricCoefficient (M := M)]
      SymmetricCoefficient (M := M) :=
  AlgebraTensorModule.lift ((LinearMap.id : SymmetricCoefficient (M := M) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)).smulRight f)

 def bottEvaluation : (l : List I) → BottIndex l →
    BottSamelsonModule cs l →ₗ[SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)
  | [], _ => LinearMap.id
  | i::l, e => inducedFunctional cs i (bottSamelson cs l).obj
      (weightFunctional cs i (bottSamelson cs l).obj (bottEvaluation l e.2) e.1)

 theorem bottEvaluation_tmul (i : I) (l : List I) (e : BottIndex (i::l))
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottEvaluation cs (i::l) e (a ⊗ₜ[simpleFixed cs i] m) =
      a*(if e.1=0 then bottEvaluation cs l e.2 m else
        coefficientAction cs (cs.simple i) (bottEvaluation cs l e.2 m)) := rfl

 theorem bottEvaluation_right (l : List I) (e : BottIndex l)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottEvaluation cs l e (bottSamelsonRight cs l a m) =
      coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e m := by
  induction l with
  | nil =>
    change SymmetricCoefficient (M := M) at m
    change a*m = coefficientAction cs 1 a * m
    rw [coefficientAction_one]
  | cons i l ih =>
    change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
    induction m using TensorProduct.inductionOn with
    | add m n hm hn => erw [map_add,map_add,map_add,hm,hn,mul_add]
    | tmul b m =>
      change bottEvaluation cs (i::l) e (b ⊗ₜ[simpleFixed cs i] bottSamelsonRight cs l a m) = _
      erw [bottEvaluation_tmul,bottEvaluation_tmul,ih]
      change b*(if e.1=0 then _ else _) = coefficientAction cs
        (if e.1=0 then bottWeight cs l e.2 else cs.simple i*bottWeight cs l e.2) a * _
      split_ifs with h
      · ring
      · rw [map_mul,coefficientAction_mul]
        ring

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
open scoped Matrix
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def bottEvaluationMatrix (l : List I) : Matrix (BottIndex l) (BottIndex l)
    (SymmetricCoefficient (M := M)) := fun e j => bottEvaluation cs l e (bottBasis cs l j)

 theorem bottEvaluation_expand (l : List I) (e : BottIndex l) (m : BottSamelsonModule cs l) :
    bottEvaluation cs l e m =
      (bottEvaluationMatrix cs l *ᵥ (bottBasis cs l).equivFun m) e := by
  classical
  conv_lhs => rw [← (bottBasis cs l).sum_repr m]
  simp only [map_sum,map_smul,smul_eq_mul,Matrix.mulVec,dotProduct,
    bottEvaluationMatrix,Basis.equivFun_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

 theorem bottEvaluationMatrix_cons (i : I) (l : List I)
    (r c : Fin 2) (j k : BottIndex l) :
    bottEvaluationMatrix cs (i::l) (r,j) (c,k) =
      if r=0 then (if c=0 then bottEvaluationMatrix cs l j k else
        simpleRootPolynomial i*bottEvaluationMatrix cs l j k)
      else if c=0 then coefficientAction cs (cs.simple i) (bottEvaluationMatrix cs l j k)
      else -simpleRootPolynomial i*coefficientAction cs (cs.simple i) (bottEvaluationMatrix cs l j k) := by
  let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
    simpleFixed_free cs i
  let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
    simpleFixed_finite cs i
  change bottEvaluation cs (i::l) (r,j)
    (inducedBasis (coefficientAction cs (cs.simple i)) (simpleRootPolynomial i)
      (simple_involutive cs i) (simpleRootPolynomial_ne_zero i) (simple_anti cs i)
      (simple_divisible cs i) (bottSamelson cs l).obj (bottBasis cs l) (c,k)) = _
  rw [inducedBasis_apply]
  erw [bottEvaluation_tmul]
  fin_cases r <;> fin_cases c <;>
    simp only [Fin.zero_eta,Fin.isValue,Fin.mk_one,ite_true,
      show (1:Fin 2) ≠ 0 by decide,ite_false,reflectionBasis_zero,reflectionBasis_one,
      one_smul,one_mul,map_smul,smul_eq_mul,map_mul,simple_anti,bottEvaluationMatrix]

 theorem bottEvaluationMatrix_mulVec_cons (i : I) (l : List I)
    (v : BottIndex (i::l) → SymmetricCoefficient (M := M)) :
    bottEvaluationMatrix cs (i::l) *ᵥ v =
      wallCoordinate (coefficientAction cs (cs.simple i)).toRingEquiv
        (simpleRootPolynomial i) (bottEvaluationMatrix cs l) v := by
  have heq : bottEvaluationMatrix cs (i::l) =
      wallMatrix (coefficientAction cs (cs.simple i)).toRingEquiv
        (simpleRootPolynomial i) (bottEvaluationMatrix cs l) := by
    funext e f
    rcases e with ⟨r,j⟩
    rcases f with ⟨c,k⟩
    exact bottEvaluationMatrix_cons cs i l r c j k
  rw [heq]
  exact wallMatrix_mulVec (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial i) (bottEvaluationMatrix cs l) v

 theorem bottEvaluationMatrix_injective (l : List I) :
    Function.Injective (Matrix.mulVec (bottEvaluationMatrix cs l)) := by
  classical
  let : CharZero (SymmetricCoefficient (M := M)) := Algebra.charZero_of_charZero ℝ _
  induction l with
  | nil =>
    intro v w h
    funext j
    change PUnit at j
    cases j
    have hh := congrFun h PUnit.unit
    let : Unique (BottIndex ([] : List I)) := inferInstanceAs (Unique PUnit)
    have hcol (k : BottIndex ([] : List I)) :
        bottEvaluationMatrix cs [] PUnit.unit k = 1 := by
      change PUnit at k
      change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) k) = 1
      simp only [Basis.singleton_apply]
    simp only [Matrix.mulVec,dotProduct,hcol,one_mul,Finset.univ_unique,
      Finset.sum_singleton] at hh
    simpa only [Subsingleton.elim (default : BottIndex ([] : List I)) PUnit.unit] using hh
  | cons i l ih =>
    intro v w h
    apply wallCoordinate_injective (coefficientAction cs (cs.simple i)).toRingEquiv
      (simpleRootPolynomial i) (simpleRootPolynomial_ne_zero i) (bottEvaluationMatrix cs l) ih
    rw [← bottEvaluationMatrix_mulVec_cons,← bottEvaluationMatrix_mulVec_cons]
    exact h

 theorem bottEvaluation_injective (l : List I) :
    Function.Injective (fun m : BottSamelsonModule cs l => fun e => bottEvaluation cs l e m) := by
  intro m n h
  apply (bottBasis cs l).equivFun.injective
  apply bottEvaluationMatrix_injective cs l
  funext e
  rw [← bottEvaluation_expand,← bottEvaluation_expand]
  exact congrFun h e

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSubword : (l : List I) → BottIndex l → List I
  | [], _ => []
  | i::l, e => if e.1=0 then bottSubword l e.2 else i::bottSubword l e.2

 theorem bottSubword_sublist (l : List I) (e : BottIndex l) :
    (bottSubword l e).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons i l ih =>
    by_cases h : e.1=0
    · rw [bottSubword,ite_eq_left h]
      exact List.Sublist.cons i (ih e.2)
    · rw [bottSubword,ite_eq_right h]
      exact List.Sublist.cons_cons i (ih e.2)

 theorem bottSubword_wordProd (l : List I) (e : BottIndex l) :
    cs.wordProd (bottSubword l e) = bottWeight cs l e := by
  induction l with
  | nil => exact cs.wordProd_nil
  | cons i l ih =>
    by_cases h : e.1=0
    · simp only [bottSubword,bottWeight,ite_eq_left h,ih]
    · simp only [bottSubword,bottWeight,ite_eq_right h,cs.wordProd_cons,ih]

 theorem exists_bottSubword {ν l : List I} (h : ν.Sublist l) :
    ∃ e : BottIndex l, bottSubword l e = ν := by
  induction h with
  | slnil => exact ⟨PUnit.unit,rfl⟩
  | cons i h ih =>
    obtain ⟨e,he⟩ := ih
    exact ⟨(0,e),by simpa only [bottSubword,ite_true] using he⟩
  | cons_cons i h ih =>
    obtain ⟨e,he⟩ := ih
    exact ⟨(1,e),by simp only [bottSubword,show (1:Fin 2) ≠ 0 by decide,ite_false,he]⟩

 theorem bottWeight_bruhat (l : List I) (hl : cs.IsReduced l) (e : BottIndex l) :
    BruhatLE cs (bottWeight cs l e) (cs.wordProd l) := by
  rw [← bottSubword_wordProd]
  exact bruhat_of_subword cs (bottSubword_sublist l e) hl

 theorem exists_bottWeight (l : List I) (hl : cs.IsReduced l) {x : W}
    (hx : BruhatLE cs x (cs.wordProd l)) : ∃ e : BottIndex l, bottWeight cs l e=x := by
  obtain ⟨ν,hν,_,he⟩ := (bruhat_iff_reduced_subword cs hl).mp hx
  obtain ⟨e,he'⟩ := exists_bottSubword hν
  exact ⟨e,by rw [← bottSubword_wordProd,he',he]⟩

 theorem bottWeight_range (l : List I) (hl : cs.IsReduced l) :
    Set.range (bottWeight cs l) = {x | BruhatLE cs x (cs.wordProd l)} := by
  ext x
  constructor
  · rintro ⟨e,rfl⟩
    exact bottWeight_bruhat cs l hl e
  · exact exists_bottWeight cs l hl

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
open scoped Matrix
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottCoordinateDenominator (l : List I) : SymmetricCoefficient (M := M) := by
  classical
  exact (bottEvaluationMatrix cs l).det

 theorem bottCoordinateDenominator_ne_zero (l : List I) :
    bottCoordinateDenominator cs l ≠ 0 := by
  classical
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact Matrix.mulVec_injective_iff.mp (bottEvaluationMatrix_injective cs l)

 theorem bottEvaluation_contains_scaled_coordinates (l : List I)
    (v : BottIndex l → SymmetricCoefficient (M := M)) :
    ∃ m : BottSamelsonModule cs l, ∀ e,
      bottEvaluation cs l e m = bottCoordinateDenominator cs l * v e := by
  classical
  refine ⟨(bottBasis cs l).equivFun.symm ((bottEvaluationMatrix cs l).adjugate *ᵥ v),?_⟩
  intro e
  rw [bottEvaluation_expand]
  simp only [LinearEquiv.apply_symm_apply,Matrix.mulVec_mulVec,Matrix.mul_adjugate,
    Matrix.smul_mulVec,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,bottCoordinateDenominator]

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidableEqBottIndex (l : List I) : DecidableEq (BottIndex l) := Classical.decEq _

 def bottWeightSupported (l : List I) (x : W) : Submodule (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l) where
  carrier := {m | ∀ e, bottWeight cs l e ≠ x → bottEvaluation cs l e m = 0}
  zero_mem' := by intro e _; exact map_zero _
  add_mem' := by intro m n hm hn e he; rw [map_add,hm e he,hn e he,zero_add]
  smul_mem' := by intro a m hm e he; rw [map_smul,hm e he,smul_zero]

 theorem bott_weight_eigen (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : m ∈ bottWeightSupported cs l x) (a : SymmetricCoefficient (M := M)) :
    bottSamelsonRight cs l a m = coefficientAction cs x a • m := by
  apply bottEvaluation_injective cs l
  funext e
  change bottEvaluation cs l e (bottSamelsonRight cs l a m) =
    bottEvaluation cs l e (coefficientAction cs x a • m)
  erw [bottEvaluation_right,map_smul]
  change _ = coefficientAction cs x a * bottEvaluation cs l e m
  by_cases he : bottWeight cs l e = x
  · rw [he]
  · rw [hm e he,mul_zero,mul_zero]

 theorem bott_eigen_supported (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : ∀ a : SymmetricCoefficient (M := M),
      bottSamelsonRight cs l a m = coefficientAction cs x a • m) :
    m ∈ bottWeightSupported cs l x := by
  intro e he
  obtain ⟨a,ha⟩ := coefficientAction_separates cs he
  have h := congrArg (bottEvaluation cs l e) (hm a)
  erw [bottEvaluation_right,map_smul] at h
  change coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e m =
    coefficientAction cs x a * bottEvaluation cs l e m at h
  have hh : (coefficientAction cs (bottWeight cs l e) a-coefficientAction cs x a) *
      bottEvaluation cs l e m = 0 := by rw [sub_mul,h,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ha)

 theorem bott_distinct_weight_orthogonal (l : List I) {x y : W} (hxy : x ≠ y)
    {m n : BottSamelsonModule cs l} (hm : m ∈ bottWeightSupported cs l x)
    (hn : n ∈ bottWeightSupported cs l y) : bottSamelsonDuality cs l m n = 0 := by
  obtain ⟨a,ha⟩ := coefficientAction_separates cs hxy
  have h := bottSamelson_balanced cs l a m n
  rw [bott_weight_eigen cs l x hm,bott_weight_eigen cs l y hn] at h
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h
  have he : (coefficientAction cs x a-coefficientAction cs y a) *
      bottSamelsonDuality cs l m n = 0 := by rw [sub_mul,h,sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha)

 def bottCoordinateLift (l : List I) (e : BottIndex l) : BottSamelsonModule cs l := by
  classical
  exact (bottEvaluation_contains_scaled_coordinates cs l (Pi.single e 1)).choose

 theorem bottCoordinateLift_eval (l : List I) (e j : BottIndex l) :
    bottEvaluation cs l j (bottCoordinateLift cs l e) =
      bottCoordinateDenominator cs l * (Pi.single e 1 : BottIndex l → SymmetricCoefficient (M := M)) j := by
  classical
  exact (bottEvaluation_contains_scaled_coordinates cs l (Pi.single e 1)).choose_spec j

 theorem bottCoordinateLift_supported (l : List I) (e : BottIndex l) :
    bottCoordinateLift cs l e ∈ bottWeightSupported cs l (bottWeight cs l e) := by
  intro j hj
  rw [bottCoordinateLift_eval]
  have hje : j ≠ e := fun h => hj (congrArg (bottWeight cs l) h)
  rw [Pi.single_eq_of_ne hje, mul_zero]

 theorem bottCoordinateExpansion (l : List I) (m : BottSamelsonModule cs l) :
    bottCoordinateDenominator cs l • m =
      ∑ e : BottIndex l, bottEvaluation cs l e m • bottCoordinateLift cs l e := by
  classical
  apply bottEvaluation_injective cs l
  funext j
  simp only [map_smul,map_sum,bottCoordinateLift_eval,smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same,mul_one,mul_comm]
  · intro e _ hej
    rw [Pi.single_eq_of_ne (Ne.symm hej),mul_zero,mul_zero]
  · simp

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottWeightProjection (l : List I) (x : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  LinearMap.pi (fun e => bottEvaluation cs l e.val)

 theorem bottWeightProjection_eq_zero (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    bottWeightProjection cs l x m = 0 ↔ ∀ e, bottWeight cs l e=x → bottEvaluation cs l e m=0 := by
  constructor
  · intro h e he
    exact congrFun h ⟨e,he⟩
  · intro h
    funext e
    exact h e.val e.property

 theorem bott_supported_annihilates (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : m ∈ bottWeightSupported cs l x) (n : BottSamelsonModule cs l)
    (hn : bottWeightProjection cs l x n=0) : bottSamelsonDuality cs l m n=0 := by
  classical
  have hn' := (bottWeightProjection_eq_zero cs l x n).mp hn
  have hsum : ∑ e : BottIndex l, bottEvaluation cs l e n *
      bottSamelsonDuality cs l m (bottCoordinateLift cs l e) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : bottWeight cs l e=x
    · rw [hn' e he,zero_mul]
    · rw [bott_distinct_weight_orthogonal cs l (Ne.symm he) hm
        (bottCoordinateLift_supported cs l e),mul_zero]
  have hh := congrArg (bottSamelsonDuality cs l m) (bottCoordinateExpansion cs l n)
  simp only [map_smul,map_sum,smul_eq_mul] at hh
  rw [hsum] at hh
  exact (mul_eq_zero.mp hh).resolve_left (bottCoordinateDenominator_ne_zero cs l)

 theorem bott_annihilates_supported (l : List I) (x : W) {m : BottSamelsonModule cs l}
    (hm : ∀ n : BottSamelsonModule cs l, bottWeightProjection cs l x n=0 →
      bottSamelsonDuality cs l m n=0) : m ∈ bottWeightSupported cs l x := by
  apply bott_eigen_supported cs l x
  intro a
  apply (bottSamelsonDuality cs l).injective
  apply LinearMap.ext
  intro n
  have hn : bottWeightProjection cs l x
      (bottSamelsonRight cs l a n - coefficientAction cs x a • n)=0 := by
    apply (bottWeightProjection_eq_zero cs l x _).mpr
    intro e he
    erw [map_sub,bottEvaluation_right,map_smul]
    change coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e n -
      coefficientAction cs x a * bottEvaluation cs l e n=0
    rw [he,sub_self]
  have hh := hm _ hn
  simp only [map_sub,map_smul,smul_eq_mul] at hh
  rw [bottSamelson_balanced]
  change bottSamelsonDuality cs l m (bottSamelsonRight cs l a n) =
    (bottSamelsonDuality cs l (coefficientAction cs x a • m)) n
  rw [map_smul,LinearMap.smul_apply,smul_eq_mul]
  exact sub_eq_zero.mp hh

 theorem bott_supported_iff_annihilates (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    m ∈ bottWeightSupported cs l x ↔ ∀ n : BottSamelsonModule cs l,
      bottWeightProjection cs l x n=0 → bottSamelsonDuality cs l m n=0 :=
  ⟨fun h => bott_supported_annihilates cs l x h,fun h => bott_annihilates_supported cs l x h⟩

 def bottStalk (l : List I) (x : W) : Submodule (SymmetricCoefficient (M := M))
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  LinearMap.range (bottWeightProjection cs l x)

 def bottStalkProjection (l : List I) (x : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] bottStalk cs l x :=
  (bottWeightProjection cs l x).rangeRestrict

 theorem bottStalkProjection_surjective (l : List I) (x : W) :
    Function.Surjective (bottStalkProjection cs l x) := by
  rintro ⟨v,m,hm⟩
  exact ⟨m,Subtype.ext hm⟩

 theorem bottStalkProjection_eq_zero (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x m=0 ↔ bottWeightProjection cs l x m=0 := by
  exact Subtype.ext_iff

 def bottStalkDualToSupport (l : List I) (x : W) :
    Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) →ₗ[SymmetricCoefficient (M := M)]
      bottWeightSupported cs l x :=
  ((bottSamelsonDuality cs l).symm.toLinearMap.comp
    (bottStalkProjection cs l x).dualMap).codRestrict (bottWeightSupported cs l x) (by
    intro lam
    apply bott_annihilates_supported cs l x
    intro n hn
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.dualMap_apply]
    change lam (bottStalkProjection cs l x n)=0
    rw [(bottStalkProjection_eq_zero cs l x n).mpr hn,map_zero])

 theorem bottStalkDualToSupport_bijective (l : List I) (x : W) :
    Function.Bijective (bottStalkDualToSupport cs l x) := by
  constructor
  · intro lam mu he
    apply LinearMap.dualMap_injective_of_surjective (bottStalkProjection_surjective cs l x)
    apply (bottSamelsonDuality cs l).symm.injective
    exact congrArg Subtype.val he
  · intro m
    have hm : bottSamelsonDuality cs l m.val ∈
        (LinearMap.ker (bottStalkProjection cs l x)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro n hn
      exact bott_supported_annihilates cs l x m.property n
        ((bottStalkProjection_eq_zero cs l x n).mp hn)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _
      (bottStalkProjection_surjective cs l x)] at hm
    obtain ⟨lam,hlam⟩ := hm
    refine ⟨lam,?_⟩
    apply Subtype.ext
    change (bottSamelsonDuality cs l).symm ((bottStalkProjection cs l x).dualMap lam)=m.val
    rw [hlam,LinearEquiv.symm_apply_apply]

 def bottStalkDuality (l : List I) (x : W) : bottWeightSupported cs l x ≃ₗ[
    SymmetricCoefficient (M := M)] Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  (LinearEquiv.ofBijective (bottStalkDualToSupport cs l x)
    (bottStalkDualToSupport_bijective cs l x)).symm

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

 theorem bottStalkProjection_right (l : List I) (x : W)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x (bottSamelsonRight cs l a m) =
      coefficientAction cs x a • bottStalkProjection cs l x m := by
  apply Subtype.ext
  funext e
  change bottEvaluation cs l e.val (bottSamelsonRight cs l a m) =
    coefficientAction cs x a * bottEvaluation cs l e.val m
  rw [bottEvaluation_right,e.property]

 def bottProjectionSheaf (l : List I) (u b : W) : Sheaf (R := SymmetricCoefficient (M := M))
    (graph cs u b) where
  vertex x := ModuleCat.of _ (bottStalk cs l x.val)
  edge e := ModuleCat.of _ (PairProjection.Edge
    (bottStalkProjection cs l (source cs u b e).val)
    (bottStalkProjection cs l (target cs u b e).val))
  lower e := by
    change (bottStalk cs l (source cs u b e).val) →ₗ[SymmetricCoefficient (M := M)] _
    exact PairProjection.lower (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val)
  upper e := by
    change (bottStalk cs l (target cs u b e).val) →ₗ[SymmetricCoefficient (M := M)] _
    exact PairProjection.upper (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val)

 def bottSection (l : List I) (u b : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] (bottProjectionSheaf cs l u b).sections Set.univ where
  toFun m := ⟨fun x => bottStalkProjection cs l x.val m,by
    intro e _ _
    exact PairProjection.compatible _ _ m⟩
  map_add' := by
    intro m n
    apply Subtype.ext
    funext x
    exact map_add (bottStalkProjection cs l x.val) m n
  map_smul' := by
    intro r m
    apply Subtype.ext
    funext x
    exact map_smul (bottStalkProjection cs l x.val) r m

 theorem bottProjectionSheaf_generated (l : List I) (u b : W) :
    (bottProjectionSheaf cs l u b).Generated := by
  intro x v
  obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val v
  exact ⟨(bottSection cs l u b m).val,(bottSection cs l u b m).property,hm⟩

 theorem bottProjectionSheaf_lower_surjective (l : List I) (u b : W) (e : Edge cs u b) :
    Function.Surjective ((bottProjectionSheaf cs l u b).lower e) :=
  PairProjection.lower_surjective _ _ (bottStalkProjection_surjective cs l _)

 theorem bottProjectionSheaf_upper_surjective (l : List I) (u b : W) (e : Edge cs u b) :
    Function.Surjective ((bottProjectionSheaf cs l u b).upper e) :=
  PairProjection.upper_surjective _ _ (bottStalkProjection_surjective cs l _)

/-- An actual Bruhat reflection root annihilates the integral edge quotient. -/
 theorem bottProjectionSheaf_annihilated (l : List I) (u b : W) (e : Edge cs u b)
    {a : I → ℝ} (ha : Represents M cs (label cs u b e) a)
    (z : (bottProjectionSheaf cs l u b).edge e) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z = 0 := by
  obtain ⟨p,hp⟩ := reflectionCoefficient_difference cs ha (source cs u b e).val
  rw [label_mul_source] at hp
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs l _) (bottStalkProjection_surjective cs l _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs l _ p) (bottStalkProjection_right cs l _ p) z

 theorem bottSection_injective (l : List I) (hl : cs.IsReduced l) :
    Function.Injective (bottSection cs l 1 (cs.wordProd l)) := by
  intro m n h
  apply bottEvaluation_injective cs l
  funext e
  let x : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hh := congrArg (fun z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    z.val x) h
  exact congrFun (congrArg Subtype.val hh) ⟨e,rfl⟩

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

/-- The reflection is linear over its actual invariant subalgebra. -/
def simpleFixedAction (i : I) : SymmetricCoefficient (M := M) →ₗ[simpleFixed cs i]
    SymmetricCoefficient (M := M) where
  toFun := coefficientAction cs (cs.simple i)
  map_add' := map_add _
  map_smul' c a := by
    change coefficientAction cs (cs.simple i) ((c : SymmetricCoefficient (M := M))*a) =
      (c : SymmetricCoefficient (M := M))*coefficientAction cs (cs.simple i) a
    rw [map_mul, show coefficientAction cs (cs.simple i)
      (c : SymmetricCoefficient (M := M)) = c from c.property]

/-- Reflect the first tensor factor. It is not asserted to be left A-linear. -/
def bottSimpleFlip (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[simpleFixed cs i]
    BottSamelsonModule cs (i::l) :=
  TensorProduct.map (simpleFixedAction cs i)
    (LinearMap.id : BottSamelsonModule cs l →ₗ[simpleFixed cs i] BottSamelsonModule cs l)

@[simp] theorem bottSimpleFlip_tmul (i : I) (l : List I)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottSimpleFlip cs i l (a ⊗ₜ[simpleFixed cs i] m) =
      coefficientAction cs (cs.simple i) a ⊗ₜ[simpleFixed cs i] m := rfl

/-- The integral divisibility statement, before any localization. -/
theorem bottSimpleFlip_divisible (i : I) (l : List I) (m : BottSamelsonModule cs (i::l)) :
    ∃ n : BottSamelsonModule cs (i::l),
      m-bottSimpleFlip cs i l m = simpleRootPolynomial (M := M) i • n := by
  change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
  induction m using TensorProduct.inductionOn with
  | add m n hm hn =>
    obtain ⟨m',hm'⟩ := hm
    obtain ⟨n',hn'⟩ := hn
    refine ⟨m'+n', ?_⟩
    erw [map_add, add_sub_add_comm, hm', hn', smul_add]
  | tmul a m =>
    obtain ⟨b,hb⟩ := simple_divisible cs i a
    refine ⟨b ⊗ₜ[simpleFixed cs i] m, ?_⟩
    erw [bottSimpleFlip_tmul, ← sub_tmul, hb]
    rfl


/-- Exchange the two branches of the first subexpression slot. -/
def bottIndexFlip (i : I) (l : List I) (e : BottIndex (i::l)) : BottIndex (i::l) :=
  (1-e.1,e.2)

omit [Fintype I] in
theorem bottWeight_flip (i : I) (l : List I) (e : BottIndex (i::l)) :
    bottWeight cs (i::l) (bottIndexFlip i l e) = cs.simple i * bottWeight cs (i::l) e := by
  rcases e with ⟨ε,e⟩
  fin_cases ε <;> simp [bottIndexFlip, bottWeight, cs.simple_mul_simple_cancel_left]

theorem bottEvaluation_flip (i : I) (l : List I) (e : BottIndex (i::l))
    (m : BottSamelsonModule cs (i::l)) :
    bottEvaluation cs (i::l) e (bottSimpleFlip cs i l m) =
      coefficientAction cs (cs.simple i)
        (bottEvaluation cs (i::l) (bottIndexFlip i l e) m) := by
  change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => erw [map_add, map_add, map_add, map_add, hm, hn]
  | tmul a m =>
    rcases e with ⟨ε,e⟩
    fin_cases ε
    · change coefficientAction cs (cs.simple i) a * bottEvaluation cs l e m =
        coefficientAction cs (cs.simple i)
          (a * coefficientAction cs (cs.simple i) (bottEvaluation cs l e m))
      rw [map_mul, simple_involutive cs i]
    · change coefficientAction cs (cs.simple i) a *
        coefficientAction cs (cs.simple i) (bottEvaluation cs l e m) =
        coefficientAction cs (cs.simple i) (a * bottEvaluation cs l e m)
      rw [map_mul]

theorem bottStalkProjection_flip_zero (i : I) (l : List I) (x : W)
    {m : BottSamelsonModule cs (i::l)} (hm : bottStalkProjection cs (i::l) x m=0) :
    bottStalkProjection cs (i::l) (cs.simple i*x) (bottSimpleFlip cs i l m)=0 := by
  apply (bottStalkProjection_eq_zero cs _ _ _).mpr
  apply (bottWeightProjection_eq_zero cs _ _ _).mpr
  intro e he
  rw [bottEvaluation_flip]
  have hh := (bottWeightProjection_eq_zero cs _ _ _).mp
    ((bottStalkProjection_eq_zero cs _ _ _).mp hm)
  rw [hh (bottIndexFlip i l e) (by
    rw [bottWeight_flip, he, cs.simple_mul_simple_cancel_left]), map_zero]

/-- The reverse inclusion to edge annihilation for the simple wall at the
first tensor letter, expressed directly on kernel projections. -/
theorem bottSimpleWall_kernel_projection (i : I) (l : List I) (x : W)
    {m : BottSamelsonModule cs (i::l)} (hm : bottStalkProjection cs (i::l) x m=0) :
    ∃ n : bottStalk cs (i::l) (cs.simple i*x),
      bottStalkProjection cs (i::l) (cs.simple i*x) m = simpleRootPolynomial (M := M) i • n := by
  obtain ⟨n,hn⟩ := bottSimpleFlip_divisible cs i l m
  refine ⟨bottStalkProjection cs (i::l) (cs.simple i*x) n, ?_⟩
  have he := congrArg (bottStalkProjection cs (i::l) (cs.simple i*x)) hn
  rw [map_sub, map_smul, bottStalkProjection_flip_zero cs i l x hm, sub_zero] at he
  exact he

theorem simpleCoefficient_difference (i : I) (x : W) :
    ∃ p : SymmetricCoefficient (M := M),
      coefficientAction cs x p - coefficientAction cs (cs.simple i*x) p =
        simpleRootPolynomial (M := M) i := by
  let α := simpleRootPolynomial (M := M) i
  refine ⟨(coefficientAction cs x).symm ((1/2 : ℝ) • α), ?_⟩
  rw [coefficientAction_mul, AlgEquiv.apply_symm_apply]
  change (1/2 : ℝ) • α - coefficientAction cs (cs.simple i) ((1/2 : ℝ) • α) = α
  rw [map_smul, simple_anti]
  module


/-- Any old word's simple-edge quotient is killed by the actual label. -/
theorem bottSimpleEdge_annihilated (i : I) (l : List I) (x : W)
    (z : PairProjection.Edge (bottStalkProjection cs l x)
      (bottStalkProjection cs l (cs.simple i*x))) :
    simpleRootPolynomial (M := M) i • z = 0 := by
  obtain ⟨p,hp⟩ := simpleCoefficient_difference cs i x
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs _ _) (bottStalkProjection_surjective cs _ _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs _ _ p) (bottStalkProjection_right cs _ _ p) z

theorem bottSimpleEdge_kernel_inclusion (i : I) (l : List I) (x : W)
    (y : bottStalk cs l (cs.simple i*x)) :
    ∃ n : BottSamelsonModule cs l, bottStalkProjection cs l x n=0 ∧
      bottStalkProjection cs l (cs.simple i*x) n=simpleRootPolynomial (M := M) i • y := by
  apply (PairProjection.kernel_upper _ _ _).mp
  rw [map_smul]
  exact bottSimpleEdge_annihilated cs i l x _

/-- The integral edge quotient is killed by its actual simple-root label. -/
theorem bottSimpleWall_annihilated (i : I) (l : List I) (x : W)
    (z : PairProjection.Edge (bottStalkProjection cs (i::l) x)
      (bottStalkProjection cs (i::l) (cs.simple i*x))) :
    simpleRootPolynomial (M := M) i • z = 0 :=
  bottSimpleEdge_annihilated cs i (i::l) x z

/-- The exact integral quotient kernel, without a free-stalk hypothesis. -/
theorem bottSimpleWall_upper_kernel (i : I) (l : List I) (x : W)
    (z : bottStalk cs (i::l) (cs.simple i*x)) :
    PairProjection.upper (bottStalkProjection cs (i::l) x)
      (bottStalkProjection cs (i::l) (cs.simple i*x)) z = 0 ↔
    ∃ n : bottStalk cs (i::l) (cs.simple i*x), z = simpleRootPolynomial (M := M) i • n :=
  PairProjection.upper_kernel_of_divisibility _ _ _
    (fun _ hm => bottSimpleWall_kernel_projection cs i l x hm)
    (bottSimpleWall_annihilated cs i l x) z

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
  let names : Array Name := #[`OAI.KLInvariance.TitsSpace.coefficientAction_reflection]
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
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.RepresentationTheory.BottSamelson.TitsWords.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
