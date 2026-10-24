module
import ForMathlib.Algebra.Module.CoefficientChange.Basic
import ForMathlib.Algebra.Module.Cover.Local
import ForMathlib.Algebra.Module.ReflectionPair.Twist
import ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties
import ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder
import ForMathlib.RepresentationTheory.BottSamelson.TitsWords
import Lean
open Lean Elab Command
run_elab do
  let names : Array Name := #[`OAI.KLInvariance.CoefficientChange.ext.match_1, `OAI.KLInvariance.LocalCover.splitEquiv.match_3, `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_1, `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_3, `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate_injective.match_1_2, `OAI.KLInvariance.ReflectionFrobenius.wallMatrix_mulVec.match_1_1, `OAI.KLInvariance.ReflectionPairTranslation.Twist.ext.match_1, `OAI.KLInvariance.TitsSpace.exists_common_transverse.match_1_1]
  for n in names do
    let visible ← try pure (some (← realizeGlobalConstNoOverload (mkIdent n))) catch _ => pure none
    unless visible.isNone do throwError "Historical generated name unexpectedly public: {n}"
  for n in #[`OAI.KLInvariance.CoefficientChange.ext,
      `OAI.KLInvariance.ReflectionPairTranslation.Twist.ext,
      `OAI.KLInvariance.LocalCover.splitEquiv,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient,
      `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate_injective,
      `OAI.KLInvariance.ReflectionFrobenius.wallMatrix_mulVec,
      `OAI.KLInvariance.TitsSpace.exists_common_transverse] do
    discard <| realizeGlobalConstNoOverload (mkIdent n)
  logInfo "Exactly eight historical generated names unavailable; semantic names available in ordinary module imports."
open OAI.KLInvariance
section
variable {k A B M : Type*} [Field k] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B] (e : A ≃ₐ[k] B)
example (x y : CoefficientChange e M) (h : x.val = y.val) : x = y := CoefficientChange.ext h
example (x : M) : (CoefficientChange.mk x : CoefficientChange e M).val = x := rfl
end
section
open ReflectionPairTranslation
variable {R Y : Type*} [CommRing R] (τ : R ≃+* R)
example (x y : Twist τ Y) (h : x.val = y.val) : x = y := Twist.ext h
example (x : Y) : (Twist.mk x : Twist τ Y).val = x := rfl
end
section
variable {R B P : Type*} [CommRing R] [AddCommGroup B] [Module R B]
  [AddCommGroup P] [Module R P] (g : B →ₗ[R] P) (s : P →ₗ[R] B)
  (hs : g.comp s = LinearMap.id)
example (b : B) : (LocalCover.splitEquiv g s hs b).1 = g b := rfl
example (p : P) (b : LinearMap.ker g) :
    (LocalCover.splitEquiv g s hs).symm (p,b) = s p + b := rfl
end
section
open TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
example (a b : PositiveRoot M cs) : rootDifference a b = normalizedRoot b-normalizedRoot a := rfl
example (f : Module.Dual ℝ (I → ℝ)) (a b c : PositiveRoot M cs) :
    wallVector f a b c = f (rootDifference a b) • rootDifference a c -
      f (rootDifference a c) • rootDifference a b := rfl
example (f h : Module.Dual ℝ (I → ℝ)) :
    ∃ g : Module.Dual ℝ (I → ℝ),
      Function.Injective (fun a : PositiveRoot M cs => g (normalizedRoot a)) ∧
      Transverse (M := M) (cs := cs) f g ∧ Transverse (M := M) (cs := cs) h g :=
  exists_common_transverse f h
example {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t = ReflectionFrobenius.reflectionAction (embed M a) (extendedForm M (embed M a))
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  rw [coefficientAction_reflection cs ha]
example {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t = ReflectionFrobenius.reflectionAction (embed M a) (extendedForm M (embed M a))
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  simp only [coefficientAction_reflection cs ha]
end
