module
public import Mathlib
public import ForMathlib.Algebra.Module.CoefficientChange.Basic

public section

/-! Semantic home: ForMathlib.Algebra.Module.CoefficientChange.Dual. Source spans: Support:29.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.CoefficientChange
open Module
universe uk ua ub um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {B : Type ub} [CommRing B] [Algebra k B]
  (e : A ≃ₐ[k] B) {M : Type um} [AddCommGroup M] [Module A M]
  [Module k M] [IsScalarTower k A M]
noncomputable section

 @[expose] def mapEquiv {N : Type un} [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] (f : M ≃ₗ[A] N) : CoefficientChange e M ≃ₗ[B] CoefficientChange e N where
  toLinearMap := map e f.toLinearMap
  invFun n := mk (f.symm n.val)
  left_inv m := by
    apply CoefficientChange.ext
    exact (congrArg f.symm (val_map e f.toLinearMap m)).trans (f.symm_apply_apply m.val)
  right_inv n := by
    apply CoefficientChange.ext
    exact (val_map e f.toLinearMap (mk (f.symm n.val))).trans (f.apply_symm_apply n.val)

 omit [Module k M] [IsScalarTower k A M] in
 /-- Transporting an equivalence applies it to the underlying vector. -/
 @[simp] theorem val_mapEquiv {N : Type un} [AddCommGroup N] [Module A N]
     [Module k N] [IsScalarTower k A N]
     (f : M ≃ₗ[A] N) (m : CoefficientChange e M) :
     (mapEquiv e f m).val = f m.val := by rfl

 @[expose] def dualTo (f : CoefficientChange e (Dual A M)) : Dual B (CoefficientChange e M) where
  toFun m := e (f.val m.val)
  map_add' m n := by change e (f.val (m.val+n.val))=_; rw [map_add,map_add]
  map_smul' b m := by
    change e (f.val (e.symm b • m.val))=b * e (f.val m.val)
    rw [map_smul]
    change e (e.symm b * f.val m.val)=_
    rw [map_mul,e.apply_symm_apply]

 @[expose] def dualFrom (f : Dual B (CoefficientChange e M)) : Dual A M where
  toFun m := e.symm (f (mk m))
  map_add' m n := by
    change e.symm (f (mk m+mk n))=_
    rw [map_add,map_add]
  map_smul' a m := by
    change e.symm (f (mk (a • m)))=a * e.symm (f (mk m))
    rw [show (mk (a • m) : CoefficientChange e M)=e a • mk m from by
      apply CoefficientChange.ext
      change a • m=e.symm (e a) • m
      rw [e.symm_apply_apply],
      map_smul]
    change e.symm (e a * f (mk m))=_
    rw [map_mul,e.symm_apply_apply]

 @[expose] def dualEquiv : CoefficientChange e (Dual A M) ≃ₗ[B] Dual B (CoefficientChange e M) where
  toFun := dualTo e
  invFun f := mk (dualFrom e f)
  left_inv f := by
    apply CoefficientChange.ext
    apply LinearMap.ext
    intro m
    exact e.symm_apply_apply (f.val m)
  right_inv f := by
    apply LinearMap.ext
    intro m
    exact e.apply_symm_apply (f m)
  map_add' f g := by
    apply LinearMap.ext
    intro m
    exact map_add e (f.val m.val) (g.val m.val)
  map_smul' b f := by
    apply LinearMap.ext
    intro m
    change e (e.symm b * f.val m.val)=b * e (f.val m.val)
    rw [map_mul,e.apply_symm_apply]

 @[expose] def pairingEquiv (d : M ≃ₗ[A] Dual A M) :
    CoefficientChange e M ≃ₗ[B] Dual B (CoefficientChange e M) :=
  (mapEquiv e d).trans (dualEquiv e)

 omit [Module k M] [IsScalarTower k A M] in
 theorem pairingEquiv_apply (d : M ≃ₗ[A] Dual A M) (m n : CoefficientChange e M) :
    pairingEquiv e d m n=e (d m.val n.val) := by
   change e ((mapEquiv e d m).val n.val) = _
   rw [val_mapEquiv]

end
end KLInvariance.CoefficientChange
end

end OAI
