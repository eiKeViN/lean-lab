import Mathlib

/-! Semantic home: ForMathlib.Algebra.Module.CoefficientChange.Basic. Source spans: BottSamelson:27.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe uk ua ub um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {B : Type ub} [CommRing B] [Algebra k B]

@[ext] structure CoefficientChange (_e : A ≃ₐ[k] B) (M : Type um) where
  val : M

namespace CoefficientChange
variable (e : A ≃ₐ[k] B) (M : Type um) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

 def equivVal : CoefficientChange e M ≃ M where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

 instance _root_.OAI.KLInvariance.CoefficientChange.instAddCommGroup : AddCommGroup (CoefficientChange e M) := (equivVal e M).addCommGroup
 instance _root_.OAI.KLInvariance.CoefficientChange.instModule : Module B (CoefficientChange e M) := by
   letI : Module B M := Module.compHom M e.symm.toRingHom
   exact ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module B
 instance _root_.OAI.KLInvariance.CoefficientChange.instModule_1 : Module k (CoefficientChange e M) :=
   ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module k
 instance _root_.OAI.KLInvariance.CoefficientChange.instIsScalarTower : IsScalarTower k B (CoefficientChange e M) where
   smul_assoc c b m := by
     apply CoefficientChange.ext
     change e.symm (c • b) • m.val=c • (e.symm b • m.val)
     rw [map_smul,smul_assoc]

 local instance _root_.OAI.KLInvariance.CoefficientChange.instRingHomInvPairToRingHomToRingEquivSymm : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e.toRingEquiv
 local instance _root_.OAI.KLInvariance.CoefficientChange.instRingHomInvPairToRingHomToRingEquivSymm_1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv

 def equiv : M ≃ₛₗ[e.toRingHom] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' a m := by
     change mk (a • m)=mk (e.symm (e a) • m)
     rw [e.symm_apply_apply]

 def kEquiv : M ≃ₗ[k] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' _ _ := rfl

 instance _root_.OAI.KLInvariance.CoefficientChange.instFree [Module.Free A M] : Module.Free B (CoefficientChange e M) :=
   Module.Free.of_equiv (equiv e M)
 instance _root_.OAI.KLInvariance.CoefficientChange.instFinite [Module.Finite A M] : Module.Finite B (CoefficientChange e M) :=
   Module.Finite.of_surjective (equiv e M).toLinearMap (equiv e M).surjective

 variable {M} {N : Type un} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
 def map (f : M →ₗ[A] N) : CoefficientChange e M →ₗ[B] CoefficientChange e N where
   toFun m := mk (f m.val)
   map_add' m n := CoefficientChange.ext (map_add f m.val n.val)
   map_smul' b m := CoefficientChange.ext (map_smul f (e.symm b) m.val)

 omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
 theorem map_injective (f : M →ₗ[A] N) (hf : Function.Injective f) :
     Function.Injective (map e f) := fun _m _n h => CoefficientChange.ext (hf (congrArg val h))
 omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
 theorem map_surjective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
     Function.Surjective (map e f) := by
   intro n
   obtain ⟨m,hm⟩ := hf n.val
   exact ⟨mk m,CoefficientChange.ext hm⟩

end CoefficientChange
end KLInvariance
end

end OAI
