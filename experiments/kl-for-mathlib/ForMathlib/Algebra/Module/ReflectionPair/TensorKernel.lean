import Mathlib
import ForMathlib.Algebra.Module.ReflectionPair.Twist

/-! Semantic home: ForMathlib.Algebra.Module.ReflectionPair.TensorKernel. Source spans: BottSamelson:7, BottSamelson:10, BottSamelson:18.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionPairTranslation.Twist
universe uk ur uy
variable {k : Type uk} [Field k] {R : Type ur} [CommRing R] [Algebra k R]
  (τ : R ≃ₐ[k] R) (Y : Type uy) [AddCommGroup Y] [Module R Y] [Module k Y]
  [IsScalarTower k R Y]

instance scalarModule : Module k (Twist τ.toRingEquiv Y) :=
  ({ equivVal τ.toRingEquiv Y with map_add' := fun _ _ => rfl } :
    Twist τ.toRingEquiv Y ≃+ Y).module k

instance scalarTower : IsScalarTower k R (Twist τ.toRingEquiv Y) where
  smul_assoc c r y := by
    apply Twist.ext
    change τ (c • r) • y.val=c • (τ r • y.val)
    rw [map_smul,smul_assoc]

def scalarEquiv : Twist τ.toRingEquiv Y ≃ₗ[k] Y where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KLInvariance.ReflectionPairTranslation.Twist
end


section
namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section

 def tensorFirst : (A ⊗[C] N) →ₗ[A] N :=
  AlgebraTensorModule.lift ((LinearMap.id : A →ₗ[A] A).smulRight
    (LinearMap.id : N →ₗ[C] N))

 @[simp] theorem tensorFirst_tmul (a : A) (n : N) :
    tensorFirst (C := C) (a ⊗ₜ[C] n)=a • n := rfl

 def tensorSecond : (A ⊗[C] N) →ₗ[A] Twist τ N := by
  letI : Module C (Twist τ N) := Module.compHom _ (algebraMap C A)
  letI : IsScalarTower C A (Twist τ N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let F : N →ₗ[C] Twist τ N := {
    toFun := Twist.mk
    map_add' := fun _ _ => rfl
    map_smul' := fun c n => by
      apply Twist.ext
      change c • n=τ (algebraMap C A c) • n
      rw [hfix,algebraMap_smul] }
  exact AlgebraTensorModule.lift ((LinearMap.id : A →ₗ[A] A).smulRight F)

 @[simp] theorem tensorSecond_tmul (a : A) (n : N) :
    tensorSecond τ hfix (a ⊗ₜ[C] n)=Twist.mk (τ a • n) := rfl

 def twistMap {P : Type*} [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) :
    Twist τ N →ₗ[A] Twist τ P where
  toFun m := ⟨f m.val⟩
  map_add' m n := Twist.ext (map_add f m.val n.val)
  map_smul' a m := Twist.ext (map_smul f (τ a) m.val)
end
end KLInvariance.ReflectionPairTranslation
end


section
namespace KLInvariance.ReflectionPairTranslation
universe u v w z
variable {R : Type u} [CommRing R]
  {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y) (τ : R ≃+* R) (α : R)
  (hdiv : ∀ r : R, α ∣ τ r-r)
  (hinc : ∀ y : Y, ∃ n : N, f n=0 ∧ g n=α • y)
  (hker : ∀ x : X, (∃ n : N, f n=x ∧ g n=0) ↔ ∃ z : X, x=α • z)

 def right : lattice f g τ α hdiv hinc →ₗ[R] Twist τ Y :=
  (LinearMap.snd R X (Twist τ Y)).comp (lattice f g τ α hdiv hinc).subtype

 theorem right_surjective (hg : Function.Surjective g) :
    Function.Surjective (right f g τ α hdiv hinc) := by
  intro y
  obtain ⟨n,hn⟩ := hg y.val
  exact ⟨⟨(f n,y),n,rfl,hn⟩,rfl⟩

 def rightKernelMap : X →ₗ[R] LinearMap.ker (right f g τ α hdiv hinc) where
  toFun x := ⟨⟨(α • x,⟨0⟩),(hker (α • x)).mpr ⟨x,rfl⟩⟩,rfl⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact smul_add α x y
    · apply Twist.ext
      exact (zero_add (0 : Y)).symm
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact smul_comm α r x
    · apply Twist.ext
      exact (smul_zero _).symm

 theorem rightKernelMap_surjective :
    Function.Surjective (rightKernelMap f g τ α hdiv hinc hker) := by
  rintro ⟨⟨⟨x,y⟩,n,hn,hn'⟩,hy⟩
  have hy' : y.val=0 := congrArg Twist.val hy
  obtain ⟨z,hz⟩ := (hker x).mp ⟨n,hn,hn'.trans hy'⟩
  refine ⟨z,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hz.symm (Twist.ext hy'.symm)

 theorem rightKernelMap_injective (hinj : Function.Injective (fun x : X => α • x)) :
    Function.Injective (rightKernelMap f g τ α hdiv hinc hker) := by
  intro x y h
  exact hinj (congrArg (fun p => p.val.val.1) h)

 noncomputable def rightKernelEquiv (hinj : Function.Injective (fun x : X => α • x)) :
    X ≃ₗ[R] LinearMap.ker (right f g τ α hdiv hinc) :=
  LinearEquiv.ofBijective (rightKernelMap f g τ α hdiv hinc hker)
    ⟨rightKernelMap_injective f g τ α hdiv hinc hker hinj,
      rightKernelMap_surjective f g τ α hdiv hinc hker⟩

 include hker in
 theorem lattice_free_right (hg : Function.Surjective g)
    (hinj : Function.Injective (fun x : X => α • x))
    [Module.Free R X] [Module.Free R Y] :
    Module.Free R (lattice f g τ α hdiv hinc) := by
  let : Module.Free R (LinearMap.ker (right f g τ α hdiv hinc)) :=
    Module.Free.of_equiv (rightKernelEquiv f g τ α hdiv hinc hker hinj)
  exact free_of_surjective_of_ker_free (right f g τ α hdiv hinc)
    (right_surjective f g τ α hdiv hinc hg)
end KLInvariance.ReflectionPairTranslation
end

end OAI
