import Mathlib
import OAI.Algebra.Algebra.ReflectionFrobenius.Basic
import OAI.Algebra.Module.Graded.AlgebraMap

/-! Semantic home: OAI.Algebra.Algebra.ReflectionFrobenius.Basis. Source spans: Frobenius:17, Frobenius:9, Frobenius:8, Frobenius:12.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionFrobenius
open scoped Matrix
universe ua ui
variable {A : Type ua} [CommRing A] [IsDomain A] [CharZero A]
  {ι : Type ui} [Fintype ι] (τ : A ≃+* A) (α : A)
noncomputable section

 def wallCoordinate (E : Matrix ι ι A) (v : Fin 2 × ι → A) : Fin 2 × ι → A := fun e =>
  if e.1=0 then (E *ᵥ (fun j => v (0,j)+α*v (1,j))) e.2
  else ((E.map τ) *ᵥ (fun j => v (0,j)-α*v (1,j))) e.2

 def wallMatrix (E : Matrix ι ι A) : Matrix (Fin 2 × ι) (Fin 2 × ι) A := fun e f =>
  if e.1=0 then (if f.1=0 then E e.2 f.2 else α*E e.2 f.2)
  else if f.1=0 then τ (E e.2 f.2) else -α*τ (E e.2 f.2)

omit [IsDomain A] [CharZero A] in
 theorem wallMatrix_mulVec (E : Matrix ι ι A) (v : Fin 2 × ι → A) :
    wallMatrix τ α E *ᵥ v = wallCoordinate τ α E v := by
  classical
  funext ⟨r,j⟩
  change (∑ c : Fin 2 × ι, wallMatrix τ α E (r,j) c * v c) = _
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  fin_cases r <;>
    simp [wallMatrix,wallCoordinate,Matrix.mulVec,dotProduct,
      Finset.sum_add_distrib,mul_add,
      mul_left_comm,mul_assoc,sub_eq_add_neg]

omit [IsDomain A] [CharZero A] in
 theorem matrixTwist_injective (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (Matrix.mulVec (E.map τ)) := by
  intro v w hv
  have hh : E *ᵥ (fun j => τ.symm (v j)) = E *ᵥ (fun j => τ.symm (w j)) := by
    funext i
    have h := congrArg τ.symm (congrFun hv i)
    simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply,
      RingEquiv.symm_apply_apply] using h
  have hh' := hE hh
  funext i
  exact τ.symm.injective (congrFun hh' i)

 theorem wallCoordinate_injective (hα : α ≠ 0) (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (wallCoordinate τ α E) := by
  intro v w hv
  have h₀ : (fun j => v (0,j)+α*v (1,j)) = (fun j => w (0,j)+α*w (1,j)) := by
    apply hE
    funext j
    simpa only [wallCoordinate,ite_eq_left rfl,ite_true] using congrFun hv (0,j)
  have h₁ : (fun j => v (0,j)-α*v (1,j)) = (fun j => w (0,j)-α*w (1,j)) := by
    apply matrixTwist_injective τ E hE
    funext j
    simpa only [wallCoordinate,show (1:Fin 2) ≠ 0 by decide,ite_false] using congrFun hv (1,j)
  funext ⟨ε,j⟩
  have h0 := congrFun h₀ j
  have h1 := congrFun h₁ j
  have hi1 : v (1,j)=w (1,j) := by
    have hh : (2:A)*α*(v (1,j)-w (1,j))=0 := by linear_combination h0-h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero two_ne_zero hα))
  have hi0 : v (0,j)=w (0,j) := by simpa only [hi1,add_left_inj] using h0
  fin_cases ε
  · exact hi0
  · exact hi1

end
end KLInvariance.ReflectionFrobenius
end


section
namespace KLInvariance.ReflectionFrobenius
open Module
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 def reflectionBasis : Basis (Fin 2) (fixed τ) A :=
  (Basis.finTwoProd (fixed τ)).map (coordinates τ α hinv hα hanti hdiv).symm

 theorem reflectionBasis_zero : reflectionBasis τ α hinv hα hanti hdiv 0 = 1 := by
  change expand τ α (Basis.finTwoProd (fixed τ) 0) = 1
  simp [expand_apply]

 theorem reflectionBasis_one : reflectionBasis τ α hinv hα hanti hdiv 1 = α := by
  change expand τ α (Basis.finTwoProd (fixed τ) 1) = α
  simp [expand_apply]

 theorem reflectionBasis_homogeneous (𝓐 : ℤ → Submodule k A)
    [SetLike.GradedOne 𝓐] (hroot : α ∈ 𝓐 1) (i : Fin 2) :
    reflectionBasis τ α hinv hα hanti hdiv i ∈ 𝓐 (i.val : ℤ) := by
  fin_cases i
  · change reflectionBasis τ α hinv hα hanti hdiv (0 : Fin 2) ∈ 𝓐 0
    rw [reflectionBasis_zero]
    exact SetLike.one_mem_graded 𝓐
  · change reflectionBasis τ α hinv hα hanti hdiv (1 : Fin 2) ∈ 𝓐 1
    rw [reflectionBasis_one]
    exact hroot

end
end KLInvariance.ReflectionFrobenius
end


section
namespace KLInvariance.ReflectionFrobenius
open KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 theorem trace_difference (a : A) :
    2*α*(trace τ α hinv hα hanti hdiv a : A) = a-τ a := by
  have h := expand_coordinates τ α hinv hα hanti hdiv a
  have ht := congrArg τ h
  simp only [expand_apply,map_add,map_mul,fixed_val,hanti] at h ht
  change 2*α*((coordinates τ α hinv hα hanti hdiv a).2 : A) = a-τ a
  linear_combination h-ht

 theorem trace_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedSMul 𝓐 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    {n : ℤ} {a : A} (ha : a ∈ 𝓐 n) :
    (trace τ α hinv hα hanti hdiv a : A) ∈ 𝓐 (n-1) := by
  apply homogeneous_of_mul 𝓐 hroot hα
  have hd := (𝓐 n).sub_mem ha (hτ n a ha)
  have hal := (𝓐 n).smul_mem ((2:k)⁻¹) hd
  have ht := trace_difference τ α hinv hα hanti hdiv a
  have htwo : (2:A)*algebraMap k A ((2:k)⁻¹) = 1 := by
    rw [show (2:A)=algebraMap k A (2:k) by exact (map_ofNat (algebraMap k A) 2).symm, ← map_mul]
    simp
  have he : α*(trace τ α hinv hα hanti hdiv a : A) =
      (2:k)⁻¹ • (a-τ a) := by
    rw [Algebra.smul_def]
    linear_combination (algebraMap k A ((2:k)⁻¹))*ht -
      (α*(trace τ α hinv hα hanti hdiv a : A))*htwo
  exact he ▸ hal

 theorem coordinates_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedSMul 𝓐 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    {n : ℤ} {a : A} (ha : a ∈ 𝓐 n) :
    ((coordinates τ α hinv hα hanti hdiv a).1 : A) ∈ 𝓐 n ∧
    ((coordinates τ α hinv hα hanti hdiv a).2 : A) ∈ 𝓐 (n-1) := by
  have ht := trace_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot hτ ha
  constructor
  · have hp : α*(trace τ α hinv hα hanti hdiv a : A) ∈ 𝓐 n := by
      simpa only [smul_eq_mul,vadd_eq_add,show (1:ℤ)+(n-1)=n by omega] using
        SetLike.GradedSMul.smul_mem hroot ht
    have he : ((coordinates τ α hinv hα hanti hdiv a).1 : A) =
        a-α*(trace τ α hinv hα hanti hdiv a : A) := by
      have h := expand_coordinates τ α hinv hα hanti hdiv a
      change ((coordinates τ α hinv hα hanti hdiv a).1 : A) +
        α*(trace τ α hinv hα hanti hdiv a : A)=a at h
      linear_combination h
    exact he ▸ (𝓐 n).sub_mem ha hp
  · exact ht

end
end KLInvariance.ReflectionFrobenius
end


section
namespace KLInvariance.ReflectionFrobenius
open Module KLInvariance.Graded
universe uk uv us
variable {k : Type uk} [Field k] [CharZero k]
  {V : Type uv} [AddCommGroup V] [Module k V]
  {σ : Type us} [Fintype σ] (basis : Basis σ k V)
noncomputable section

 def polynomialLinear (v : V) : MvPolynomial σ k :=
  SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V v)

omit [CharZero k] in
 theorem polynomialLinear_homogeneous (v : V) :
    polynomialLinear basis v ∈ polynomialGrading k σ 1 := by
  classical
  unfold polynomialLinear
  rw [← basis.sum_repr v]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading k σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => (1:ℤ)) i)

 def polynomialAction (e : V ≃ₗ[k] V) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  ((SymmetricAlgebra.equivMvPolynomial basis).symm.trans (symmetricAction e)).trans
    (SymmetricAlgebra.equivMvPolynomial basis)

omit [CharZero k] [Fintype σ] in
@[simp] theorem polynomialAction_linear (e : V ≃ₗ[k] V) (v : V) :
    polynomialAction basis e (polynomialLinear basis v) = polynomialLinear basis (e v) := by
  simp [polynomialAction,polynomialLinear]

omit [CharZero k] in
 theorem polynomialAction_homogeneous (e : V ≃ₗ[k] V) {n : ℤ}
    {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    polynomialAction basis e p ∈ polynomialGrading k σ n := by
  apply algHom_polynomialGrading (polynomialAction basis e).toAlgHom _ hp
  intro i
  change polynomialAction basis e (MvPolynomial.X i) ∈ _
  have hx : MvPolynomial.X i = polynomialLinear basis (basis i) := by
    simp [polynomialLinear]
  rw [hx,polynomialAction_linear]
  exact polynomialLinear_homogeneous basis _

variable (root : V) (coroot : Dual k V) (hroot : coroot root=2)

 abbrev polynomialReflection : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  polynomialAction basis (Module.reflection hroot)

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_involutive : Function.Involutive
    (polynomialReflection basis root coroot hroot) := by
  intro p
  change SymmetricAlgebra.equivMvPolynomial basis
    (reflectionAction root coroot hroot
      ((SymmetricAlgebra.equivMvPolynomial basis).symm
        (SymmetricAlgebra.equivMvPolynomial basis
          (reflectionAction root coroot hroot
            ((SymmetricAlgebra.equivMvPolynomial basis).symm p)))))=p
  rw [AlgEquiv.symm_apply_apply,reflectionAction_involutive,AlgEquiv.apply_symm_apply]

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_anti : polynomialReflection basis root coroot hroot
    (polynomialLinear basis root) = -polynomialLinear basis root := by
  change SymmetricAlgebra.equivMvPolynomial basis
    (reflectionAction root coroot hroot
      ((SymmetricAlgebra.equivMvPolynomial basis).symm
        (SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V root)))) = _
  rw [AlgEquiv.symm_apply_apply,reflectionAction_anti,map_neg]
  rfl

omit [Fintype σ] in
include coroot hroot in
 theorem polynomialLinear_ne_zero : polynomialLinear basis root ≠ 0 := by
  intro h
  apply reflectionRoot_ne_zero root coroot hroot
  exact (SymmetricAlgebra.equivMvPolynomial basis).injective (by simpa [polynomialLinear] using h)

omit [CharZero k] [Fintype σ] in
 theorem polynomialReflection_divisible (p : MvPolynomial σ k) :
    polynomialLinear basis root ∣ p-polynomialReflection basis root coroot hroot p := by
  obtain ⟨d,hd⟩ := reflectionAction_divisible root coroot hroot
    ((SymmetricAlgebra.equivMvPolynomial basis).symm p)
  refine ⟨SymmetricAlgebra.equivMvPolynomial basis d,?_⟩
  simpa [polynomialLinear,polynomialReflection,polynomialAction] using
    congrArg (SymmetricAlgebra.equivMvPolynomial basis) hd

 def polynomialTrace : MvPolynomial σ k →ₗ[fixed (polynomialReflection basis root coroot hroot)]
    fixed (polynomialReflection basis root coroot hroot) :=
  trace _ _ (polynomialReflection_involutive basis root coroot hroot)
    (polynomialLinear_ne_zero basis root coroot hroot)
    (polynomialReflection_anti basis root coroot hroot)
    (polynomialReflection_divisible basis root coroot hroot)

 theorem polynomialTrace_homogeneous {n : ℤ} {p : MvPolynomial σ k}
    (hp : p ∈ polynomialGrading k σ n) :
    (polynomialTrace basis root coroot hroot p : MvPolynomial σ k) ∈ polynomialGrading k σ (n-1) :=
  trace_homogeneous _ _ _ _ _ _ (polynomialGrading k σ)
    (polynomialLinear_homogeneous basis root)
    (fun _ _ h => polynomialAction_homogeneous basis (Module.reflection hroot) h) hp

end
end KLInvariance.ReflectionFrobenius
end

end OAI
