module
public import ForMathlib.LinearAlgebra.KernelTransport

public section

/-! Preserve the original KL kernel-transport names and explicit types. -/

namespace OAI

section

namespace KLInvariance
universe ur um un up
variable {R : Type ur} [Ring R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]

@[expose] def kernelSourceEquiv (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (f.comp e.symm.toLinearMap) :=
  _root_.OAI.LinearEquiv.kernelSourceEquiv f e

end KLInvariance

end

section

namespace KLInvariance
universe ur um un up
variable {R : Type ur} [Ring R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]

@[expose] def kernelTargetEquiv (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (e.toLinearMap.comp f) :=
  _root_.OAI.LinearEquiv.kernelTargetEquiv f e

end KLInvariance

end

section

namespace KLInvariance
universe uk ua um un up uq
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  {P : Type up} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  {Q : Type uq} [AddCommGroup Q] [Module k Q]

@[expose] def kernelMixedEquiv (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q) :
    LinearMap.ker f ≃ₗ[k] LinearMap.ker
      (g.toLinearMap.comp ((f.comp e.symm.toLinearMap).restrictScalars k)) :=
  _root_.OAI.LinearEquiv.kernelMixedEquiv f e g

end KLInvariance

end

end OAI
