import OAI.KL.Compatibility.KernelTransport

run_elab do
  let env ← Lean.getEnv
  let actual := env.header.moduleNames.filter (fun n => n.toString.startsWith "OAI." || n.toString.startsWith "ForMathlib.")
  let expected := #[`ForMathlib.LinearAlgebra.KernelTransport,
    `OAI.KL.Compatibility.KernelTransport]
  unless actual == expected do
    throwError "Unexpected local imports: {actual}"

section
variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

example (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) :
    OAI.KLInvariance.kernelSourceEquiv f e =
      OAI.LinearEquiv.kernelSourceEquiv f e := rfl

example (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) (x : LinearMap.ker f) :
    (OAI.KLInvariance.kernelSourceEquiv f e x).val = e x.val := rfl

example (f : M →ₗ[R] P) (e : M ≃ₗ[R] N)
    (y : LinearMap.ker (f.comp e.symm.toLinearMap)) :
    ((OAI.KLInvariance.kernelSourceEquiv f e).symm y).val = e.symm y.val := rfl

example (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    OAI.KLInvariance.kernelTargetEquiv f e =
      OAI.LinearEquiv.kernelTargetEquiv f e := rfl

example (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) (x : LinearMap.ker f) :
    (OAI.KLInvariance.kernelTargetEquiv f e x).val = x.val := rfl

example (f : M →ₗ[R] N) (e : N ≃ₗ[R] P)
    (y : LinearMap.ker (e.toLinearMap.comp f)) :
    ((OAI.KLInvariance.kernelTargetEquiv f e).symm y).val = y.val := rfl
end

section
variable {k A M N P Q : Type*} [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  [AddCommGroup Q] [Module k Q]

example (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q) :
    OAI.KLInvariance.kernelMixedEquiv f e g =
      OAI.LinearEquiv.kernelMixedEquiv f e g := rfl

example (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q)
    (x : LinearMap.ker f) :
    (OAI.KLInvariance.kernelMixedEquiv f e g x).val = e x.val := rfl

example (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q)
    (y : LinearMap.ker
      (g.toLinearMap.comp ((f.comp e.symm.toLinearMap).restrictScalars k))) :
    ((OAI.KLInvariance.kernelMixedEquiv f e g).symm y).val = e.symm y.val := rfl
end
