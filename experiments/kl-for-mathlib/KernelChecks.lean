import ForMathlib.LinearAlgebra.KernelTransport

-- Independent import: no local KL, Bott or sheaf module may enter this harness.
run_elab do
  let env ← Lean.getEnv
  let actual := env.header.moduleNames.filter (fun n => n.toString.startsWith "OAI." || n.toString.startsWith "ForMathlib.")
  unless actual == #[`ForMathlib.LinearAlgebra.KernelTransport] do
    throwError "Unexpected local imports: {actual}"
  for name in #[`OAI.LinearEquiv.kernelSourceEquiv,
      `OAI.LinearEquiv.kernelTargetEquiv, `OAI.LinearEquiv.kernelMixedEquiv] do
    let some (.defnInfo info) := env.find? name
      | throwError "Expected a definition: {name}"
    let refs := info.value.getUsedConstants.filter
      (·.toString.startsWith "LinearEquiv.")
    Lean.logInfo m!"{name}: Mathlib LinearEquiv references {refs}"

namespace OAI.LinearEquiv
run_elab do
  for name in #[`LinearEquiv.coe_coe, `LinearEquiv.symm_apply_apply,
      `LinearEquiv.apply_symm_apply] do
    let resolved ← Lean.resolveGlobalConstNoOverload (Lean.mkIdent name)
    unless resolved == name do
      throwError "Mathlib name shadowed: {name} resolved to {resolved}"
end OAI.LinearEquiv

section
variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

example (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) (x : LinearMap.ker f) :
    (OAI.LinearEquiv.kernelSourceEquiv f e x).val = e x.val := rfl

example (f : M →ₗ[R] P) (e : M ≃ₗ[R] N)
    (y : LinearMap.ker (f.comp e.symm.toLinearMap)) :
    ((OAI.LinearEquiv.kernelSourceEquiv f e).symm y).val = e.symm y.val := rfl

example (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) (x : LinearMap.ker f) :
    (OAI.LinearEquiv.kernelTargetEquiv f e x).val = x.val := rfl

example (f : M →ₗ[R] N) (e : N ≃ₗ[R] P)
    (y : LinearMap.ker (e.toLinearMap.comp f)) :
    ((OAI.LinearEquiv.kernelTargetEquiv f e).symm y).val = y.val := rfl
end

section
variable {k A M N P Q : Type*} [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  [AddCommGroup Q] [Module k Q]

example (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q)
    (x : LinearMap.ker f) :
    (OAI.LinearEquiv.kernelMixedEquiv f e g x).val = e x.val := rfl

example (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q)
    (y : LinearMap.ker
      (g.toLinearMap.comp ((f.comp e.symm.toLinearMap).restrictScalars k))) :
    ((OAI.LinearEquiv.kernelMixedEquiv f e g).symm y).val = e.symm y.val := rfl

example (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q)
    (c : k) (x : LinearMap.ker f) :
    OAI.LinearEquiv.kernelMixedEquiv f e g (c • x) =
      c • OAI.LinearEquiv.kernelMixedEquiv f e g x :=
  map_smul (OAI.LinearEquiv.kernelMixedEquiv f e g) c x
end

-- Full kernel, zero kernel, a nontrivial coordinate change, and distinct scalars.
example (q : ℚ) :
    (OAI.LinearEquiv.kernelSourceEquiv (0 : ℚ →ₗ[ℚ] ℚ)
      (LinearEquiv.refl ℚ ℚ) ⟨q, rfl⟩).val = q := rfl

example (x : LinearMap.ker (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) :
    (OAI.LinearEquiv.kernelSourceEquiv LinearMap.id
      (LinearEquiv.refl ℚ ℚ) x).val = 0 := x.property

example (q : ℚ) :
    (OAI.LinearEquiv.kernelSourceEquiv (LinearMap.fst ℚ ℚ ℚ)
      (LinearEquiv.prodComm ℚ ℚ ℚ) ⟨(0, q), rfl⟩).val = (q, 0) := rfl

example (z : ℂ) :
    (OAI.LinearEquiv.kernelMixedEquiv (LinearMap.fst ℂ ℂ ℂ)
      (LinearEquiv.prodComm ℂ ℂ ℂ) Complex.equivRealProdCLM.toLinearEquiv
      ⟨(0, z), rfl⟩).val = (z, 0) := rfl
