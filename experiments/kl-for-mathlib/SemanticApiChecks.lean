module
import ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover
import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange
import ForMathlib.Algebra.Module.CoefficientChange.Dual
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure
import Lean

open OAI.KLInvariance
open Lean Elab Command

run_elab do
  let env ← getEnv
  for n in #[`OAI.KLInvariance.LocalCover.splitEquiv,
      `OAI.KLInvariance.CoefficientChange.equivVal,
      `OAI.KLInvariance.CoefficientChange.map,
      `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient,
      `OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback] do
    unless (env.find? n).any (fun ci => ci.hasValue) do
      throwError "Lost transparent computation control: {n}"
  logInfo "Round 2: all selected computation interfaces exposed."

section
variable {R B P : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P]
  (g : B →ₗ[R] P) (s : P →ₗ[R] B) (hs : g.comp s = LinearMap.id)

-- Simplifier controls also run with splitEquiv hidden in the bounded trial.
example (b : B) : ((LocalCover.splitEquiv g s hs b).1,
    ((LocalCover.splitEquiv g s hs b).2 : B)) = (g b, b - s (g b)) := by simp

example (p : P × LinearMap.ker g) :
    (LocalCover.splitEquiv g s hs).symm p = s p.1 + p.2 := by simp

-- A reconstruction identity, expressed entirely in coordinates.
example (b : B) : s (LocalCover.splitEquiv g s hs b).1 +
    (LocalCover.splitEquiv g s hs b).2 = b := by
  rw [LocalCover.splitEquiv_apply_fst, LocalCover.splitEquiv_apply_snd_coe]
  abel

-- Both directions are usable without unfolding the equivalence.
example (p : P × LinearMap.ker g) :
    g ((LocalCover.splitEquiv g s hs).symm p) = p.1 := by
  rw [LocalCover.splitEquiv_symm_apply, map_add,
    show g (s p.1) = p.1 from LinearMap.congr_fun hs p.1,
    LinearMap.mem_ker.mp p.2.property, add_zero]

end

section
variable {k A B M N Q : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup Q] [Module A Q]
  (e : A ≃ₐ[k] B) (f : M →ₗ[A] N) (g : N →ₗ[A] Q)

-- Existing ext plus the value rule proves functoriality; no new ext rule.
example (m : CoefficientChange e M) :
    CoefficientChange.map e LinearMap.id (CoefficientChange.map e (g.comp f) m) =
      CoefficientChange.map e g (CoefficientChange.map e f m) := by
  ext
  simp

-- The wrapper remains an intentional transparent computation interface.
example (m : CoefficientChange e M) : CoefficientChange.equivVal e M m = m.val := rfl

-- map retains its computation contract after the wider sheaf trial failed.
example (m : CoefficientChange e M) : (CoefficientChange.map e f m).val = f m.val := by
  rfl
end

section
open OAI.KLInvariance.MomentGraph.Sheaf TensorProduct
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

-- Pullback through two implications commutes with quotient reduction.
example (a : R) (p q t : Prop) (h : q → p) (j : t → q)
    (v : PLift p → R) (x : PLift t) :
    quotientPullback a p t (h ∘ j) v x =
      quotientPullback a p q h v ⟨j x.down⟩ := by simp

example (a : R) (p q : Prop) (h : q → p) (v : PLift p → R) (x : PLift q) :
    quotientPullback a p q h v x = Ideal.Quotient.mk _ (v ⟨h x.down⟩) := by
  exact quotientPullback_apply a p q h v x

-- The generic equivalence API derives the inverse formula from the existing
-- pure-tensor rule, with no inverse implementation exported.
example (a r : R) (s : S) :
    (baseChangeQuotient S a).symm (Ideal.Quotient.mk _ (s * algebraMap R S r)) =
      s ⊗ₜ[R] Ideal.Quotient.mk _ r := by
  apply (baseChangeQuotient S a).injective
  simp only [LinearEquiv.apply_symm_apply, baseChangeQuotient_tmul]
end

#print axioms OAI.KLInvariance.LocalCover.splitEquiv_apply_fst
#print axioms OAI.KLInvariance.LocalCover.splitEquiv_apply_snd_coe
#print axioms OAI.KLInvariance.LocalCover.splitEquiv_symm_apply
#print axioms OAI.KLInvariance.CoefficientChange.val_map
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback_apply
#print axioms OAI.KLInvariance.Graded.ModuleData.Hom.splitEquiv_graded
#print axioms OAI.KLInvariance.Graded.ModuleData.Hom.kernel_free_of_split
#print axioms OAI.KLInvariance.Graded.ModuleData.changeHom
#print axioms OAI.KLInvariance.CoefficientChange.mapEquiv
#print axioms OAI.KLInvariance.CoefficientChange.pairingEquiv_apply
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.baseChangePi_natural

#print axioms OAI.KLInvariance.CoefficientChange.map_id_apply
#print axioms OAI.KLInvariance.Graded.ModuleData.changeTop_split

#print axioms OAI.KLInvariance.LocalCover.splitEquiv.congr_simp
