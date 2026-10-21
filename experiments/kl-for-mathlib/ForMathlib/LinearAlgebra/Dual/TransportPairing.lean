import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.Dual.TransportPairing. Source spans: BalancedPairings:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace TransportPerfectPairing
open Module
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

theorem balanced (e : M ≃ₗ[A] N) (D : M ≃ₗ[A] Dual A M) (a : End A M)
    (h : ∀ x y, D (a x) y = D x (a y)) (s z : N) :
    (e.symm.trans (D.trans e.symm.dualMap))
      ((e.toLinearMap.comp (a.comp e.symm.toLinearMap)) s) z =
    (e.symm.trans (D.trans e.symm.dualMap)) s
      ((e.toLinearMap.comp (a.comp e.symm.toLinearMap)) z) := by
  change D (e.symm (e (a (e.symm s)))) (e.symm z) =
    D (e.symm s) (e.symm (e (a (e.symm z))))
  simp only [LinearEquiv.symm_apply_apply]
  exact h _ _

theorem symmetric (e : M ≃ₗ[A] N) (D : M ≃ₗ[A] Dual A M)
    (h : ∀ x y, D x y = D y x) (s z : N) :
    (e.symm.trans (D.trans e.symm.dualMap)) s z =
    (e.symm.trans (D.trans e.symm.dualMap)) z s :=
  h (e.symm s) (e.symm z)

end TransportPerfectPairing
end

end OAI
