import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

private def quotientLinear (e : E) : R →ₗ[R] R ⧸ Ideal.span {α e} :=
  (Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap

 def structureSheaf : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (PLift (x ≤ c) → R)
  edge e := ModuleCat.of R (PLift (G.target e ≤ c) → R ⧸ Ideal.span {α e})
  upper e := LinearMap.pi (fun h => (quotientLinear α e).comp (LinearMap.proj h))
  lower e := LinearMap.pi (fun h => (quotientLinear α e).comp
    (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩))


end
end KLInvariance.MomentGraph.Sheaf
end
end OAI
