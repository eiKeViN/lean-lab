import LegacyStructureActual
import Lean
open OAI.KLInvariance.MomentGraph
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c x : V)
#check Sheaf.structureSheaf
example : (Sheaf.structureSheaf G α c).vertex x = ModuleCat.of R (PLift (x ≤ c) → R) := rfl
example (e : E) : (Sheaf.structureSheaf G α c).upper e =
    LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp (LinearMap.proj h)) := rfl
example (e : E) : (Sheaf.structureSheaf G α c).lower e =
    LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp
      (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩)) := rfl
