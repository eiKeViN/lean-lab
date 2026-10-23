import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
import Lean
open OAI.KLInvariance.MomentGraph
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}
  {G : OrderedGraph V E} (B : Sheaf.{u,v,w,z} (R := R) G) (x : V)
#check Sheaf.stalkMap.eq_1
example (b : B.vertex x) (e : Sheaf.Outgoing (G := G) x) :
    B.stalkMap x b e = B.lower e.val (e.property.symm ▸ b) := rfl
example (b : B.vertex x) (e : Sheaf.Outgoing (G := G) x) :
    B.stalkMap x b e = B.lower e.val (e.property.symm ▸ b) := by
  rw [Sheaf.stalkMap.eq_1]
  rfl
example (b : B.vertex x) (e : Sheaf.Outgoing (G := G) x) :
    B.stalkMap x b e = B.lower e.val (e.property.symm ▸ b) := by
  simp only [Sheaf.stalkMap.eq_1]
  rfl
