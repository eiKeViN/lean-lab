module
import ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex
import Lean
open OAI.KLInvariance OAI.KLInvariance.MomentGraph
open scoped BigOperators
section Bruhat
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
  (cs : CoxeterSystem M W) (a b : W) (e : BruhatGraph.Edge cs a b)
example : (BruhatGraph.graph cs a b).source e = e.val.1 := rfl
example : (BruhatGraph.graph cs a b).target e = e.val.2 := rfl
example : BruhatGraph.label cs a b e = e.val.2.val * e.val.1.val⁻¹ := rfl
example : BruhatGraph.label cs a b e * (BruhatGraph.source cs a b e).val =
    (BruhatGraph.target cs a b e).val := by simp only [BruhatGraph.label_mul_source]
end Bruhat
section Reindex
open OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
  (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
example (x : V) : (B.reindex e).vertex x = B.vertex (e.vertex x) := rfl
example (f : B.forget.Assignment) (x : V) : B.reindexAssignment e f x = f (e.vertex x) := rfl
example (f : B.forget.Assignment) : B.unreindexAssignment e (B.reindexAssignment e f) = f := by
  simp only [GradedSheaf.unreindex_reindexAssignment]
#check GradedSheaf.reindex_lower
#check GradedSheaf.reindex_upper
#check GradedSheaf.reindex_edgeFlabby
end Reindex
section Duality
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)
  [Fintype E] [DecidableEq V]
example (α : E → R) : Sheaf.labelProduct α = ∏ e, α e := rfl
example (α : E → R) (x : V) : Sheaf.incomingProduct (G := G) α x =
    ∏ e ∈ Sheaf.incoming (G := G) x, α e := rfl
example (x : V) (v : B.singleStalk x) :
    (B.singleStalkEquivSupport x v).val.val = Pi.single x v.val := rfl
example (x : V) (v : B.singleStalk x) :
    (B.singleStalkEquivSupport x).symm (B.singleStalkEquivSupport x v) = v :=
  (B.singleStalkEquivSupport x).symm_apply_apply v
#check Sheaf.kernelEquivSingleStalk
end Duality
run_elab do
  let env ← Lean.getEnv
  for n in #[``BruhatGraph.graph, ``BruhatGraph.label, ``GradedSheaf.reindex,
      ``GradedSheaf.reindexAssignment, ``Sheaf.singleStalkEquivSupport] do
    let some (.defnInfo _) := env.find? n | throwError "Missing exposed body: {n}"
  IO.println "Ordinary modern graph/reindex/duality consumers: rfl, simp, inverse and body access pass."
