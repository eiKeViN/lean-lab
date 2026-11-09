module
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom
import Lean
open OAI.KLInvariance.Graded OAI.KLInvariance.MomentGraph
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E D : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)
  [Fintype V] [Fintype D] [IsNoetherianRing A]
  (τ : D → V) (α : D → A) (hα : ∀ d, α d ∈ 𝓐 1)
  (C : ModuleData.MinimalCover (B.attachImage τ α hα))
example (z : C.source) :
    (B.attachStalkMap τ α hα C).map z = (C.hom.map z).val := rfl
example (z : C.source) (d : D) :
    (B.attachStalkMap τ α hα C).map z d = (C.hom.map z).val d := rfl
example : (B.extendBottom τ α hα C).vertex ⊥ = C.source := rfl
example (x : V) : (B.extendBottom τ α hα C).vertex (x : WithBot V) = B.vertex x := rfl
example (d : D) :
    (B.extendBottom τ α hα C).lower (Sum.inr d) =
      (ModuleData.projection (B.attachEdges τ α hα) d).comp (B.attachStalkMap τ α hα C) := rfl
example (z : C.source) (f : B.forget.Assignment) : B.attachAssignment τ α hα C z f ⊥ = z := rfl
#check GradedSheaf.lift_global
#check GradedSheaf.extendBottom_generated
#check GradedSheaf.extendBottom_edgeFlabby
run_elab do
  let env ← Lean.getEnv
  for n in #[``GradedSheaf.attachStalkMap, ``GradedSheaf.extendBottom, ``GradedSheaf.attachAssignment] do
    let some (.defnInfo _) := env.find? n | throwError "Body not exposed: {n}"
  IO.println "Ordinary modern consumer: exposed bodies, stalk-map/extension/assignment rfl pass."
