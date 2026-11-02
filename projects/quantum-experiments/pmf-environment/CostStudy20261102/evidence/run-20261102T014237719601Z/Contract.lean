import CostStudy.NativeConsumer
import CostStudy.BridgeConsumer
noncomputable section
open scoped BigOperators
open QuantumExperiments.PMFComparison
variable {I O : Type*} [Fintype O] {n : ℕ}
example (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ k, g k (os k)) =
      ∑ k, Finite.variance (C.symb_dist (is k)) (g k) := Finite.variance_on_fin C is g
example (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ k, g k (os k)) =
      ∑ k, Finite.variance (C.symb_dist (is k)) (g k) := Transport.variance_on_fin C is g
