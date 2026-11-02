/- Both routes inhabit exactly the same finite-only consumer contracts. -/
import PMFComparison.FiniteCovariance
import PMFComparison.TransportCovariance

noncomputable section
open scoped BigOperators
namespace QuantumExperiments.PMFComparison.Contracts

variable {I O : Type*} [Fintype O] {n : ℕ}

def VarianceClaim (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) : Prop :=
  Finite.variance (C.on_fin I O is) (fun os => ∑ k, g k (os k)) =
    ∑ k, Finite.variance (C.symb_dist (is k)) (g k)

def CovarianceClaim (C : DMChannel I O) (is : Fin n → I) (g h : Fin n → O → ℝ) : Prop :=
  Finite.covariance (C.on_fin I O is) (fun os => ∑ k, g k (os k))
    (fun os => ∑ k, h k (os k)) =
    ∑ k, Finite.covariance (C.symb_dist (is k)) (g k) (h k)

theorem native_variance (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    VarianceClaim C is g := Finite.variance_on_fin C is g

theorem transported_variance (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    VarianceClaim C is g := Transport.variance_on_fin C is g

theorem native_covariance (C : DMChannel I O) (is : Fin n → I) (g h : Fin n → O → ℝ) :
    CovarianceClaim C is g h := Finite.covariance_on_fin C is g h

theorem transported_covariance (C : DMChannel I O) (is : Fin n → I) (g h : Fin n → O → ℝ) :
    CovarianceClaim C is g h := Transport.covariance_on_fin C is g h

end QuantumExperiments.PMFComparison.Contracts
