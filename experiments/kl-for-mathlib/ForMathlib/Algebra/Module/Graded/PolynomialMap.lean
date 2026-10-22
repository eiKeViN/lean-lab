module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.Generators

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.PolynomialMap. Source spans: Frobenius:11.
See migration.json and MIGRATION.md for exact provenance.
A multivariate polynomial algebra homomorphism preserves total degree when each variable has degree one. -/

namespace OAI

section
namespace KLInvariance.Graded
universe uk us
variable {k : Type uk} [Field k] {σ : Type us}

 theorem algHom_polynomialGrading (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hX : ∀ i, f (MvPolynomial.X i) ∈ polynomialGrading k σ 1)
    {n : ℤ} {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    f p ∈ polynomialGrading k σ n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (polynomialGrading k σ n).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (polynomialGrading k σ n).add_mem hp hq
  | monomial d c hd =>
    rw [MvPolynomial.monomial_eq,map_mul]
    have hc : f (MvPolynomial.C c)=MvPolynomial.C c := f.commutes c
    rw [hc]
    apply MvPolynomial.IsWeightedHomogeneous.C_mul
    simp only [Finsupp.prod,map_prod,map_pow]
    have hh := SetLike.prod_pow_mem_graded (polynomialGrading k σ)
      (fun _ : σ => (1:ℤ)) (fun i => f (MvPolynomial.X i)) d (F := d.support)
      (fun i _ => hX i)
    simpa only [Finsupp.weight_apply,Finsupp.sum] using hd ▸ hh

end KLInvariance.Graded
end

end OAI
