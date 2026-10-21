import Mathlib
import ForMathlib.Algebra.Module.Graded.HomogeneousDual
import ForMathlib.Algebra.Module.Graded.ModuleData.Character
import ForMathlib.Algebra.Module.Graded.ModuleData.Equality
import ForMathlib.Algebra.Module.Graded.ModuleData.Transport

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.Duality. Source spans: Support:5, Support:1, Support:14.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

 theorem equivOfEq_inverse {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) (m : M) :
    equivOfEq h.symm (equivOfEq h m)=m := by
  subst N
  rfl

 def homOfEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) : Hom M N :=
  ⟨(equivOfEq h).toLinearMap,equivOfEq_graded h⟩

end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n=⊥)
noncomputable section

 theorem unit_endomorphisms_commute (f g : Hom (unit.{uk,ua,um} hneg) (unit hneg))
    (v : unit hneg) : f.map (g.map v)=g.map (f.map v) := by
  let z : unit.{uk,ua,um} hneg := fun _ => (1 : A)
  have he (w : unit.{uk,ua,um} hneg) : w=w PUnit.unit • z := by
    funext j
    change w j=w PUnit.unit * 1
    simp only [mul_one]
  have hf (w : unit.{uk,ua,um} hneg) : f.map w=w PUnit.unit • f.map z := by
    conv_lhs => rw [he w]
    exact map_smul f.map _ z
  have hg (w : unit.{uk,ua,um} hneg) : g.map w=w PUnit.unit • g.map z := by
    conv_lhs => rw [he w]
    exact map_smul g.map _ z
  rw [hf (g.map v),hg (f.map v),hg v,hf v]
  funext j
  change (v PUnit.unit * (g.map z) PUnit.unit) * (f.map z) j =
    (v PUnit.unit * (f.map z) PUnit.unit) * (g.map z) j
  have hej : j=PUnit.unit := Subsingleton.elim _ _
  subst j
  ring

 theorem unit_split_reverse (f g : Hom (unit.{uk,ua,um} hneg) (unit hneg))
    (h : ∀ v, g.map (f.map v)=v) (v : unit hneg) : f.map (g.map v)=v :=
  (unit_endomorphisms_commute hneg f g v).trans (h v)


 theorem split_reverse_of_unit {B N : ModuleData.{uk,ua,um} 𝓐}
    (hB : B=unit hneg) (o : Hom N (unit hneg)) (o' : Hom (unit hneg) N)
    (ho : ∀ v, o'.map (o.map v)=v) (i : Hom B N) (p : Hom N B)
    (hpi : ∀ v, p.map (i.map v)=v) (v : N) : i.map (p.map v)=v := by
  subst B
  have hp : ∀ a, (p.comp o').map ((o.comp i).map a)=a := by
    intro a
    change p.map (o'.map (o.map (i.map a)))=a
    rw [ho]
    exact hpi a
  have hh := unit_split_reverse hneg (o.comp i) (p.comp o') hp (o.map v)
  change o.map (i.map (p.map (o'.map (o.map v))))=o.map v at hh
  rw [ho] at hh
  exact (ho _).symm.trans ((congrArg o'.map hh).trans (ho v))

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

omit [Finite σ] in
 theorem degree_le_of_dual_equiv
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l))
    (c : NonnegativeBasis (σ := σ) M.piece) (i : c.index) : c.degree i ≤ l := by
  classical
  have h := he (-(c.degree i : ℤ)) (c.basis.dualBasis i)
    (dualBasis_homogeneous (polynomialGrading k σ) M.piece c.basis
      (fun i => (c.degree i : ℤ)) c.homogeneous i)
  by_contra hn
  have hn' : -(c.degree i : ℤ)+(l:ℤ)<0 := by omega
  rw [N.nonneg _ hn',Submodule.mem_bot] at h
  have hz := e.injective (show e (c.basis.dualBasis i)=e 0 from
    h.trans (map_zero e).symm)
  exact c.basis.dualBasis.ne_zero i hz

 def reflectedBasis
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l))
    (c : NonnegativeBasis (σ := σ) M.piece) : NonnegativeBasis (σ := σ) N.piece := by
  classical
  exact {
    index := c.index
    finite := c.finite
    basis := c.basis.dualBasis.map e
    degree := fun i => l-c.degree i
    homogeneous := fun i => by
      have hi := M.degree_le_of_dual_equiv N e l he c i
      have h := he (-(c.degree i : ℤ)) (c.basis.dualBasis i)
        (dualBasis_homogeneous (polynomialGrading k σ) M.piece c.basis
          (fun i => (c.degree i : ℤ)) c.homogeneous i)
      change e (c.basis.dualBasis i) ∈ N.piece ((l-c.degree i : ℕ):ℤ)
      have hd : ((l-c.degree i : ℕ):ℤ)=-(c.degree i : ℤ)+(l:ℤ) := by omega
      rw [hd]
      exact h }

 theorem char_of_dual_equiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N]
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l)) :
    N.char=Polynomial.reflect l M.char := by
  classical
  let c := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ (M.reflectedBasis N e l he c),char,character_eq _ _ c]
  change (∑ i : c.index, (X : Polynomial ℤ)^(l-c.degree i))=
    Polynomial.reflect l (∑ i : c.index, X^c.degree i)
  have hs (s : Finset c.index) : Polynomial.reflect l (∑ i∈s, (X : Polynomial ℤ)^c.degree i)=
      ∑ i∈s, Polynomial.reflect l (X^c.degree i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha,ih]
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.reflect_monomial,Polynomial.revAt_le (M.degree_le_of_dual_equiv N e l he c i)]

end
end KLInvariance.Graded.ModuleData
end

end OAI
