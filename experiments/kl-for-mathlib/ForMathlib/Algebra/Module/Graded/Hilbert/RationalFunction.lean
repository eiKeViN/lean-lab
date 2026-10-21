import Mathlib

/-! Semantic home: ForMathlib.Algebra.Module.Graded.Hilbert.RationalFunction. Source spans: IntegralPairings:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Hilbert
open Polynomial

 theorem hasSum_shift_coeff {f : ℤ → ℝ} {q c : ℝ} (hq : q≠0)
    (hf : HasSum (fun n : ℤ => f n*q^n) c) (d : ℤ) :
    HasSum (fun n : ℤ => f (n-d)*q^n) (q^d*c) := by
  apply (Equiv.addRight d).hasSum_iff.mp
  apply (hf.mul_left (q^d)).congr_fun
  intro n
  change f (n+d-d)*q^(n+d)=q^d*(f n*q^n)
  rw [add_sub_cancel_right,zpow_add₀ hq]
  ring

 theorem numerator_unique (f : ℤ → ℕ) (F G : ℤ[X]) (D : ℝ → ℝ)
    (hD : ∀ q, 0<q → q<1 → D q≠0)
    (hF : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q F*D q))
    (hG : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q G*D q)) : F=G := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.Ioo (0 : ℝ) 1) ?_ (Set.Ioo_infinite (by norm_num))
  intro q hq
  have he := (hF q hq.1 hq.2).unique (hG q hq.1 hq.2)
  change eval q (F.map (Int.castRingHom ℝ))=eval q (G.map (Int.castRingHom ℝ))
  simpa only [eval_map] using (mul_right_cancel₀ (hD q hq.1 hq.2) he)

 theorem numerator_add_shift (f g h : ℤ → ℕ) (F G H : ℤ[X]) (D : ℝ → ℝ)
    (hD : ∀ q, 0<q → q<1 → D q≠0)
    (hF : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q F*D q))
    (hG : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (g n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q G*D q))
    (hH : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (h n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q H*D q))
    (he : ∀ n, f n=g n+h (n-1)) : F=G+X*H := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.Ioo (0 : ℝ) 1) ?_ (Set.Ioo_infinite (by norm_num))
  intro q hq
  have hh := hasSum_shift_coeff hq.1.ne' (hH q hq.1 hq.2) 1
  have hs := (hG q hq.1 hq.2).add hh
  have hf := hF q hq.1 hq.2
  have heq : eval₂ (Int.castRingHom ℝ) q F*D q=
      eval₂ (Int.castRingHom ℝ) q G*D q+q*(eval₂ (Int.castRingHom ℝ) q H*D q) := by
    rw [zpow_one] at hs
    apply hf.unique
    apply hs.congr_fun
    intro n
    rw [he,Nat.cast_add,add_mul]
  change eval q (F.map (Int.castRingHom ℝ))=eval q ((G+X*H).map (Int.castRingHom ℝ))
  simp only [eval_map,eval₂_add,eval₂_mul,eval₂_X]
  apply mul_right_cancel₀ (hD q hq.1 hq.2)
  calc
    _ = eval₂ (Int.castRingHom ℝ) q G*D q+q*(eval₂ (Int.castRingHom ℝ) q H*D q) := heq
    _ = _ := by ring

end KLInvariance.Hilbert
end

end OAI
