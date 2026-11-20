/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.PhaseTraceDistance
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Untouched finite reference systems

Tensoring a matrix with the identity of a nonzero finite reference system preserves its
operator norm. The proof decomposes a vector into orthogonal reference-coordinate fibers.
This supplies a dimension-independent trace-norm bound for amplified unitary channels.

## Main results

* `norm_kronecker_one`: identity-reference extension preserves the operator norm.
* `traceNorm_amplified_le_phaseDistance`: amplified error for arbitrary matrix inputs.
* `traceDistance_reference_unitary_le_phaseDistance`: entangled mixed-state output bound.
* `unitaryDiamondDistance_le_phaseDistance`: the unnormalized diamond bound `2 δ`.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator Kronecker ENNReal

namespace Giallar

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R]

/-- One reference-coordinate fiber of a joint vector, with its Hilbert-space norm. -/
def referenceFiber (x : EuclideanSpace ℂ (ι × R)) (r : R) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => x (i, r))

omit [DecidableEq ι] in
/-- Identity-reference tensor products act separately on reference-coordinate fibers. -/
theorem kronecker_one_mulVec (A : Matrix ι ι ℂ) (x : (ι × R) → ℂ) (i : ι) (r : R) :
    ((A ⊗ₖ (1 : Matrix R R ℂ)).mulVec x) (i, r) =
      (A.mulVec fun j => x (j, r)) i := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

omit [DecidableEq ι] [DecidableEq R] in
/-- The joint squared norm is the sum of squared fiber norms. -/
theorem norm_sq_eq_sum_fibers (x : EuclideanSpace ℂ (ι × R)) :
    ‖x‖ ^ 2 = ∑ r : R, ‖referenceFiber x r‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, referenceFiber]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Extending a finite operator by an identity reference cannot increase its operator norm. -/
theorem norm_kronecker_one_le (A : Matrix ι ι ℂ) :
    ‖A ⊗ₖ (1 : Matrix R R ℂ)‖ ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [norm_sq_eq_sum_fibers, mul_pow, norm_sq_eq_sum_fibers, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hf : referenceFiber (Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix R R ℂ)) x) r =
      Matrix.toEuclideanCLM (𝕜 := ℂ) A (referenceFiber x r) := by
    ext i
    exact kronecker_one_mulVec A x i r
  rw [hf]
  simpa only [mul_pow, Matrix.l2_opNorm_toEuclideanCLM] using
    (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (referenceFiber x r))

/-- Embed a vector into a single computational-basis reference coordinate. -/
def referenceEmbed (r : R) (x : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (ι × R) :=
  WithLp.toLp 2 (fun z => if z.2 = r then x z.1 else 0)

omit [DecidableEq ι] in
/-- Embedding in a unit reference vector preserves the Hilbert-space norm. -/
theorem norm_referenceEmbed (r : R) (x : EuclideanSpace ℂ ι) :
    ‖referenceEmbed r x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, referenceEmbed, Fintype.sum_prod_type, apply_ite]

/-- Extension by an identity intertwines the unit-reference embedding. -/
theorem kronecker_one_referenceEmbed (A : Matrix ι ι ℂ) (r : R)
    (x : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix R R ℂ)) (referenceEmbed r x) =
      referenceEmbed r (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) := by
  ext z
  rcases z with ⟨i, s⟩
  rw [Matrix.ofLp_toEuclideanCLM]
  rw [kronecker_one_mulVec]
  by_cases hs : s = r
  · simp [referenceEmbed, hs]
  · simp [referenceEmbed, hs, Matrix.mulVec, dotProduct]

/-- A nonzero reference system also provides the reverse operator-norm inequality. -/
theorem norm_le_kronecker_one [Nonempty R] (A : Matrix ι ι ℂ) :
    ‖A‖ ≤ ‖A ⊗ₖ (1 : Matrix R R ℂ)‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM (A := A)]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let r : R := Classical.choice inferInstance
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix R R ℂ))).le_opNorm
    (referenceEmbed r x)
  simpa only [kronecker_one_referenceEmbed, norm_referenceEmbed,
    Matrix.l2_opNorm_toEuclideanCLM] using h

/-- Identity-reference extension preserves operator norm, uniformly in reference dimension. -/
theorem norm_kronecker_one [Nonempty R] (A : Matrix ι ι ℂ) :
    ‖A ⊗ₖ (1 : Matrix R R ℂ)‖ = ‖A‖ :=
  le_antisymm (norm_kronecker_one_le A) (norm_le_kronecker_one A)

/-- Extend a unitary operator by the identity action on the finite reference system. -/
noncomputable def unitaryReference (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (ι × R) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ),
    Matrix.kronecker_mem_unitary U.property (unitary (Matrix R R ℂ)).one_mem⟩

omit [Fintype ι] [DecidableEq ι] [Fintype R] in
/-- Tensoring both operands with a fixed identity commutes with subtraction. -/
theorem sub_kronecker_one (A B : Matrix ι ι ℂ) :
    (A - B) ⊗ₖ (1 : Matrix R R ℂ) =
      A ⊗ₖ (1 : Matrix R R ℂ) - B ⊗ₖ (1 : Matrix R R ℂ) := by
  ext x y
  simp [Matrix.kroneckerMap_apply, sub_mul]

/-- The full amplified-channel bound holds for every input matrix, including matrices entangled
with the reference system. The factor two uses the unnormalized trace-norm convention. -/
theorem traceNorm_amplified_conjugation_sub_le [Nonempty ι] [Nonempty R]
    (U V : Matrix.unitaryGroup ι ℂ) (X : Matrix (ι × R) (ι × R) ℂ) :
    (((U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ)) * X *
        ((U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ))ᴴ -
      ((V : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ)) * X *
        ((V : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ))ᴴ).traceNorm ≤
      2 * ‖(U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)‖ * X.traceNorm := by
  have h := traceNorm_conjugation_sub_le
    (unitaryReference (R := R) U) (unitaryReference (R := R) V) X
  have hnorm :
      ‖((unitaryReference (R := R) U : Matrix.unitaryGroup (ι × R) ℂ) :
          Matrix (ι × R) (ι × R) ℂ) -
        ((unitaryReference (R := R) V : Matrix.unitaryGroup (ι × R) ℂ) :
          Matrix (ι × R) (ι × R) ℂ)‖ = ‖(U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)‖ := by
    change ‖(U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ) -
      (V : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ)‖ = _
    rw [← sub_kronecker_one, norm_kronecker_one]
  rw [hnorm] at h
  exact h

/-- Unitary conjugation difference on a joint system with an untouched finite reference. -/
def amplifiedDifference (U V : Matrix.unitaryGroup ι ℂ)
    (X : Matrix (ι × R) (ι × R) ℂ) : Matrix (ι × R) (ι × R) ℂ :=
  ((U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ)) * X *
      ((U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ))ᴴ -
    ((V : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ)) * X *
      ((V : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix R R ℂ))ᴴ

/-- The unnormalized diamond distance of two unitary conjugation channels. The supremum
ranges over every positive finite reference dimension and every matrix, not only states.
The zero matrix contributes zero by the convention `0 / 0 = 0`. -/
noncomputable def unitaryDiamondDistance (U V : Matrix.unitaryGroup ι ℂ) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ X : Matrix (ι × Fin (r + 1)) (ι × Fin (r + 1)) ℂ,
    ENNReal.ofReal ((amplifiedDifference U V X).traceNorm / X.traceNorm)

/-- The dimension-independent amplified bound controls the actual diamond supremum. -/
theorem unitaryDiamondDistance_le [Nonempty ι] (U V : Matrix.unitaryGroup ι ℂ) :
    unitaryDiamondDistance U V ≤
      ENNReal.ofReal (2 * ‖(U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)‖) := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  apply ENNReal.ofReal_le_ofReal
  by_cases hX : X.traceNorm = 0
  · simp [hX]
  · have hpos : 0 < X.traceNorm := lt_of_le_of_ne (Matrix.traceNorm_nonneg X) (Ne.symm hX)
    apply (div_le_iff₀ hpos).mpr
    exact traceNorm_amplified_conjugation_sub_le U V X

omit [Fintype ι] [DecidableEq ι] [Fintype R] in
/-- Scalar multiplication commutes with identity-reference extension. -/
theorem smul_kronecker_one (A : Matrix ι ι ℂ) (z : ℂ) :
    (z • A) ⊗ₖ (1 : Matrix R R ℂ) = z • (A ⊗ₖ (1 : Matrix R R ℂ)) := by
  ext x y
  simp [Matrix.kroneckerMap_apply, mul_assoc]

/-- A global phase does not change an amplified conjugation channel. -/
theorem amplifiedDifference_phase (U V : Matrix.unitaryGroup ι ℂ)
    (X : Matrix (ι × R) (ι × R) ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    amplifiedDifference U (scaleUnitary z hz V) X = amplifiedDifference U V X := by
  change _ - ((z • (V : Matrix ι ι ℂ)) ⊗ₖ (1 : Matrix R R ℂ)) * X *
    ((z • (V : Matrix ι ι ℂ)) ⊗ₖ (1 : Matrix R R ℂ))ᴴ = _
  rw [smul_kronecker_one, conjugation_scale_phase z hz]
  rfl

/-- The amplified-channel error is controlled by the attained global-phase distance. -/
theorem traceNorm_amplified_le_phaseDistance [Nonempty ι] [Nonempty R]
    (U V : Matrix.unitaryGroup ι ℂ) (X : Matrix (ι × R) (ι × R) ℂ) :
    (amplifiedDifference U V X).traceNorm ≤
      2 * phaseDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) * X.traceNorm := by
  let z := optimalPhase (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)
  have hz : ‖z‖ = 1 := norm_optimalPhase _ _
  have h := traceNorm_amplified_conjugation_sub_le U (scaleUnitary z hz V) X
  change (amplifiedDifference U (scaleUnitary z hz V) X).traceNorm ≤ _ at h
  rw [amplifiedDifference_phase] at h
  exact h

/-- Joint mixed states, including entangled inputs, inherit the phase-distance trace bound. -/
theorem traceDistance_reference_unitary_le_phaseDistance [Nonempty ι] [Nonempty R]
    (U V : Matrix.unitaryGroup ι ℂ) (ρ : MState (ι × R)) :
    TrDistance (ρ.uConj (unitaryReference U)) (ρ.uConj (unitaryReference V)) ≤
      phaseDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
  have h := traceNorm_amplified_le_phaseDistance U V ρ.m
  rw [ρ.traceNorm_eq_one, mul_one] at h
  change (1 / 2 : ℝ) *
    ((ρ.uConj (unitaryReference U)).m - (ρ.uConj (unitaryReference V)).m).traceNorm ≤ _
  change (1 / 2 : ℝ) * (amplifiedDifference U V ρ.m).traceNorm ≤ _
  linarith

/-- Diamond distance is at most twice phase distance, with no restriction on entangled inputs. -/
theorem unitaryDiamondDistance_le_phaseDistance [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) :
    unitaryDiamondDistance U V ≤
      ENNReal.ofReal (2 * phaseDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)) := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  apply ENNReal.ofReal_le_ofReal
  by_cases hX : X.traceNorm = 0
  · simp [hX, phaseDistance_nonneg]
  · have hpos : 0 < X.traceNorm := lt_of_le_of_ne (Matrix.traceNorm_nonneg X) (Ne.symm hX)
    apply (div_le_iff₀ hpos).mpr
    exact traceNorm_amplified_le_phaseDistance U V X

end Giallar
