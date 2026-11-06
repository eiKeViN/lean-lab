module

public import MeasurementAPI.POVM

@[expose] public section
noncomputable section
open Classical BigOperators
open scoped ComplexOrder

namespace POVM
variable {X a b : Type*} [Fintype X]
variable [Fintype a] [DecidableEq a] [Fintype b]

/-- Extract outcome statistics from a chosen normalized Kraus implementation.
This constructor does not redefine Physlib's canonical measurementMap update. -/
def ofKraus (K : X → Matrix b a ℂ)
    (hK : (∑ x, (K x).conjTranspose * K x) = 1) : POVM X a := by
  let E : X → HermitianMat a ℂ := fun x =>
    ⟨(K x).conjTranspose * K x,
      (Matrix.posSemidef_conjTranspose_mul_self (K x)).isHermitian⟩
  exact {
    mats := E
    nonneg x := HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_conjTranspose_mul_self (K x))
    normalized := HermitianMat.ext ((HermitianMat.mat_finset_sum E Finset.univ).trans hK)
  }

@[simp] theorem ofKraus_mats_mat (K : X → Matrix b a ℂ)
    (hK : (∑ x, (K x).conjTranspose * K x) = 1) (x : X) :
    ((ofKraus K hK).mats x).mat = (K x).conjTranspose * K x := rfl

/-- The chosen implementation's branch trace is exactly its POVM probability. -/
theorem measure_ofKraus (K : X → Matrix b a ℂ)
    (hK : (∑ x, (K x).conjTranspose * K x) = 1) (ρ : MState a) (x : X) :
    ((ofKraus K hK).measure ρ x : ℝ) =
      (K x * ρ.m * (K x).conjTranspose).trace.re := by
  rw [measure_apply, MState.exp_val, HermitianMat.inner_eq_re_trace]
  change (ρ.m * ((K x).conjTranspose * K x)).trace.re = _
  apply congrArg Complex.re
  calc
    (ρ.m * ((K x).conjTranspose * K x)).trace =
        ((ρ.m * (K x).conjTranspose) * K x).trace := by rw [Matrix.mul_assoc]
    _ = (K x * (ρ.m * (K x).conjTranspose)).trace := Matrix.trace_mul_comm _ _
    _ = (K x * ρ.m * (K x).conjTranspose).trace := by rw [Matrix.mul_assoc]

end POVM
