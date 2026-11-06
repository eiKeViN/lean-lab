module

public import MeasurementAPI

@[expose] public section

/-!
Two physical implementations of the same two-outcome statistics.
The first retains the measured bit; the second prepares zero after either result.
Both Kraus families are normalized. Their branch traces agree on EVERY input
matrix, while their total CPTP maps and their outputs on |1><1| differ.
-/
open scoped ComplexOrder
open BigOperators
noncomputable section

namespace MeasurementAPI.ProcessSeparation

abbrev Qubit := Fin 2

def preserve (i : Qubit) : Matrix Qubit Qubit ℂ := Matrix.single i i 1
def reset (i : Qubit) : Matrix Qubit Qubit ℂ := Matrix.single 0 i 1

theorem preserve_normalized : (∑ i, (preserve i).conjTranspose * preserve i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [preserve, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply, Matrix.one_apply]

theorem reset_normalized : (∑ i, (reset i).conjTranspose * reset i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reset, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply, Matrix.one_apply]

def preserveProcess : CPTPMap Qubit Qubit :=
  CPTPMap.of_kraus_CPTPMap preserve preserve_normalized

def resetProcess : CPTPMap Qubit Qubit :=
  CPTPMap.of_kraus_CPTPMap reset reset_normalized

theorem same_POVM : POVM.ofKraus preserve preserve_normalized =
    POVM.ofKraus reset reset_normalized := by
  apply POVM.ext
  intro i
  apply HermitianMat.ext
  simp only [POVM.ofKraus_mats_mat]
  fin_cases i <;> ext r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [preserve, reset, Matrix.mul_apply, Matrix.single,
      Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem same_probabilities (ρ : MState Qubit) :
    (POVM.ofKraus preserve preserve_normalized).measure ρ =
      (POVM.ofKraus reset reset_normalized).measure ρ :=
  congrArg (fun P : POVM Qubit Qubit => P.measure ρ) same_POVM

theorem same_branch_trace (i : Qubit) (A : Matrix Qubit Qubit ℂ) :
    (preserve i * A * (preserve i).conjTranspose).trace =
      (reset i * A * (reset i).conjTranspose).trace := by
  fin_cases i <;>
    simp [preserve, reset, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.single, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem processes_ne : preserveProcess ≠ resetProcess := by
  intro h
  have he := congrArg (fun N : CPTPMap Qubit Qubit =>
    N.map (Matrix.single 1 1 1) 0 0) h
  norm_num [preserveProcess, resetProcess, CPTPMap.of_kraus_CPTPMap,
    HPMap.map, MatrixMap.of_kraus, preserve, reset, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply] at he

def inputOne : MState Qubit := MState.ofClassical (ProbDistribution.constant 1)

theorem output_states_ne : preserveProcess inputOne ≠ resetProcess inputOne := by
  intro h
  have he := congrArg (fun ρ : MState Qubit => ρ.m 0 0) h
  change preserveProcess.map inputOne.m 0 0 = resetProcess.map inputOne.m 0 0 at he
  norm_num [preserveProcess, resetProcess,
    CPTPMap.of_kraus_CPTPMap, HPMap.map, MatrixMap.of_kraus, preserve, reset,
    inputOne, MState.m, MState.ofClassical, ProbDistribution.constant,
    HermitianMat.diagonal, Fin.sum_univ_two, Matrix.mul_apply, Matrix.single,
    Matrix.conjTranspose_apply] at he

end MeasurementAPI.ProcessSeparation
