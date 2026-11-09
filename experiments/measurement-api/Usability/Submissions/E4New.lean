module

public import MeasurementAPI

@[expose] public section
noncomputable section

open BigOperators

namespace E4New

variable {a b I J : Type*} [Fintype a] [Fintype b] [Fintype I] [Fintype J]
variable [DecidableEq a] [DecidableEq b] [DecidableEq I] [DecidableEq J]

/-- Attach the fine label by multiplying a Kraus operator by its amplitude. -/
def fineKraus (K : I → Matrix b a ℂ) (c : I → J → ℂ) :
    I × J → Matrix b a ℂ := fun ij => c ij.1 ij.2 • K ij.1

theorem fine_effect (K : I → Matrix b a ℂ) (c : I → J → ℂ) (i : I) (j : J) :
    (fineKraus K c (i, j)).conjTranspose * fineKraus K c (i, j) =
      (star (c i j) * c i j) • ((K i).conjTranspose * K i) := by
  simp [fineKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_comm]

theorem sum_fine_effect (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (hc : ∀ i, ∑ j, star (c i j) * c i j = 1) (i : I) :
    (∑ j, (fineKraus K c (i, j)).conjTranspose * fineKraus K c (i, j)) =
      (K i).conjTranspose * K i := by
  simp_rw [fine_effect]
  rw [← Finset.sum_smul, hc, one_smul]

/-- The fine Kraus family is normalized, including for empty finite types. -/
theorem fine_normalized (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (hc : ∀ i, ∑ j, star (c i j) * c i j = 1) :
    (∑ ij, (fineKraus K c ij).conjTranspose * fineKraus K c ij) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_fine_effect K c hc]
  exact hK

/-- The statistics POVM of the original implementation. -/
def originalPOVM (K : I → Matrix b a ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1) : POVM I a :=
  POVM.ofKraus K hK

/-- The statistics POVM with the fine labels retained. -/
def finePOVM (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (hc : ∀ i, ∑ j, star (c i j) * c i j = 1) : POVM (I × J) a :=
  POVM.ofKraus (fineKraus K c) (fine_normalized K c hK hc)

@[simp] theorem originalPOVM_effect (K : I → Matrix b a ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1) (i : I) :
    ((originalPOVM K hK).mats i).mat = (K i).conjTranspose * K i := rfl

@[simp] theorem finePOVM_effect (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (hc : ∀ i, ∑ j, star (c i j) * c i j = 1) (ij : I × J) :
    ((finePOVM K c hK hc).mats ij).mat =
      (fineKraus K c ij).conjTranspose * fineKraus K c ij := rfl

/-- Forgetting the random label recovers the original effects. -/
theorem coarsegrain_finePOVM (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (hc : ∀ i, ∑ j, star (c i j) * c i j = 1) :
    POVM.coarsegrain (finePOVM K c hK hc) Prod.fst = originalPOVM K hK := by
  apply POVM.ext
  intro i
  apply HermitianMat.ext
  simp only [POVM.coarsegrain_mats, HermitianMat.mat_finset_sum,
    Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [apply_ite, HermitianMat.mat_zero, finePOVM_effect, originalPOVM_effect]
  calc
    _ = ∑ j, (fineKraus K c (i, j)).conjTranspose * fineKraus K c (i, j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hne
        simp [hne]
      · simp
    _ = _ := sum_fine_effect K c hc i

theorem fine_branch (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (A : Matrix a a ℂ) (i : I) (j : J) :
    fineKraus K c (i, j) * A * (fineKraus K c (i, j)).conjTranspose =
      (star (c i j) * c i j) • (K i * A * (K i).conjTranspose) := by
  simp [fineKraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_comm]

/-- The fine label does not alter the nonselective output, for any complex input. -/
theorem nonselective_eq (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (hc : ∀ i, ∑ j, star (c i j) * c i j = 1) (A : Matrix a a ℂ) :
    (∑ ij, fineKraus K c ij * A * (fineKraus K c ij).conjTranspose) =
      ∑ i, K i * A * (K i).conjTranspose := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [fine_branch]
  rw [← Finset.sum_smul, hc, one_smul]

/-- The two normalized Kraus implementations define the same CPTP channel. -/
theorem channel_eq (K : I → Matrix b a ℂ) (c : I → J → ℂ)
    (hK : ∑ i, (K i).conjTranspose * K i = 1)
    (hc : ∀ i, ∑ j, star (c i j) * c i j = 1) :
    CPTPMap.of_kraus_CPTPMap (fineKraus K c) (fine_normalized K c hK hc) =
      CPTPMap.of_kraus_CPTPMap K hK := by
  apply CPTPMap.ext
  apply LinearMap.ext
  intro A
  change (MatrixMap.of_kraus (fineKraus K c) (fineKraus K c)) A =
    (MatrixMap.of_kraus K K) A
  simpa [MatrixMap.of_kraus] using nonselective_eq K c hc A

end E4New
