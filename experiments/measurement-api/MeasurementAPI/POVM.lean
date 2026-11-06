module

public import QuantumInfo.Measurements.POVM
public import QuantumInfo.Channels.Dual
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
Finite POVM operations returning Physlib's existing type.
Binary outcome 0 is acceptance; outcome transport is distinct from state update.
-/

open Classical BigOperators
open scoped RealInnerProductSpace

namespace POVM
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

@[ext] theorem ext {P Q : POVM X a} (h : ∀ x, P.mats x = Q.mats x) : P = Q := by
  have hm := funext h
  cases P
  cases Q
  cases hm
  rfl

/-- The existing positivity, linear-map and one-map classes discharge all laws. -/
def mapEffects (P : POVM X b) (F : PUMap b a ℂ) : POVM X a where
  mats x := F (P.mats x)
  nonneg x := F.pos_Hermitian (P.nonneg x)
  normalized := by rw [← map_sum, P.normalized, map_one]

@[simp] theorem mapEffects_mats (P : POVM X b) (F : PUMap b a ℂ) (x : X) :
    (mapEffects P F).mats x = F (P.mats x) := rfl

/-- Heisenberg pullback needs a positive TP map for standalone probabilities. -/
def pullback (P : POVM X b) (N : PTPMap a b ℂ) : POVM X a :=
  mapEffects P N.hermDual

/-- A stable observation rule hides the orientation of Physlib's real inner product. -/
@[simp] theorem measure_apply (P : POVM X a) (ρ : MState a) (x : X) :
    (P.measure ρ x : ℝ) = ρ.exp_val (P.mats x) := by
  change ⟪P.mats x, ρ.M⟫ = ⟪ρ.M, P.mats x⟫
  exact HermitianMat.inner_comm _ _

theorem measure_pullback (P : POVM X b) (N : PTPMap a b ℂ) (ρ : MState a) :
    (pullback P N).measure ρ = P.measure (N ρ) := by
  apply ProbDistribution.ext
  intro x
  apply Subtype.ext
  rw [measure_apply, measure_apply]
  exact (PTPMap.exp_val_hermDual N ρ (P.mats x)).symm

/-- This is outcome postprocessing only; it does not select a state update. -/
def coarsegrain (P : POVM X a) (f : X → Y) : POVM Y a where
  mats y := ∑ x ∈ Finset.univ.filter (fun x => f x = y), P.mats x
  nonneg y := Finset.sum_nonneg (fun x _ => P.nonneg x)
  normalized := by
    rw [show (∑ y, ∑ x ∈ Finset.univ.filter (fun x => f x = y), P.mats x) =
        ∑ x, P.mats x by
      simpa using Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f P.mats]
    exact P.normalized

@[simp] theorem coarsegrain_mats (P : POVM X a) (f : X → Y) (y : Y) :
    (coarsegrain P f).mats y =
      ∑ x ∈ Finset.univ.filter (fun x => f x = y), P.mats x := rfl

@[simp] theorem coarsegrain_id (P : POVM X a) : coarsegrain P id = P := by
  apply ext
  intro x
  simp [coarsegrain_mats, Finset.sum_filter]

@[simp] theorem coarsegrain_comp {Z : Type*} [Fintype Z]
    (P : POVM X a) (f : X → Y) (g : Y → Z) :
    coarsegrain (coarsegrain P f) g = coarsegrain P (g ∘ f) := by
  apply ext
  intro z
  simp only [coarsegrain_mats]
  simpa using Finset.sum_fiberwise_eq_sum_filter Finset.univ
    (Finset.univ.filter (fun y => g y = z)) f P.mats

/-- Effect transport commutes with classical postprocessing by linearity. -/
theorem mapEffects_coarsegrain (P : POVM X b) (F : PUMap b a ℂ) (f : X → Y) :
    mapEffects (coarsegrain P f) F = coarsegrain (mapEffects P F) f := by
  apply ext
  intro y
  exact map_sum F _ _

/-- Binary testing: outcome 0 is acceptance, matching ProbDistribution.coin. -/
def binary (T : HermitianMat a ℂ) (hT : 0 ≤ T ∧ T ≤ 1) : POVM (Fin 2) a where
  mats i := if i = 0 then T else 1 - T
  nonneg i := by
    split
    · exact hT.1
    · exact sub_nonneg.mpr hT.2
  normalized := by simp

@[simp] theorem binary_zero (T : HermitianMat a ℂ) (hT : 0 ≤ T ∧ T ≤ 1) :
    (binary T hT).mats 0 = T := by simp [binary]

/-- Reuse the existing characterization of every two-point distribution as a coin. -/
theorem measure_binary (T : HermitianMat a ℂ) (hT : 0 ≤ T ∧ T ≤ 1) (ρ : MState a) :
    (binary T hT).measure ρ =
      ProbDistribution.coin ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩ := by
  symm
  apply (ProbDistribution.coin_eq_iff _ _).mpr
  apply Subtype.ext
  symm
  simpa only [binary_zero] using measure_apply (binary T hT) ρ (0 : Fin 2)

/-- A binary test has exactly the output required by the hypothesis-testing DPI client. -/
theorem measureDiscard_binary (T : HermitianMat a ℂ) (hT : 0 ≤ T ∧ T ≤ 1)
    (ρ : MState a) :
    (binary T hT).measureDiscard ρ =
      MState.ofClassical (ProbDistribution.coin ⟨ρ.exp_val T, ρ.exp_val_prob hT⟩) := by
  rw [POVM.measureDiscard_apply, measure_binary]

end
end POVM
