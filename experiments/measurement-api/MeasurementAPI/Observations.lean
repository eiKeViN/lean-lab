module

public import MeasurementAPI.POVM
public import MeasurementAPI.Probability

@[expose] public section

/-! One compositional observation interface for quantum and classical transport. -/
open Classical BigOperators
open scoped RealInnerProductSpace
noncomputable section

namespace POVM

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem measure_coarsegrain (P : POVM X a) (f : X → Y) (ρ : MState a) :
    (P.coarsegrain f).measure ρ = (P.measure ρ).pushforward f := by
  apply ProbDistribution.ext
  intro y
  apply Subtype.ext
  rw [measure_apply, ProbDistribution.pushforward_apply]
  simp only [coarsegrain_mats, measure_apply, MState.exp_val, inner_sum]

/-- A complete observation pipeline: channel, measurement, then relabeling.
The right side exposes existing PMF transport to probability-only consumers. -/
theorem observe_pipeline (P : POVM X b) (N : PTPMap a b ℂ)
    (f : X → Y) (ρ : MState a) :
    ((P.pullback N).coarsegrain f).measure ρ =
      (P.measure (N ρ)).pushforward f := by
  rw [measure_coarsegrain, measure_pullback]

end POVM
