module

public import MeasurementAPI

@[expose] public section

noncomputable section

namespace E3New

open Classical BigOperators

variable {X Y a : Type*} [Fintype X] [Fintype Y]
  [Fintype a] [DecidableEq a]

/-- The POVM obtained by forgetting all distinctions inside a fiber of `f`. -/
def merged (E : POVM X a) (f : X → Y) : POVM Y a :=
  E.coarsegrain f

theorem merged_effects (E : POVM X a) (f : X → Y) (y : Y) :
    (merged E f).mats y =
      ∑ x ∈ Finset.univ.filter (fun x => f x = y), E.mats x := by
  rfl

/-- The real Born probability of a merged label is the sum over its fiber. -/
theorem merged_probability (E : POVM X a) (f : X → Y) (ρ : MState a) (y : Y) :
    ((merged E f).measure ρ y : ℝ) =
      ∑ x ∈ Finset.univ.filter (fun x => f x = y), (E.measure ρ x : ℝ) := by
  rw [merged, POVM.measure_coarsegrain, ProbDistribution.pushforward_apply]

/-- Deterministic relabeling contracts the real `ℓ¹` distance. -/
theorem pushforward_sum_abs_le (p q : ProbDistribution X) (f : X → Y) :
    (∑ y, |(p.pushforward f y : ℝ) - (q.pushforward f y : ℝ)|) ≤
      ∑ x, |(p x : ℝ) - (q x : ℝ)| := by
  simp_rw [ProbDistribution.pushforward_apply]
  calc
    (∑ y, |(∑ x ∈ Finset.univ.filter (fun x => f x = y), (p x : ℝ)) -
        ∑ x ∈ Finset.univ.filter (fun x => f x = y), (q x : ℝ)|) =
        ∑ y, |∑ x ∈ Finset.univ.filter (fun x => f x = y),
          ((p x : ℝ) - (q x : ℝ))| := by
      simp only [Finset.sum_sub_distrib]
    _ ≤ ∑ y, ∑ x ∈ Finset.univ.filter (fun x => f x = y),
        |(p x : ℝ) - (q x : ℝ)| := by
      apply Finset.sum_le_sum
      intro y _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |(p x : ℝ) - (q x : ℝ)| := by
      simpa using Finset.sum_fiberwise_eq_sum_filter
        Finset.univ Finset.univ f (fun x => |(p x : ℝ) - (q x : ℝ)|)

/-- Forgetting classical labels does not increase distinguishability. -/
theorem measurement_sum_abs_le (E : POVM X a) (f : X → Y) (ρ σ : MState a) :
    (∑ y, |((merged E f).measure ρ y : ℝ) -
      ((merged E f).measure σ y : ℝ)|) ≤
      ∑ x, |(E.measure ρ x : ℝ) - (E.measure σ x : ℝ)| := by
  simp only [merged, POVM.measure_coarsegrain]
  exact pushforward_sum_abs_le (E.measure ρ) (E.measure σ) f

end E3New
