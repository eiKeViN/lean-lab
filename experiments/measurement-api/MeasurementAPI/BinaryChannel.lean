module

public import MeasurementAPI.POVM

@[expose] public section
noncomputable section

namespace POVM
variable {a : Type*} [Fintype a] [DecidableEq a]

/-- A single binary test sends two states to their specified classical coins.
Used to replace the local channel construction in Ref81Lem5. -/
theorem binary_channel_for_pair
    (T : HermitianMat a ℂ) (hT : 0 ≤ T ∧ T ≤ 1)
    (ρ σ : MState a) (p q : Prob)
    (hp : ρ.exp_val T = (p : ℝ)) (hq : σ.exp_val T = (q : ℝ)) :
    ∃ N : CPTPMap a (Fin 2),
      N ρ = MState.ofClassical (ProbDistribution.coin p) ∧
      N σ = MState.ofClassical (ProbDistribution.coin q) := by
  refine ⟨(binary T hT).measureDiscard, ?_, ?_⟩
  · rw [measureDiscard_binary]
    apply congrArg MState.ofClassical
    apply congrArg ProbDistribution.coin
    apply Subtype.ext
    exact hp
  · rw [measureDiscard_binary]
    apply congrArg MState.ofClassical
    apply congrArg ProbDistribution.coin
    apply Subtype.ext
    exact hq

end POVM
