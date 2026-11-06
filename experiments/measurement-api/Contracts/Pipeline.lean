module

public import MeasurementAPI

@[expose] public section
open Classical
noncomputable section

namespace MeasurementAPI.Contracts
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
variable {a b c : Type*}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- Classical label transport commutes with Heisenberg transport as POVMs. -/
theorem pullback_coarsegrain (P : POVM X b) (N : PTPMap a b ℂ) (f : X → Y) :
    (P.coarsegrain f).pullback N = (P.pullback N).coarsegrain f :=
  P.mapEffects_coarsegrain N.hermDual f

/-- Complete typed use chain with two consecutive classical relabelings. -/
theorem two_relabelings (P : POVM X b) (N : PTPMap a b ℂ)
    (f : X → Y) (g : Y → Z) (ρ : MState a) :
    (((P.pullback N).coarsegrain f).coarsegrain g).measure ρ =
      ((P.measure (N ρ)).pushforward f).pushforward g := by
  rw [POVM.measure_coarsegrain, POVM.observe_pipeline]

/-- Channel composition remains usable at the probability consumer boundary. -/
theorem channel_composition (P : POVM X c) (N : CPTPMap a b) (L : CPTPMap b c)
    (f : X → Y) (ρ : MState a) :
    ((P.pullback (L ∘ₘ N).toPTPMap).coarsegrain f).measure ρ =
      ((P.pullback L.toPTPMap).coarsegrain f).measure (N ρ) := by
  rw [POVM.observe_pipeline, POVM.observe_pipeline]
  rfl

theorem pmf_consumer (P : POVM X b) (N : PTPMap a b ℂ) (f : X → Y) (ρ : MState a) :
    QuantumExperiments.PMFBridgeDraft.Bridge.toPMF
        (((P.pullback N).coarsegrain f).measure ρ) =
      (QuantumExperiments.PMFBridgeDraft.Bridge.toPMF (P.measure (N ρ))).map f := by
  rw [POVM.observe_pipeline, ProbDistribution.toPMF_pushforward]

/-- A non-surjective label map is allowed; the unused fiber has zero effect. -/
theorem unused_label (P : POVM (Fin 2) a) :
    (P.coarsegrain (fun i => if i = 0 then (0 : Fin 3) else 1)).mats 2 = 0 := by
  simp [POVM.coarsegrain_mats, Finset.sum_filter, Fin.sum_univ_two]

theorem unused_label_probability (P : POVM (Fin 2) a) (ρ : MState a) :
    ((P.coarsegrain (fun i => if i = 0 then (0 : Fin 3) else 1)).measure ρ 2 : ℝ) = 0 := by
  rw [POVM.measure_apply, unused_label, MState.exp_val_zero]

/-- Empty quantum/outcome carriers require no artificial Nonempty assumptions. -/
def zeroDimPOVM : POVM Empty Empty where
  mats := isEmptyElim
  nonneg := isEmptyElim
  normalized := by
    apply HermitianMat.ext
    ext i
    exact isEmptyElim i

/-- The Kraus constructor does not request decidable equality on its output carrier. -/
example {R S T : Type*} [Fintype R] [Fintype S] [DecidableEq S] [Fintype T]
    (K : R → Matrix T S ℂ) (hK : (∑ r, (K r).conjTranspose * K r) = 1) :
    POVM R S := POVM.ofKraus K hK

end MeasurementAPI.Contracts
