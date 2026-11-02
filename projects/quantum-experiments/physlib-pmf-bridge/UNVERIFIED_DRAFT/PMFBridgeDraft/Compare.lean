/-
UNVERIFIED_DRAFT — NOT COMPILED. Static shared-goal check for two routes.
No new placeholders, but BOTH imported routes are incomplete and unverified.
No timing, maintenance-benefit or accepted-theorem claim follows from this file.
-/
import PMFBridgeDraft.Native
import PMFBridgeDraft.ViaPMF

noncomputable section

namespace QuantumExperiments.PMFBridgeDraft

variable {α β : Type*} [Fintype α] [Fintype β]

theorem route_bind_eq (d : ProbDistribution α) (k : α → ProbDistribution β) :
    Native.bind d k = ViaPMF.bind d k := by
  apply ProbDistribution.ext
  intro b
  apply Subtype.ext
  change (Native.bind d k b : ℝ) = (ViaPMF.bind d k b : ℝ)
  rw [Native.bind_apply, ViaPMF.bind_apply]

theorem route_comp_eq {I O P : Type*} [Fintype O] [Fintype P]
    (C : DMChannel I O) (D : DMChannel O P) : Native.comp C D = ViaPMF.comp C D := by
  cases C with
  | mk c =>
    cases D with
    | mk d =>
      change DMChannel.mk (fun i => Native.bind (c i) d) =
        DMChannel.mk (fun i => ViaPMF.bind (c i) d)
      congr 1
      funext i
      exact route_bind_eq (c i) d

end QuantumExperiments.PMFBridgeDraft
