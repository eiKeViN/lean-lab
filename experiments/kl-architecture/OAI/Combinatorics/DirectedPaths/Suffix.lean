import Mathlib

/-! Semantic home: OAI.Combinatorics.DirectedPaths.Suffix. Source spans: TerminalKernels:24.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SchedulePaths
universe u v
variable {E : Type u} {Λ : Type v} [LinearOrder Λ]

 theorem exists_suffix_score_gt (score : E → Λ) (r : Λ) (p : List E)
    (hp : p.Pairwise (fun a b => score a ≤ score b)) :
    ∃ q, q <:+ p ∧ ∀ e, e ∈ q ↔ e ∈ p ∧ r < score e := by
  induction p with
  | nil => exact ⟨[],List.suffix_refl _,fun e => by simp⟩
  | cons a p ih =>
    have hs := List.pairwise_cons.mp hp
    by_cases ha : r < score a
    · refine ⟨a::p,List.suffix_refl _,?_⟩
      intro e
      constructor
      · intro he
        refine ⟨he,?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact ha
        · exact lt_of_lt_of_le ha (hs.1 e he)
      · exact And.left
    · obtain ⟨q,hq,hmem⟩ := ih hs.2
      refine ⟨q,hq.trans (List.suffix_cons a p),?_⟩
      intro e
      rw [hmem,List.mem_cons]
      constructor
      · exact fun h => ⟨Or.inr h.1,h.2⟩
      · rintro ⟨he,hr⟩
        rcases he with rfl | he
        · exact (ha hr).elim
        · exact ⟨he,hr⟩

end KLInvariance.SchedulePaths
end

end OAI
