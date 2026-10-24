module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Boundary.Extension. Source spans: MinimalExtensions:13.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B C : BoundarySheaf hneg G α b) (hb : ∀ x, x ≤ b)

omit [Fintype V] in
include hzero hb in
 theorem extend_iso {U : Set V} (hU : IsUpperSet U)
    (j : GradedSheaf.OnIso B.sheaf C.sheaf U)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U) :
    Nonempty (GradedSheaf.OnIso B.sheaf C.sheaf (insert x U)) := by
  classical
  by_cases hxb : x=b
  · subst x
    let eqv := ModuleData.equivOfEq (B.top.trans C.top.symm)
    have heqv := ModuleData.equivOfEq_graded (B.top.trans C.top.symm)
    refine ⟨j.extend hU b hx hmax α B.quotient C.quotient eqv heqv ?_⟩
    intro e he
    exact False.elim ((not_lt_of_ge (hb (G.target e))) (he ▸ G.increasing e))
  · let ja := j.toOnIso.above x hmax
    obtain ⟨e,he,hcomm⟩ := ja.extend_stalk_graded hneg hzero
      (fun e ht => j.edge_graded e (hmax ht)) (B.free x) (C.free x)
      B.flabby.flabby B.generated C.flabby.flabby C.generated
      (B.minimal x hxb) (C.minimal x hxb)
    refine ⟨j.extend hU x hx hmax α B.quotient C.quotient e he ?_⟩
    intro f hf v
    subst x
    exact congrFun (hcomm v) ⟨f,rfl⟩

include hzero hb in
 theorem exists_gradedIso : Nonempty (GradedSheaf.Iso B.sheaf C.sheaf) := by
  classical
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      GradedSheaf.OnIso B.sheaf C.sheaf ((s : Set V)ᶜ) →
      Nonempty (GradedSheaf.Iso B.sheaf C.sheaf) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU j
      by_cases hs : s=∅
      · subst s
        have heq : ((∅ : Finset V) : Set V)ᶜ=Set.univ := by simp
        exact ⟨GradedSheaf.OnIso.ofUniv (heq ▸ j)⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        obtain ⟨jj⟩ := B.extend_iso hzero C hb hU j x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : GradedSheaf.OnIso B.sheaf C.sheaf (∅ : Set V) := by
    refine { toOnIso := ?_, vertex_graded := ?_, edge_graded := ?_ }
    · exact ⟨fun x hx => False.elim hx, fun e he => False.elim he,
        fun e hs => False.elim hs, fun e ht => False.elim ht⟩
    · intro x hx; exact False.elim hx
    · intro e he; exact False.elim he
  have hh := h Finset.univ
  rw [hset] at hh
  exact hh isUpperSet_empty hj

end KLInvariance.MomentGraph.BoundarySheaf
end

end OAI
