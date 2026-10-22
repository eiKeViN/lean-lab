import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown. Source spans: DihedralIntervals:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue}
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section
variable [Fintype E] [DecidableEq V]

def modelOutgoing (x : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => G.source e = x ∧ G.target e ≤ c)

@[simp] theorem mem_modelOutgoing (x : V) (e : E) :
    e ∈ modelOutgoing G c x ↔ G.source e = x ∧ G.target e ≤ c := by
  classical
  simp [modelOutgoing]

def modelProduct (x : V) : R := ∏ e ∈ modelOutgoing G c x, α e

def HasFlowDown : Prop :=
  ∀ x, x ≤ c → ∃ f : (structureSheaf G α c).Assignment,
    (structureSheaf G α c).IsGlobal f ∧
    (∀ h : PLift (x ≤ c), f x h = modelProduct G α c x) ∧
    (∀ y, ¬ y ≤ x → f y = 0)

omit [DecompositionMonoid R] [Fintype E] [DecidableEq V] in
 theorem structureCompatible_iff (Ω : Set V) (f : (structureSheaf G α c).Assignment) :
    (structureSheaf G α c).CompatibleOn Ω f ↔
      ∀ e, G.source e ∈ Ω → G.target e ∈ Ω → ∀ h : PLift (G.target e ≤ c),
        α e ∣ f (G.source e) ⟨(G.increasing e).le.trans h.down⟩ - f (G.target e) h := by
  constructor
  · intro hf e hs ht h
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq.mp (congrFun (hf e hs ht) h))
  · intro hf e hs ht
    funext h
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hf e hs ht h))

/-- Agreement off one vertex makes the remaining correction divisible by
the outgoing label product. Compatibility and pairwise relative primality suffice;
choosing a flow-down section and a minimal vertex belongs to the caller. -/
theorem modelProduct_dvd_difference (a : V)
    (hrel : (modelOutgoing G c a : Set E).Pairwise (Function.onFun IsRelPrime α))
    (s : Finset V) (hs : IsUpperSet (s : Set V)) (ha : a ∈ s) (hac : a ≤ c)
    (f g : (structureSheaf G α c).Assignment)
    (hf : (structureSheaf G α c).CompatibleOn (s : Set V) f)
    (hg : (structureSheaf G α c).IsGlobal g)
    (hgf : ∀ x ∈ s.erase a, g x=f x) :
    modelProduct G α c a ∣ f a ⟨hac⟩ - g a ⟨hac⟩ := by
  classical
  apply Finset.prod_dvd_of_isRelPrime hrel
  intro e he
  obtain ⟨hea,hec⟩ := (mem_modelOutgoing G c a e).mp he
  have hsource : G.source e ∈ s := hea ▸ ha
  have htarget : G.target e ∈ s.erase a := Finset.mem_erase.mpr
    ⟨by simpa [← hea] using (G.increasing e).ne',hs (G.increasing e).le hsource⟩
  have hf' := (structureCompatible_iff G α c (s : Set V) f).mp hf e hsource
    (Finset.mem_of_mem_erase htarget) ⟨hec⟩
  have hg' := (structureCompatible_iff G α c Set.univ g).mp hg e
    (Set.mem_univ _) (Set.mem_univ _) ⟨hec⟩
  rw [hgf _ htarget] at hg'
  have hd := dvd_sub hf' hg'
  rw [sub_sub_sub_cancel_right] at hd
  subst a
  exact hd

include G α c in
 theorem flowDown_flabby [Finite V]
    (hrel : ∀ x, (modelOutgoing G c x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hflow : HasFlowDown G α c) : (structureSheaf G α c).Flabby := by
  classical
  let B := structureSheaf G α c
  let : Fintype V := Fintype.ofFinite V
  suffices hh : ∀ s : Finset V, IsUpperSet (s : Set V) →
      ∀ f : B.Assignment, B.CompatibleOn (s : Set V) f →
        ∃ g : B.Assignment, B.IsGlobal g ∧ ∀ x ∈ s, g x = f x by
    intro Ω hΩ f hf
    have hset : (↑(Finset.univ.filter (· ∈ Ω)) : Set V) = Ω := by ext x; simp
    obtain ⟨g,hg,hgf⟩ := hh (Finset.univ.filter (· ∈ Ω)) (by rwa [hset]) f (by rwa [hset])
    exact ⟨g,hg,fun x hx => hgf x (by simpa using hx)⟩
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih hs f hf
  by_cases hempty : s = ∅
  · subst s
    refine ⟨0,?_,by simp⟩
    exact (B.sections Set.univ).zero_mem
  obtain ⟨a,ha,hmin⟩ := s.exists_minimal (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hu : IsUpperSet (↑(s.erase a) : Set V) := by
    intro x y hxy hx
    have hx' := Finset.mem_erase.mp hx
    refine Finset.mem_erase.mpr ⟨?_,hs hxy hx'.2⟩
    intro hya
    subst y
    exact hx'.1 (le_antisymm hxy (hmin hx'.2 hxy))
  obtain ⟨g,hg,hgf⟩ := ih (s.erase a) (Finset.erase_ssubset ha) hu f
    (fun e he ht => hf e (Finset.mem_of_mem_erase he) (Finset.mem_of_mem_erase ht))
  by_cases hac : a ≤ c
  · obtain ⟨t,ht,hta,htzero⟩ := hflow a hac
    have hdiv := modelProduct_dvd_difference G α c a (hrel a) s hs ha hac f g hf hg hgf
    obtain ⟨r,hr⟩ := hdiv
    refine ⟨g+r • t,(B.sections Set.univ).add_mem hg
      ((B.sections Set.univ).smul_mem r ht),?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst x
      funext h
      change g a h + r * t a h = f a h
      rw [hta h]
      change f a h - g a h = modelProduct G α c a * r at hr
      linear_combination -hr
    · have hnot : ¬ x ≤ a := fun h => hxa (le_antisymm h (hmin hx h))
      have ht0 := htzero x hnot
      change g x + r • t x = f x
      rw [ht0,smul_zero,add_zero]
      exact hgf x (Finset.mem_erase.mpr ⟨hxa,hx⟩)
  · refine ⟨g,hg,?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst x
      let := structureSheaf_support G α c a hac
      exact Subsingleton.elim _ _
    · exact hgf x (Finset.mem_erase.mpr ⟨hxa,hx⟩)

end
end KLInvariance.MomentGraph.Sheaf
end

end OAI
