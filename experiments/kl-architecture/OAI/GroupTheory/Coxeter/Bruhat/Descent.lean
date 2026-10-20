import Mathlib
import OAI.GroupTheory.Coxeter.Bruhat.LowerFinset

/-! Semantic home: OAI.GroupTheory.Coxeter.Bruhat.Descent. Source spans: SheafMorphisms:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem simple_mul_bruhat_of_descent {c : W} (i : I)
    (hi : cs.length (cs.simple i*c) < cs.length c) {z : W} (hz : BruhatLE cs z c) :
    BruhatLE cs (cs.simple i*z) c := by
  have h := le_upperSimple cs i (cs.simple i*z)
  rw [upperSimple_mul] at h
  have htop : upperSimple cs i c = c := by simp only [upperSimple,ite_eq_left hi]
  rw [← htop]
  exact bruhat_trans cs h (upperSimple_mono cs i hz)

 theorem lower_parity_balance {c : W} (hc : c ≠ 1) {p : ℕ} (hp : p < 2) :
    ((lowerFinset cs c).filter (fun z => cs.length z % 2 = p)).card =
      ((lowerFinset cs c).filter (fun z => cs.length z % 2 ≠ p)).card := by
  classical
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one hc
  have hmem {z : W} (hz : z ∈ lowerFinset cs c) : cs.simple i*z ∈ lowerFinset cs c :=
    (mem_lowerFinset cs c _).mpr (simple_mul_bruhat_of_descent cs i hi
      ((mem_lowerFinset cs c _).mp hz))
  refine Finset.card_bij (fun z _ => cs.simple i*z) ?_ ?_ ?_
  · intro z hz
    obtain ⟨hz,hp'⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hmem hz,?_⟩
    have := cs.length_simple_mul z i
    omega
  · intro z hz w hw he
    exact mul_left_cancel he
  · intro z hz
    obtain ⟨hz,hp'⟩ := Finset.mem_filter.mp hz
    refine ⟨cs.simple i*z,Finset.mem_filter.mpr ⟨hmem hz,?_⟩,
      cs.simple_mul_simple_cancel_left i⟩
    have := cs.length_simple_mul z i
    omega

 def externalLower (x c : W) : Finset W := by
  classical
  exact (lowerFinset cs c) \ (lowerFinset cs x)

@[simp] theorem mem_externalLower (x c z : W) :
    z ∈ externalLower cs x c ↔ BruhatLE cs z c ∧ ¬ BruhatLE cs z x := by
  classical
  simp [externalLower]

 theorem one_bruhat (x : W) : BruhatLE cs 1 x := by
  obtain ⟨ω,hω,hx⟩ := cs.exists_isReduced x
  simpa only [cs.wordProd_nil,← hx] using bruhat_of_subword cs (List.nil_sublist ω) hω

 theorem external_parity_card_le {x c : W} (hxc : BruhatLE cs x c) :
    ((externalLower cs x c).filter (fun z => cs.length z % 2 = cs.length x % 2)).card ≤
      ((externalLower cs x c).filter (fun z => cs.length z % 2 ≠ cs.length x % 2)).card := by
  classical
  by_cases hc : c = 1
  · subst c
    have hx : x = 1 := bruhat_antisymm cs hxc (one_bruhat cs x)
    subst x
    simp [externalLower]
  have hp : cs.length x % 2 < 2 := Nat.mod_lt _ (by omega)
  have hbal := lower_parity_balance cs hc hp
  have hsub : lowerFinset cs x ⊆ lowerFinset cs c := by
    intro z hz
    exact (mem_lowerFinset cs c z).mpr (((mem_lowerFinset cs x z).mp hz).trans hxc)
  have hs₀ : (lowerFinset cs x).filter (fun z => cs.length z % 2 = cs.length x % 2) ⊆
      (lowerFinset cs c).filter (fun z => cs.length z % 2 = cs.length x % 2) :=
    Finset.filter_subset_filter _ hsub
  have hs₁ : (lowerFinset cs x).filter (fun z => cs.length z % 2 ≠ cs.length x % 2) ⊆
      (lowerFinset cs c).filter (fun z => cs.length z % 2 ≠ cs.length x % 2) :=
    Finset.filter_subset_filter _ hsub
  have heq (p : W → Prop) [DecidablePred p] :
      (externalLower cs x c).filter p = (lowerFinset cs c).filter p \ (lowerFinset cs x).filter p := by
    ext z
    simp only [externalLower,Finset.mem_filter,Finset.mem_sdiff]
    tauto
  rw [heq,heq,Finset.card_sdiff_of_subset hs₀,Finset.card_sdiff_of_subset hs₁]
  rw [hbal]
  apply Nat.sub_le_sub_left
  by_cases hx : x = 1
  · subst x
    have hh : lowerFinset cs (1:W) = {1} := by
      ext z
      simp only [mem_lowerFinset,Finset.mem_singleton]
      exact ⟨fun h => bruhat_antisymm cs h (one_bruhat cs z),fun h => h ▸ bruhat_refl cs 1⟩
    simp [hh,Finset.filter_singleton]
  · exact (lower_parity_balance cs hx hp).symm.le

end
end KLInvariance
end

end OAI
