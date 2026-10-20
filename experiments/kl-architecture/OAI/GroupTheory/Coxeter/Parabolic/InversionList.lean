import Mathlib
import OAI.GroupTheory.Coxeter.Parabolic.Standard

/-! Semantic home: OAI.GroupTheory.Coxeter.Parabolic.InversionList. Source spans: DyerPaths:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I)
noncomputable section

theorem leftInvSeq_inclusion (ω : List J) :
    ((system (M := M) J).leftInvSeq ω).map (inclusion cs J) =
      cs.leftInvSeq (ω.map Subtype.val) := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    simp only [CoxeterSystem.leftInvSeq, List.map_cons, List.map_map,
      inclusion_simple]
    rw [← ih, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, MulAut.conj_apply, map_mul, map_inv,
      inclusion_simple]

theorem reflection_inclusion {t : (matrix (M := M) J).Group}
    (ht : (system (M := M) J).IsReflection t) :
    cs.IsReflection (inclusion cs J t) := by
  obtain ⟨w, i, rfl⟩ := ht
  exact ⟨inclusion cs J w, i.val, by simp only [map_mul, map_inv, inclusion_simple]⟩

theorem bruhatStep_inclusion_iff [Fintype J] (x y : (matrix (M := M) J).Group) :
    BruhatStep cs (inclusion cs J x) (inclusion cs J y) ↔
      BruhatStep (system (M := M) J) x y := by
  constructor
  · rintro ⟨hlen, t, ht, heq⟩
    obtain ⟨ω, hω, hprod⟩ := (system (M := M) J).exists_isReduced y
    have hi : cs.IsLeftInversion (inclusion cs J y) t := by
      refine ⟨ht, ?_⟩
      rw [heq, ← mul_assoc, ht.mul_self, one_mul]
      simpa only [heq] using hlen
    have hr := (reduced_map_iff cs J ω).2 hω
    have hw : cs.wordProd (ω.map Subtype.val) = inclusion cs J y := by
      rw [← inclusion_word, hprod]
    have hm := CoxeterSupport.mem_leftInvSeq_of_inversion cs hr (hw ▸ hi)
    rw [← leftInvSeq_inclusion] at hm
    obtain ⟨r, hr, hrt⟩ := List.mem_map.mp hm
    refine ⟨by simpa only [length_inclusion] using hlen,
      r, (system (M := M) J).isReflection_of_mem_leftInvSeq ω hr, ?_⟩
    apply inclusion_injective cs J
    simpa only [map_mul, hrt] using heq
  · rintro ⟨hlen, t, ht, heq⟩
    refine ⟨by simpa only [length_inclusion] using hlen,
      inclusion cs J t, reflection_inclusion cs J ht, ?_⟩
    rw [heq, map_mul]

end
end KLInvariance.StandardParabolic
end

end OAI
