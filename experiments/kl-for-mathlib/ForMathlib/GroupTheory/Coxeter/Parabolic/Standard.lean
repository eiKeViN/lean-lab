import Mathlib
import ForMathlib.GroupTheory.Coxeter.Realization.Cotangent

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Parabolic.Standard. Source spans: Tits:16, Tits:17.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I)
noncomputable section

def matrix : CoxeterMatrix J where
  M i j := M i.val j.val
  isSymm := M.isSymm.submatrix Subtype.val
  diagonal i := M.diagonal i.val
  off_diagonal i j h := M.off_diagonal i.val j.val (fun h' => h (Subtype.ext h'))

abbrev system : CoxeterSystem (matrix (M := M) J) (matrix (M := M) J).Group :=
  (matrix (M := M) J).toCoxeterSystem

def inclusion : (matrix (M := M) J).Group →* W :=
  (system (M := M) J).lift ⟨fun i => cs.simple i.val,
    fun i j => cs.simple_mul_simple_pow i.val j.val⟩

@[simp] theorem inclusion_simple (i : J) :
    inclusion cs J ((system (M := M) J).simple i) = cs.simple i.val :=
  (system (M := M) J).lift_apply_simple _ i

lemma inclusion_word (ω : List J) :
    inclusion cs J ((system (M := M) J).wordProd ω) = cs.wordProd (ω.map Subtype.val) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, map_mul, inclusion_simple, List.map_cons, wordProd_cons, ih]

def restrictVec (l : I → ℝ) : J → ℝ := fun j => l j.val

lemma simple_restrict (i : J) (l : I → ℝ) :
    restrictVec J (Cotangent.action M cs (cs.simple i.val) l) =
      Cotangent.action (matrix (M := M) J) (system (M := M) J)
        ((system (M := M) J).simple i) (restrictVec J l) := by
  rw [Cotangent.action_simple, Cotangent.action_simple]
  funext j
  rfl

theorem action_restrict (w : (matrix (M := M) J).Group) (l : I → ℝ) :
    restrictVec J (Cotangent.action M cs (inclusion cs J w) l) =
      Cotangent.action (matrix (M := M) J) (system (M := M) J) w (restrictVec J l) := by
  obtain ⟨ω, rfl⟩ := (system (M := M) J).wordProd_surjective w
  induction ω generalizing l with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, map_mul, inclusion_simple, map_mul, map_mul,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, simple_restrict, ih]

theorem inclusion_injective [Fintype J] : Function.Injective (inclusion cs J) := by
  classical
  apply (injective_iff_map_eq_one _).2
  intro w hw
  apply Cotangent.action_injective (matrix (M := M) J) (system (M := M) J)
  rw [map_one]
  apply LinearEquiv.ext
  intro l
  let l' : I → ℝ := fun i => if hi : i ∈ J then l ⟨i, hi⟩ else 0
  have hr : restrictVec J l' = l := by ext j; simp [restrictVec, l', j.property]
  have h := action_restrict cs J w l'
  rw [hw, map_one] at h
  change restrictVec J l' = _ at h
  rw [hr] at h
  exact h.symm

lemma lift_word {ω : List I} (hω : ∀ i ∈ ω, i ∈ J) :
    ∃ ν : List J, ν.map Subtype.val = ω := by
  induction ω with
  | nil => exact ⟨[], rfl⟩
  | cons i ω ih =>
    obtain ⟨ν, rfl⟩ := ih (fun j hj => hω j (by simp [hj]))
    exact ⟨⟨i, hω i (by simp)⟩ :: ν, rfl⟩

theorem inclusion_mem (w : (matrix (M := M) J).Group) :
    inclusion cs J w ∈ ParabolicSupport.subgroup cs J := by
  obtain ⟨ω, rfl⟩ := (system (M := M) J).wordProd_surjective w
  rw [inclusion_word]
  apply ParabolicSupport.word_mem
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact j.property

theorem inclusion_range : (inclusion cs J).range = ParabolicSupport.subgroup cs J := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact inclusion_mem cs J w
  · intro w hw
    obtain ⟨ω, hω, rfl⟩ := ParabolicSupport.exists_word cs J hw
    obtain ⟨ν, rfl⟩ := lift_word J hω
    exact ⟨(system (M := M) J).wordProd ν, inclusion_word cs J ν⟩

theorem length_inclusion [Fintype J] (w : (matrix (M := M) J).Group) :
    cs.length (inclusion cs J w) = (system (M := M) J).length w := by
  apply le_antisymm
  · obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced w
    rw [inclusion_word, hω.eq]
    simpa using cs.length_wordProd_le (ω.map Subtype.val)
  · obtain ⟨ω, hω, hred, hprod⟩ := ParabolicSupport.exists_reduced_word cs J
      (inclusion_mem cs J w)
    obtain ⟨ν, rfl⟩ := lift_word J hω
    have heq : (system (M := M) J).wordProd ν = w :=
      inclusion_injective cs J ((inclusion_word cs J ν).trans hprod)
    have hb := (system (M := M) J).length_wordProd_le ν
    rw [heq] at hb
    have hr := hred.eq
    rw [hprod, List.length_map] at hr
    omega

lemma reduced_map_iff [Fintype J] (ω : List J) :
    cs.IsReduced (ω.map Subtype.val) ↔ (system (M := M) J).IsReduced ω := by
  simp only [CoxeterSystem.IsReduced, List.length_map, ← inclusion_word, length_inclusion]

end
end KLInvariance.StandardParabolic
end


namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I) [Fintype J]
noncomputable section

theorem bruhat_inclusion_iff (x y : (matrix (M := M) J).Group) :
    BruhatLE cs (inclusion cs J x) (inclusion cs J y) ↔
      BruhatLE (system (M := M) J) x y := by
  obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced y
  rw [inclusion_word]
  constructor
  · intro h
    obtain ⟨ν, hsub, _, hprod⟩ := (bruhat_iff_reduced_subword cs
      ((reduced_map_iff cs J ω).2 hω)).1 h
    obtain ⟨τ, hτ, rfl⟩ := List.sublist_map_iff.mp hsub
    have hx : (system (M := M) J).wordProd τ = x :=
      inclusion_injective cs J ((inclusion_word cs J τ).trans hprod)
    rw [← hx]
    exact bruhat_of_subword _ hτ hω
  · intro h
    obtain ⟨ν, hsub, _, rfl⟩ := (bruhat_iff_reduced_subword _ hω).1 h
    rw [inclusion_word]
    exact bruhat_of_subword cs (hsub.map Subtype.val) ((reduced_map_iff cs J ω).2 hω)

theorem lower_range (y : (matrix (M := M) J).Group) {z : W}
    (hzy : BruhatLE cs z (inclusion cs J y)) :
    ∃ x, inclusion cs J x = z := by
  obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced y
  rw [inclusion_word] at hzy
  obtain ⟨ν, hsub, _, hprod⟩ := (bruhat_iff_reduced_subword cs
    ((reduced_map_iff cs J ω).2 hω)).1 hzy
  obtain ⟨τ, _, rfl⟩ := List.sublist_map_iff.mp hsub
  exact ⟨(system (M := M) J).wordProd τ, (inclusion_word cs J τ).trans hprod⟩

def intervalMap (x y : (matrix (M := M) J).Group) :
    Interval (system (M := M) J) x y →
      Interval cs (inclusion cs J x) (inclusion cs J y) :=
  fun z => ⟨inclusion cs J z.val, (bruhat_inclusion_iff cs J x z.val).2 z.property.1,
    (bruhat_inclusion_iff cs J z.val y).2 z.property.2⟩

lemma intervalMap_bijective (x y : (matrix (M := M) J).Group) :
    Function.Bijective (intervalMap cs J x y) := by
  constructor
  · intro z t h
    exact Subtype.ext (inclusion_injective cs J (congrArg Subtype.val h))
  · intro z
    obtain ⟨w, hw⟩ := lower_range cs J y z.property.2
    refine ⟨⟨w, ?_, ?_⟩, Subtype.ext hw⟩
    · apply (bruhat_inclusion_iff cs J x w).1
      rw [hw]
      exact z.property.1
    · apply (bruhat_inclusion_iff cs J w y).1
      rw [hw]
      exact z.property.2

/-- The exact unlabelled interval identification used in the finite-rank
reduction; it arises from a proved embedding, not an added main hypothesis. -/
def intervalIso (x y : (matrix (M := M) J).Group) :
    Interval (system (M := M) J) x y ≃o
      Interval cs (inclusion cs J x) (inclusion cs J y) where
  toEquiv := Equiv.ofBijective _ (intervalMap_bijective cs J x y)
  map_rel_iff' := by
    intro z t
    exact bruhat_inclusion_iff cs J z.val t.val

@[simp] theorem intervalIso_val (x y : (matrix (M := M) J).Group)
    (z : Interval (system (M := M) J) x y) :
    (intervalIso cs J x y z).val = inclusion cs J z.val := rfl

lemma rankDifference_inclusion (x y : (matrix (M := M) J).Group) :
    rankDifference cs (inclusion cs J x) (inclusion cs J y) =
      rankDifference (system (M := M) J) x y := by
  simp only [rankDifference, length_inclusion]

end
end KLInvariance.StandardParabolic

end OAI
