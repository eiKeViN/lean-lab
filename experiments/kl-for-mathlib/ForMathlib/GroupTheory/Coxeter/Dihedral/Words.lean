import Mathlib
import ForMathlib.GroupTheory.Coxeter.Bruhat.Basic

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Dihedral.Words. Source spans: Dihedral:2, Dihedral:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Dihedral

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

/-- The alternating expression starting with `i`, unlike Mathlib's
`alternatingWord`, which specifies the final letter. -/
def alt (i : Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => i :: alt (!i) n

@[simp] theorem alt_zero (i : Bool) : alt i 0 = [] := rfl
@[simp] theorem alt_succ (i : Bool) (n : ℕ) : alt i (n+1) = i :: alt (!i) n := rfl
@[simp] theorem length_alt (i : Bool) (n : ℕ) : (alt i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [ih]

@[simp] theorem take_alt (i : Bool) (k n : ℕ) : (alt i n).take k = alt i (min k n) := by
  induction n generalizing i k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih]

theorem reduced_cons_cons_ne (cs : CoxeterSystem M W) {i j : Bool} {ω : List Bool}
    (h : cs.IsReduced (i :: j :: ω)) : i ≠ j := by
  rintro rfl
  have hlen := cs.length_wordProd_le ω
  have heq := h.eq
  simp only [cs.wordProd_cons, cs.simple_mul_simple_cancel_left, List.length_cons] at heq
  omega

theorem reduced_cons_eq_alt (cs : CoxeterSystem M W) (i : Bool) (ω : List Bool)
    (h : cs.IsReduced (i :: ω)) : i :: ω = alt i (ω.length + 1) := by
  induction ω generalizing i with
  | nil => simp
  | cons j ω ih =>
    have hj : j = !i := by
      have := reduced_cons_cons_ne cs h
      cases i <;> cases j <;> simp_all
    have hω : cs.IsReduced (j :: ω) := by simpa using h.drop 1
    rw [show (j :: ω).length + 1 = (ω.length + 1) + 1 by rfl, alt_succ]
    congr 1
    rw [ih j hω, hj]

theorem reduced_eq_alt (cs : CoxeterSystem M W) (ω : List Bool)
    (h : cs.IsReduced ω) : ∃ i, ω = alt i ω.length := by
  cases ω with
  | nil => exact ⟨false, rfl⟩
  | cons i ω => exact ⟨i, reduced_cons_eq_alt cs i ω h⟩

theorem exists_alt (cs : CoxeterSystem M W) (w : W) :
    ∃ i, w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced w
  obtain ⟨i, hi⟩ := reduced_eq_alt cs ω hω
  refine ⟨i, ?_⟩
  rw [hw, hω.eq, ← hi]

theorem reduced_alt_take (cs : CoxeterSystem M W) {i : Bool} {k n : ℕ}
    (h : cs.IsReduced (alt i n)) (hk : k ≤ n) : cs.IsReduced (alt i k) := by
  simpa only [take_alt, Nat.min_eq_left hk] using h.take k

theorem alt_sublist (i : Bool) {k n : ℕ} (h : k ≤ n) : (alt i k).Sublist (alt i n) := by
  simpa only [take_alt, Nat.min_eq_left h] using List.take_sublist k (alt i n)

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral

noncomputable local instance _root_.OAI.KLInvariance.Dihedral.instDecidable_oAI (p : Prop) : Decidable p := Classical.propDecidable p

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

/-- In a rank-two Coxeter system, every strictly shorter element lies below
every longer element. This uses the actual Bruhat subword theorem. -/
theorem shorter_bruhat (cs : CoxeterSystem M W) {x w : W}
    (h : cs.length x < cs.length w) : BruhatLE cs x w := by
  obtain ⟨i, hi⟩ := exists_alt cs w
  obtain ⟨j, hj⟩ := exists_alt cs x
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    change cs.length (cs.wordProd (alt i (cs.length w))) = (alt i (cs.length w)).length
    rw [← hi, length_alt]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show cs.length w ≠ 0 by omega)
  rw [hn] at hi hr h
  rw [hi, hj]
  apply bruhat_of_subword cs _ hr
  by_cases hji : j = i
  · subst j
    exact alt_sublist i (by omega)
  · have hj' : j = !i := by cases i <;> cases j <;> first | rfl | exact (hji rfl).elim
    rw [hj', alt_succ]
    exact (alt_sublist (!i) (by omega)).cons i

theorem bruhat_iff_length_lt_or_eq (cs : CoxeterSystem M W) (x w : W) :
    BruhatLE cs x w ↔ cs.length x < cs.length w ∨ x = w := by
  constructor
  · intro h
    by_cases he : x = w
    · exact Or.inr he
    · exact Or.inl (length_lt_of_bruhat_ne cs h he)
  · rintro (h | rfl)
    · exact shorter_bruhat cs h
    · exact bruhat_refl cs _

theorem eq_alt_of_descent (cs : CoxeterSystem M W) (i : Bool) {w : W}
    (h : cs.length (cs.simple i * w) < cs.length w) :
    w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced (cs.simple i * w)
  have hlen : cs.length w = ω.length + 1 := by
    have := cs.length_simple_mul w i
    rw [hw, hω.eq] at this h
    omega
  have hp : cs.wordProd (i :: ω) = w := by
    simp only [cs.wordProd_cons, ← hw, cs.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: ω) := by
    simpa only [CoxeterSystem.IsReduced, hp, List.length_cons] using hlen
  rw [hlen, ← reduced_cons_eq_alt cs i ω hr, hp]

end KLInvariance.Dihedral
end

end OAI
