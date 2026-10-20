import Mathlib
import OAI.Combinatorics.DirectedPaths.Basic

/-! Semantic home: OAI.Combinatorics.DirectedPaths.Monotone. Source spans: PositiveTransfer:3, PositiveTransfer:11.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SchedulePaths
universe u v
variable {E : Type u} {Λ : Type v} [LinearOrder Λ]

 theorem mem_suffix_iff_score_lt (score : E → Λ) {p q : List E} {e f : E}
    (hs : p.Pairwise (fun a b => score a ≤ score b))
    (hq : e::q <:+ p) (hf : f ∈ p) (hne : score e ≠ score f) :
    f ∈ q ↔ score e < score f := by
  obtain ⟨a,rfl⟩ := hq
  have h := List.pairwise_append.mp hs
  constructor
  · intro hfq
    exact lt_of_le_of_ne ((List.pairwise_cons.mp h.2.1).1 f hfq) hne
  · intro hlt
    rcases List.mem_append.mp hf with hfa | hfr
    · exact False.elim (not_le_of_gt hlt (h.2.2 f hfa e List.mem_cons_self))
    · rcases List.mem_cons.mp hfr with rfl | hfr
      · exact False.elim (hne rfl)
      · exact hfr

 theorem mem_suffix_iff_score_lt_injective (score : E → Λ) {p q : List E} {e f : E}
    (hs : p.Pairwise (fun a b => score a ≤ score b)) (hn : p.Nodup)
    (hq : e::q <:+ p) (hf : f ∈ p) (heq : score e = score f → e=f) :
    f ∈ q ↔ score e < score f := by
  by_cases hne : score e ≠ score f
  · exact mem_suffix_iff_score_lt score hs hq hf hne
  · have hef := heq (not_ne_iff.mp hne)
    subst f
    have hx := (List.nodup_cons.mp (hn.sublist hq.sublist)).1
    simp only [hx,lt_self_iff_false]

end KLInvariance.SchedulePaths
end


section
namespace KLInvariance.SchedulePaths
universe u v
variable {V : Type u} {E : Type v}
  (source target : E → V)
noncomputable section

 theorem step_monotone (T : ℝ) (hT : 0 ≤ T) (e : E) :
    Monotone (step source target T e) := by
  intro v w hv x
  dsimp [step]
  split_ifs
  · exact add_le_add (hv x) (mul_le_mul_of_nonneg_left (hv _) hT)
  · simpa using hv x

 theorem step_injective (T : ℝ) (e : E) (hne : source e ≠ target e) :
    Function.Injective (step source target T e) := by
  intro v w he
  have ht := congrFun he (target e)
  simp only [step,hne,ite_false,add_zero] at ht
  funext x
  have hx := congrFun he x
  dsimp [step] at hx
  split_ifs at hx with h
  · rw [ht] at hx
    exact add_right_cancel hx
  · exact add_right_cancel hx

 theorem dispatch_monotone (T : ℝ) (hT : 0 ≤ T) (p : List E) :
    Monotone (fun v => dispatch source target T v p) := by
  induction p with
  | nil => exact monotone_id
  | cons e p ih => exact (step_monotone source target T hT e).comp ih

 theorem dispatch_injective (T : ℝ) (p : List E)
    (hne : ∀ e ∈ p, source e ≠ target e) :
    Function.Injective (fun v => dispatch source target T v p) := by
  induction p with
  | nil => exact Function.injective_id
  | cons e p ih =>
    exact (step_injective source target T e (hne e (by simp))).comp
      (ih (fun a ha => hne a (by simp [ha])))

 theorem dispatch_append' (T : ℝ) (v : V → ℝ) (p q : List E) :
    dispatch source target T v (p++q) =
      dispatch source target T (dispatch source target T v q) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append,dispatch,ih]

/-- A concrete state indexed by the remaining chronological edge list. -/
 theorem remaining_state_le (T : ℝ) (hT : 0 ≤ T)
    (D : List E → V → ℝ) (p : List E)
    (hstep : ∀ e q, e::q <:+ p → D q ≤ step source target T e (D (e::q))) :
    D [] ≤ dispatch source target T (D p) p.reverse := by
  induction p with
  | nil => exact le_rfl
  | cons e p ih =>
    have hp := ih (fun a q hq => hstep a q (hq.trans (List.suffix_cons e p)))
    have he := hstep e p (List.suffix_refl _)
    rw [List.reverse_cons,dispatch_append']
    exact hp.trans (dispatch_monotone source target T hT p.reverse he)

/-- If the endpoint bound is equality, every embedded one-edge Hilbert bound
is equality. Injectivity must be used together with the one-sided bounds. -/
 theorem remaining_steps_eq (T : ℝ) (hT : 0 ≤ T)
    (D : List E → V → ℝ) (p : List E)
    (hne : ∀ e ∈ p, source e ≠ target e)
    (hstep : ∀ e q, e::q <:+ p → D q ≤ step source target T e (D (e::q)))
    (hend : D [] = dispatch source target T (D p) p.reverse) :
    ∀ e q, e::q <:+ p → D q = step source target T e (D (e::q)) := by
  induction p with
  | nil =>
    intro e q hq
    have := hq.length_le
    simp at this
  | cons e p ih =>
    have hps := fun a q (hq : a::q <:+ p) => hstep a q (hq.trans (List.suffix_cons e p))
    have hp := remaining_state_le source target T hT D p hps
    have he := hstep e p (List.suffix_refl _)
    have hm := dispatch_monotone source target T hT p.reverse he
    have hend' : D [] = dispatch source target T
        (step source target T e (D (e::p))) p.reverse := by
      simpa only [List.reverse_cons,dispatch_append',dispatch] using hend
    have hh : dispatch source target T (D p) p.reverse =
        dispatch source target T (step source target T e (D (e::p))) p.reverse := by
      apply le_antisymm hm
      exact hend'.symm.le.trans hp
    have hep : D p = step source target T e (D (e::p)) :=
      dispatch_injective source target T p.reverse
        (fun a ha => hne a (by simp only [List.mem_reverse] at ha; simp [ha])) hh
    have hendpoint : D [] = dispatch source target T (D p) p.reverse := by
      exact hend'.trans hh.symm
    intro a q hq
    rcases List.suffix_cons_iff.mp hq with h | h
    · cases h
      exact hep
    · exact ih (fun a ha => hne a (by simp [ha])) hps hendpoint a q h

end
end KLInvariance.SchedulePaths
end

end OAI
