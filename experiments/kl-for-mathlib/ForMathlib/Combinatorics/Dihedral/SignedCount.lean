module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Combinatorics.Dihedral.SignedCount. Source spans: DihedralIntervals:11, DihedralIntervals:17, DihedralIntervals:18.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SignedDihedral
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SignedDihedral.instDecidable_oAI (p : Prop) : Decidable p := Classical.propDecidable p

 @[expose] def Before (a b : ℤ) : Prop :=
  (0 < a ∧ 0 < b ∧ a < b) ∨ (a < 0 ∧ b < 0 ∧ a < b) ∨ (0 < a ∧ b < 0)

 theorem before_same_source_pos {i j z : ℤ} (hij : |i| < |j|)
    (hiz : |i| < |z|) (hj : 0 < j) :
    Before (i+j) (i+z) ↔ z < 0 ∨ j < z := by
  rw [abs_of_pos hj, abs_lt] at hij
  obtain hz | hz := le_total 0 z
  · rw [abs_of_nonneg hz, abs_lt] at hiz
    dsimp [Before]
    omega
  · rw [abs_of_nonpos hz, abs_lt] at hiz
    dsimp [Before]
    omega

 theorem before_same_source_neg {i j z : ℤ} (hij : |i| < |j|)
    (hiz : |i| < |z|) (hj : j < 0) :
    Before (i+j) (i+z) ↔ z < 0 ∧ j < z := by
  rw [abs_of_neg hj, abs_lt] at hij
  obtain hz | hz := le_total 0 z
  · rw [abs_of_nonneg hz, abs_lt] at hiz
    dsimp [Before]
    omega
  · rw [abs_of_nonpos hz, abs_lt] at hiz
    dsimp [Before]
    omega

 theorem before_next_source {i j z : ℤ} (hij : |i| < |j|)
    (hjz : |j| < |z|) :
    Before (i+j) (j+z) ↔ 0 < j := by
  obtain hj | hj := le_total 0 j
  · rw [abs_of_nonneg hj, abs_lt] at hij
    obtain hz | hz := le_total 0 z
    · rw [abs_of_nonneg hj, abs_of_nonneg hz] at hjz
      dsimp [Before]
      omega
    · rw [abs_of_nonneg hj, abs_of_nonpos hz] at hjz
      dsimp [Before]
      omega
  · rw [abs_of_nonpos hj, abs_lt] at hij
    obtain hz | hz := le_total 0 z
    · rw [abs_of_nonpos hj, abs_of_nonneg hz] at hjz
      dsimp [Before]
      omega
    · rw [abs_of_nonpos hj, abs_of_nonpos hz] at hjz
      dsimp [Before]
      omega

 theorem midpoint_mod {m a : ℤ} (_hm : 0 < m) (ha : -2*m < a) (ha' : a < 2*m) :
    a % (2*m) = if 0 ≤ a then a else 2*m+a := by
  split_ifs with h
  · exact Int.emod_eq_of_lt h ha'
  · have he : a % (2*m) = (a+2*m) % (2*m) := by simp
    rw [he, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- For two outgoing edges at the same vertex, reduction modulo the period
has no wrap-around exception in the midpoint comparison table. -/
 theorem finite_before_same {m i j z : ℤ} (hm : 0 < m)
    (hi : |i| < |j|) (hz : |i| < |z|)
    (hjM : -m < j ∧ j ≤ m) (hzM : -m < z ∧ z ≤ m) :
    (i+j) % (2*m) < (i+z) % (2*m) ↔ Before (i+j) (i+z) := by
  have hjabs : |j| ≤ m := abs_le.mpr (by omega)
  have hzabs : |z| ≤ m := abs_le.mpr (by omega)
  have hiabs := abs_lt.mp (hi.trans_le hjabs)
  rw [midpoint_mod hm (by omega) (by omega), midpoint_mod hm (by omega) (by omega)]
  obtain hjs | hjs := le_total 0 j
  · rw [abs_of_nonneg hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
  · rw [abs_of_nonpos hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hzs, abs_lt] at hz
      dsimp [Before]
      split_ifs <;> omega

 theorem finite_before_next {m i j z : ℤ} (hm : 0 < m)
    (hi : |i| < |j|) (hz : |j| < |z|)
    (hzM : -m < z ∧ z ≤ m) :
    (i+j) % (2*m) < (j+z) % (2*m) ↔ Before (i+j) (j+z) := by
  have hzabs : |z| ≤ m := abs_le.mpr (by omega)
  have hjabs := abs_lt.mp (hz.trans_le hzabs)
  have hiabs := abs_lt.mp ((hi.trans hz).trans_le hzabs)
  rw [midpoint_mod hm (by omega) (by omega), midpoint_mod hm (by omega) (by omega)]
  obtain hjs | hjs := le_total 0 j
  · rw [abs_of_nonneg hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonneg hjs, abs_of_nonneg hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonneg hjs, abs_of_nonpos hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
  · rw [abs_of_nonpos hjs, abs_lt] at hi
    obtain hzs | hzs := le_total 0 z
    · rw [abs_of_nonpos hjs, abs_of_nonneg hzs] at hz
      dsimp [Before]
      split_ifs <;> omega
    · rw [abs_of_nonpos hjs, abs_of_nonpos hzs] at hz
      dsimp [Before]
      split_ifs <;> omega

 theorem eligible_ranks_card (L k : ℕ) :
    ((Finset.range (L+2*k+1)).filter (fun r => L < r ∧ Odd (L+r))).card = k := by
  classical
  have hc : (Finset.range k).card =
      ((Finset.range (L+2*k+1)).filter (fun r => L < r ∧ Odd (L+r))).card := by
    apply Finset.card_bij (fun a _ => L+1+2*a)
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_filter, Nat.odd_iff] at ha ⊢
      omega
    · intro a ha b hb he
      omega
    · intro b hb
      simp only [Finset.mem_range, Finset.mem_filter, Nat.odd_iff] at hb
      refine ⟨(b-L-1)/2, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
  simpa only [Finset.card_range] using hc.symm

 @[expose] noncomputable def arrowAfter (a label z : ℤ) : ℕ :=
  if |a| < |z| ∧ Odd (a+z) ∧ Before label (a+z) then 1 else 0

/-- Double internal ranks and the singleton top, with no singleton bottom
term because upward arrows never end at the bottom. -/
 @[expose] noncomputable def countAfter (a label c : ℤ) : ℕ :=
  (∑ r ∈ Finset.range c.natAbs, (arrowAfter a label r + arrowAfter a label (-r))) +
    arrowAfter a label c

 theorem arrowAfter_of_not_lt {a label z : ℤ} (h : ¬ |a| < |z|) :
    arrowAfter a label z = 0 := by simp [arrowAfter,h]

 theorem arrowAfter_self (i j : ℤ) : arrowAfter i (i+j) j = 0 := by
  have hb : ¬ Before (i+j) (i+j) := by
    dsimp [Before]
    omega
  simp only [arrowAfter, hb, and_false, ite_false]

end
end KLInvariance.SignedDihedral
end


section
namespace KLInvariance.SignedDihedral
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SignedDihedral.instDecidable_oAI_1 (p : Prop) : Decidable p := Classical.propDecidable p

 theorem odd_add_abs (i z : ℤ) : Odd (i+z) ↔ Odd (i.natAbs+z.natAbs) := by
  rw [Int.odd_add, Nat.odd_add, Int.natAbs_odd, Int.natAbs_even]

 theorem odd_add_natAbs (i : ℤ) (r : ℕ) : Odd (i+r) ↔ Odd (i.natAbs+r) := by
  simpa only [Int.natAbs_natCast] using odd_add_abs i (r : ℤ)

 theorem odd_sub_natAbs (i : ℤ) (r : ℕ) : Odd (i-r) ↔ Odd (i.natAbs+r) := by
  simpa only [sub_eq_add_neg, Int.natAbs_neg, Int.natAbs_natCast] using
    odd_add_abs i (-(r : ℤ))

 theorem arrowAfter_pos {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) r =
      if i.natAbs < r ∧ Odd (i.natAbs+r) ∧ 0 < j ∧ j.natAbs < r then 1 else 0 := by
  have hir : |i| < |(r:ℤ)| ↔ i.natAbs < r := by
    rw [Int.abs_natCast, ← Int.natCast_natAbs i, Nat.cast_lt]
  by_cases hl : i.natAbs < r
  · have hb : Before (i+j) (i+r) ↔ 0 < j ∧ j.natAbs < r := by
      by_cases hj : 0 < j
      · rw [before_same_source_pos hij (hir.mpr hl) hj]
        have he : (j.natAbs : ℤ) = j := (Int.natCast_natAbs j).trans (abs_of_pos hj)
        omega
      · have hj' : j < 0 := by
          have := abs_nonneg i
          rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
          omega
        rw [before_same_source_neg hij (hir.mpr hl) hj']
        omega
    simp only [arrowAfter, hir, odd_add_natAbs, hb]
  · simp only [arrowAfter, hir, hl, false_and, ite_false]

 theorem arrowAfter_neg {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) ∧ (0 < j ∨ r < j.natAbs) then 1 else 0 := by
  have hir : |i| < |-(r:ℤ)| ↔ i.natAbs < r := by
    rw [abs_neg, Int.abs_natCast, ← Int.natCast_natAbs i, Nat.cast_lt]
  by_cases hl : i.natAbs < r
  · have hb : Before (i+j) (i+ -r) ↔ 0 < j ∨ r < j.natAbs := by
      by_cases hj : 0 < j
      · rw [before_same_source_pos hij (hir.mpr hl) hj]
        omega
      · have hj' : j < 0 := by
          have := abs_nonneg i
          rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
          omega
        rw [before_same_source_neg hij (hir.mpr hl) hj']
        have he : (j.natAbs : ℤ) = -j := (Int.natCast_natAbs j).trans (abs_of_neg hj')
        omega
    simp only [arrowAfter, hir, show i+ -(r:ℤ)=i-r by ring, odd_sub_natAbs]
    rw [show i-(r:ℤ) = i+ -r by ring, hb]
    split_ifs <;> rfl
  · simp only [arrowAfter, hir, hl, false_and, ite_false]

 theorem arrowAfter_next {i j : ℤ} (hij : |i| < |j|) (z : ℤ) :
    arrowAfter j (i+j) z =
      if j.natAbs < z.natAbs ∧ Odd (j.natAbs+z.natAbs) ∧ 0 < j then 1 else 0 := by
  have hlt : |j| < |z| ↔ j.natAbs < z.natAbs := by
    rw [← Int.natCast_natAbs j, ← Int.natCast_natAbs z, Nat.cast_lt]
  by_cases h : |j| < |z|
  · simp only [arrowAfter, before_next_source hij h, odd_add_abs, hlt]
  · have h' := hlt.not.mp h
    simp only [arrowAfter,h,h',false_and,ite_false]

/-- The two signed endpoints at one rank, normalized before summation. -/
 theorem arrowAfter_pair {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) then
        if 0 < j then 1 + (if j.natAbs < r then 1 else 0)
        else (if r < j.natAbs then 1 else 0)
      else 0 := by
  rw [arrowAfter_pos hij, arrowAfter_neg hij]
  by_cases h : i.natAbs < r ∧ Odd (i.natAbs+r)
  · rcases h with ⟨hl, ho⟩
    simp only [hl, ho, true_and]
    split_ifs <;> omega
  · have hp : ¬(i.natAbs < r ∧ Odd (i.natAbs+r) ∧ 0 < j ∧ j.natAbs < r) := by tauto
    have hn : ¬(i.natAbs < r ∧ Odd (i.natAbs+r) ∧ (0 < j ∨ r < j.natAbs)) := by tauto
    simp only [h, hp, hn, ite_false, add_zero]

 theorem arrowAfter_pair_below {i j : ℤ} (hij : |i| < |j|) {r : ℕ}
    (hr : r < j.natAbs) :
    arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) then 1 else 0 := by
  rw [arrowAfter_pair hij]
  have hn : ¬j.natAbs < r := by omega
  simp only [hr, hn, ite_true, ite_false, add_zero, ite_self]

 theorem countAfter_base {i j : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) :
    countAfter i (i+j) j = (j.natAbs-i.natAbs-1)/2 := by
  unfold countAfter
  rw [arrowAfter_self,add_zero]
  have hs : ∀ r ∈ Finset.range j.natAbs,
      arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
        if i.natAbs < r ∧ Odd (i.natAbs+r) then 1 else 0 := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    exact arrowAfter_pair_below hij hr'
  rw [Finset.sum_congr rfl hs, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hh : i.natAbs < j.natAbs := by
    rw [← Nat.cast_lt (α := ℤ),Int.natCast_natAbs,Int.natCast_natAbs]
    exact hij
  have he : j.natAbs = i.natAbs+2*((j.natAbs-i.natAbs-1)/2)+1 := by
    rw [Nat.odd_iff] at ho
    omega
  conv_lhs => rw [he]
  exact eligible_ranks_card _ _

/-- A double internal level together with the singleton top contributes one
outgoing arrow per rank, independently of top parity. -/
 theorem total_outgoing_count (L C : ℕ) (h : L ≤ C) :
    (∑ r ∈ Finset.range C, if L < r ∧ Odd (L+r) then 2 else 0) +
      (if L < C ∧ Odd (L+C) then 1 else 0) = C-L := by
  induction C, h using Nat.le_induction with
  | base =>
    have hz : ∀ r ∈ Finset.range L, ¬ L < r := by
      intro r hr
      have := Finset.mem_range.mp hr
      omega
    have hs : (∑ r ∈ Finset.range L, if L < r ∧ Odd (L+r) then 2 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp only [hz r hr, false_and, ite_false]
    simp only [hs, lt_self_iff_false, false_and, ite_false, add_zero, Nat.sub_self]
  | succ C h ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : L<C
    · have hc' : L<C+1 := by omega
      by_cases he : Odd (L+C)
      · have he' : ¬Odd (L+(C+1)) := by rw [Nat.odd_iff] at he ⊢; omega
        simp only [hc,he,and_self,ite_true] at ih
        simp only [hc,he,hc',he',and_true,and_false,ite_true,ite_false,add_zero]
        omega
      · have he' : Odd (L+(C+1)) := by rw [Nat.odd_iff] at he ⊢; omega
        simp only [he,and_false,ite_false,add_zero] at ih
        simp only [hc,he,hc',he',and_true,and_false,ite_true,ite_false,add_zero]
        omega
    · have heq : C=L := by omega
      subst C
      have he : ¬Odd (L+L) := by rw [Nat.odd_iff]; omega
      have he' : Odd (L+(L+1)) := by rw [Nat.odd_iff]; omega
      simp only [lt_self_iff_false,false_and,ite_false,add_zero] at ih
      simp only [he,he',and_false,and_true,ite_false,Nat.lt_succ_self,ite_true,add_zero]
      omega

end
end KLInvariance.SignedDihedral
end


section
namespace KLInvariance.SignedDihedral
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SignedDihedral.instDecidable_oAI_2 (p : Prop) : Decidable p := Classical.propDecidable p

 theorem arrowAfter_far {i j z : ℤ} (hij : |i| < |j|) (hjz : |j| < |z|) :
    arrowAfter i (i+j) z = if Odd (i.natAbs+z.natAbs) ∧ 0 < j then 1 else 0 := by
  have hiz := hij.trans hjz
  have hb : Before (i+j) (i+z) ↔ 0 < j := by
    by_cases hj : 0 < j
    · rw [before_same_source_pos hij hiz hj]
      rw [abs_of_pos hj] at hjz
      rw [lt_abs] at hjz
      omega
    · have hj' : j < 0 := by
        have := abs_nonneg i
        rw [abs_of_nonpos (by omega : j ≤ 0)] at hij
        omega
      rw [before_same_source_neg hij hiz hj']
      rw [abs_of_neg hj',lt_abs] at hjz
      omega
  simp only [arrowAfter,hiz,true_and,odd_add_abs,hb]

 @[expose] def positiveCount (L M C : ℕ) : ℕ :=
  (∑ r ∈ Finset.range C, if L < r ∧ Odd (L+r) then (if M < r then 2 else 1) else 0) +
    (if M < C ∧ Odd (L+C) then 1 else 0)

 theorem positiveCount_formula (L M C : ℕ) (hLM : L < M) (ho : Odd (L+M))
    (hMC : M ≤ C) : positiveCount L M C = (M-L-1)/2 + (C-M) := by
  induction C, hMC using Nat.le_induction with
  | base =>
    have he : M = L+2*((M-L-1)/2)+1 := by
      rw [Nat.odd_iff] at ho
      omega
    have hs : (∑ r ∈ Finset.range M,
        if L < r ∧ Odd (L+r) then (if M < r then 2 else 1) else 0) =
        (∑ r ∈ Finset.range M, if L < r ∧ Odd (L+r) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hn : ¬ M < r := by have := Finset.mem_range.mp hr; omega
      simp only [hn,ite_false]
    rw [positiveCount,hs,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp only [lt_self_iff_false,false_and,ite_false,add_zero,Nat.sub_self]
    conv_lhs => rw [he]
    exact eligible_ranks_card _ _
  | succ C hMC ih =>
    rw [positiveCount,Finset.sum_range_succ]
    unfold positiveCount at ih
    by_cases h : M<C
    · have h' : M<C+1 := by omega
      have hl : L<C := by omega
      by_cases hc : Odd (L+C)
      · have hc' : ¬Odd (L+(C+1)) := by rw [Nat.odd_iff] at hc ⊢; omega
        simp only [h,h',hl,hc,hc',and_true,and_false,ite_true,ite_false,add_zero] at ih ⊢
        omega
      · have hc' : Odd (L+(C+1)) := by rw [Nat.odd_iff] at hc ⊢; omega
        simp only [h,h',hl,hc,hc',and_true,and_false,ite_true,ite_false,add_zero] at ih ⊢
        omega
    · have heq : C=M := by omega
      subst C
      have hc' : ¬Odd (L+(M+1)) := by rw [Nat.odd_iff] at ho ⊢; omega
      simp only [lt_self_iff_false,false_and,ite_false,add_zero] at ih
      simp only [hLM,ho,hc',and_self,and_false,ite_true,ite_false,lt_self_iff_false,add_zero]
      omega

 theorem countAfter_pos_formula {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (hj : 0 < j)
    (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = (j.natAbs-i.natAbs-1)/2 + (c.natAbs-j.natAbs) := by
  rcases h with rfl|h
  · rw [countAfter_base hij ho,Nat.sub_self,add_zero]
  have hMC : j.natAbs < c.natAbs := by
    exact_mod_cast (show (j.natAbs:ℤ) < c.natAbs by simpa only [Int.natCast_natAbs] using h)
  have hLM : i.natAbs < j.natAbs := by
    exact_mod_cast (show (i.natAbs:ℤ) < j.natAbs by simpa only [Int.natCast_natAbs] using hij)
  have hs : ∀ r ∈ Finset.range c.natAbs,
      arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) then (if j.natAbs < r then 2 else 1) else 0 := by
    intro r _
    rw [arrowAfter_pair hij]
    simp only [hj, ite_true]
    split_ifs <;> omega
  rw [countAfter,Finset.sum_congr rfl hs,arrowAfter_far hij h]
  simp only [hj,and_true]
  have heq : (if Odd (i.natAbs+c.natAbs) then 1 else 0) =
      (if j.natAbs < c.natAbs ∧ Odd (i.natAbs+c.natAbs) then 1 else 0) := by
    simp only [hMC,true_and]
  rw [heq]
  exact positiveCount_formula _ _ _ hLM ho hMC.le

 theorem countAfter_neg_formula {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (hj : j < 0)
    (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = (j.natAbs-i.natAbs-1)/2 := by
  rcases h with rfl|h
  · exact countAfter_base hij ho
  have hMC : j.natAbs < c.natAbs := by
    exact_mod_cast (show (j.natAbs:ℤ) < c.natAbs by simpa only [Int.natCast_natAbs] using h)
  have hn : ¬0<j := by omega
  have hs : (∑ r ∈ Finset.range c.natAbs, (arrowAfter i (i+j) r + arrowAfter i (i+j) (-r))) =
      (∑ r ∈ Finset.range j.natAbs, (arrowAfter i (i+j) r + arrowAfter i (i+j) (-r))) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hMC.le)
    intro r _ hr
    have hr' : ¬ r < j.natAbs := by simpa only [Finset.mem_range] using hr
    rw [arrowAfter_pair hij]
    simp only [hn, hr', ite_false]
    split_ifs <;> rfl
  rw [countAfter,hs,arrowAfter_far hij h]
  simp only [hn,and_false,ite_false,add_zero]
  have hh := countAfter_base hij ho
  rw [countAfter,arrowAfter_self,add_zero] at hh
  exact hh

 theorem countAfter_next_formula {i j c : ℤ} (hij : |i| < |j|)
    (h : c=j ∨ |j| < |c|) :
    countAfter j (i+j) c = if 0<j then c.natAbs-j.natAbs else 0 := by
  have hMC : j.natAbs ≤ c.natAbs := by
    rcases h with rfl|h
    · exact le_rfl
    · exact_mod_cast (show (j.natAbs:ℤ) ≤ c.natAbs by simpa only [Int.natCast_natAbs] using h.le)
  unfold countAfter
  simp_rw [arrowAfter_next hij]
  simp only [Int.natAbs_natCast,Int.natAbs_neg]
  by_cases hj : 0<j
  · simp only [hj,and_true,ite_true]
    have hs : ∀ r ∈ Finset.range c.natAbs,
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 1 else 0) +
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 1 else 0) =
        (if j.natAbs < r ∧ Odd (j.natAbs+r) then 2 else 0) := by
      intro r _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl hs]
    exact total_outgoing_count _ _ hMC
  · simp only [hj,and_false,ite_false,add_zero,Finset.sum_const_zero]

/-- The signed-index cardinality identity for the source's forward angular
order. Its identification with actual Coxeter angular roots is separate. -/
 theorem countAfter_difference {i j c : ℤ} (hij : |i| < |j|)
    (ho : Odd (i.natAbs+j.natAbs)) (h : c=j ∨ |j| < |c|) :
    countAfter i (i+j) c = countAfter j (i+j) c + (j.natAbs-i.natAbs-1)/2 := by
  rw [countAfter_next_formula hij h]
  by_cases hj : 0<j
  · rw [ite_eq_left hj,countAfter_pos_formula hij ho hj h,Nat.add_comm]
  · have hj' : j<0 := by
      have := abs_nonneg i
      rw [abs_of_nonpos (by omega : j≤0)] at hij
      omega
    rw [ite_eq_right hj,zero_add,countAfter_neg_formula hij ho hj' h]

end
end KLInvariance.SignedDihedral
end

end OAI
