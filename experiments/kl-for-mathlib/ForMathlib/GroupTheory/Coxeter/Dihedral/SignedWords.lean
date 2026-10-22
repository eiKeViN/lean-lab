module
public import Mathlib
public import ForMathlib.Combinatorics.Dihedral.SignedCount
public import ForMathlib.GroupTheory.Coxeter.Bruhat.Descent
public import ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport
public import ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords. Source spans: DihedralIntervals:1, DihedralIntervals:7, DihedralIntervals:8, DihedralIntervals:19, DihedralIntervals:9, DihedralIntervals:12, DihedralIntervals:15, DihedralIntervals:16.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem wordProd_alt_odd (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    cs.wordProd (alt i (2*n+1)) = (cs.simple i * cs.simple (!i)) ^ n * cs.simple i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+2 by omega, alt_add_two]
    simp only [cs.wordProd_cons, ih, pow_succ']
    group

 @[expose] def rotation (cs : CoxeterSystem M W) : W := cs.simple false * cs.simple true

 theorem simple_rotation (cs : CoxeterSystem M W) :
    cs.simple false * rotation cs = (rotation cs)⁻¹ * cs.simple false := by
  simp only [rotation, mul_inv_rev, cs.inv_simple]
  rw [cs.simple_mul_simple_cancel_left, mul_assoc, cs.simple_mul_simple_self, mul_one]

 theorem simple_rotation_zpow (cs : CoxeterSystem M W) (n : ℤ) :
    cs.simple false * rotation cs ^ n = rotation cs ^ (-n) * cs.simple false := by
  have h : SemiconjBy (cs.simple false) (rotation cs) (rotation cs)⁻¹ :=
    simple_rotation cs
  have hh := h.zpow_right n
  change cs.simple false * rotation cs ^ n = ((rotation cs)⁻¹) ^ n * cs.simple false at hh
  simpa only [inv_zpow, zpow_neg] using hh

/-- The signed coordinate evaluates both alternating rays in the same group.
The Euclidean quotient also gives the correct odd negative coordinates. -/
 @[expose] def indexWord (cs : CoxeterSystem M W) (i : ℤ) : W :=
  if i % 2 = 0 then rotation cs ^ (i/2)
  else rotation cs ^ (i/2) * cs.simple false

 theorem indexWord_even (cs : CoxeterSystem M W) (n : ℤ) :
    indexWord cs (2*n) = rotation cs ^ n := by simp [indexWord]

 theorem indexWord_odd (cs : CoxeterSystem M W) (n : ℤ) :
    indexWord cs (2*n+1) = rotation cs ^ n * cs.simple false := by
  simp only [indexWord, show (2*n+1)%2 = 1 by omega, show (1:ℤ) ≠ 0 by omega, ite_false,
    show (2*n+1)/2 = n by omega]

 theorem indexWord_nat (cs : CoxeterSystem M W) (n : ℕ) :
    indexWord cs n = cs.wordProd (alt false n) := by
  rcases Nat.even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [show k+k = 2*k by omega, Nat.cast_mul, Nat.cast_ofNat, indexWord_even,
      wordProd_alt_even]
    simp only [rotation, Bool.not_false, zpow_natCast]
  · rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, indexWord_odd, wordProd_alt_odd]
    simp only [rotation, Bool.not_false, zpow_natCast]

 theorem indexWord_neg_nat (cs : CoxeterSystem M W) (n : ℕ) :
    indexWord cs (-(n:ℤ)) = cs.wordProd (alt true n) := by
  have hr : cs.simple true * cs.simple false = (rotation cs)⁻¹ := by
    simp only [rotation, mul_inv_rev, cs.inv_simple]
  rcases Nat.even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [show k+k = 2*k by omega, Nat.cast_mul, Nat.cast_ofNat,
      show -(2*(k:ℤ)) = 2*(-k) by ring, indexWord_even, wordProd_alt_even]
    simp only [Bool.not_true, hr, zpow_neg, zpow_natCast, inv_pow]
  · rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one,
      show -(2*(k:ℤ)+1) = 2*(-(k:ℤ)-1)+1 by ring, indexWord_odd,
      wordProd_alt_odd]
    rw [show -(k:ℤ)-1 = -(k:ℤ)+(-1) by ring, zpow_add]
    simp only [zpow_neg, zpow_natCast, zpow_one, Bool.not_true, hr, inv_pow]
    simp only [rotation, mul_inv_rev, cs.inv_simple]
    simp only [mul_assoc, cs.simple_mul_simple_self, mul_one]

 theorem exists_indexWord (cs : CoxeterSystem M W) (w : W) :
    ∃ i : ℤ, |i| = (cs.length w : ℤ) ∧ indexWord cs i = w := by
  obtain ⟨i,hi⟩ := exists_alt cs w
  cases i
  · exact ⟨cs.length w, by simp, (indexWord_nat cs _).trans hi.symm⟩
  · exact ⟨-(cs.length w : ℤ), by simp, (indexWord_neg_nat cs _).trans hi.symm⟩

/-- A reflection acts on the signed index line by reflection in its midpoint.
Finite dihedral groups are handled by equality in the group, without choosing
residue representatives here. -/
 theorem indexWord_reflection_mul (cs : CoxeterSystem M W) {a : ℤ} (ha : Odd a)
    (i : ℤ) : indexWord cs a * indexWord cs i = indexWord cs (a-i) := by
  obtain ⟨k,hk⟩ := ha
  have hk' : a = 2*k+1 := by omega
  rw [hk',indexWord_odd]
  rcases Int.even_or_odd i with ⟨l,hl⟩ | ⟨l,hl⟩
  · have hl' : i=2*l := by omega
    rw [hl',indexWord_even,show 2*k+1-2*l=2*(k-l)+1 by ring,indexWord_odd]
    rw [mul_assoc, simple_rotation_zpow, ← mul_assoc, ← zpow_add]
    congr 2
  · have hl' : i=2*l+1 := by omega
    rw [hl',indexWord_odd,show 2*k+1-(2*l+1)=2*(k-l) by ring,indexWord_even]
    calc
      (rotation cs ^ k * cs.simple false) * (rotation cs ^ l * cs.simple false) =
          rotation cs ^ k * (cs.simple false * rotation cs ^ l) * cs.simple false := by group
      _ = rotation cs ^ k * (rotation cs ^ (-l) * cs.simple false) * cs.simple false := by
        rw [simple_rotation_zpow]
      _ = rotation cs ^ (k-l) := by
        rw [← mul_assoc, mul_assoc (rotation cs ^ k * rotation cs ^ (-l)),
          cs.simple_mul_simple_self, mul_one, ← zpow_add]
        congr 1

 theorem indexWord_label (cs : CoxeterSystem M W) {i j : ℤ} (h : Odd (i+j)) :
    indexWord cs j * (indexWord cs i)⁻¹ = indexWord cs (i+j) := by
  have he := indexWord_reflection_mul cs h i
  rw [show i+j-i=j by omega] at he
  rw [← he]
  group

end
end KLInvariance.Dihedral
end


section
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]

 theorem bruhat_top_of_all_descents (cs : CoxeterSystem M W) (w : W)
    (hw : ∀ i, cs.length (cs.simple i * w) < cs.length w) (x : W) :
    BruhatLE cs x w := by
  classical
  have hword : ∀ ω, BruhatLE cs (cs.wordProd ω) w := by
    intro ω
    induction ω with
    | nil => simpa only [cs.wordProd_nil] using one_bruhat cs w
    | cons i ω ih =>
      have hu := upperSimple_mono cs i ih
      have hz := le_upperSimple cs i (cs.simple i * cs.wordProd ω)
      rw [upperSimple_mul] at hz
      have he : upperSimple cs i w = w := by simp only [upperSimple,ite_eq_left (hw i)]
      rw [he] at hu
      change BruhatLE cs (cs.simple i * cs.wordProd ω) w
      exact hz.trans hu
  obtain ⟨ω,_,hx⟩ := cs.exists_isReduced x
  rw [hx]
  exact hword ω

namespace Dihedral
variable {N : CoxeterMatrix Bool} (ds : CoxeterSystem N W)

 theorem exists_common_upper (s : Finset W) : ∃ b, ∀ x ∈ s, BruhatLE ds x b := by
  classical
  by_cases hb : BddAbove (Set.range ds.length)
  · have hf : (Set.range ds.length).Finite := hb.finite
    obtain ⟨b,hb⟩ := (Set.range_nonempty ds.length).csSup_mem hf
    have hmax (x : W) : ds.length x ≤ ds.length b := by
      rw [hb]
      exact le_csSup (hf.bddAbove) (Set.mem_range_self x)
    refine ⟨b,fun x _ => bruhat_top_of_all_descents ds b ?_ x⟩
    intro i
    have hle := hmax (ds.simple i*b)
    have hne := ds.length_simple_mul b i
    omega
  · have hn : ∀ n : ℕ, ∃ w, n < ds.length w := by
      intro n
      by_contra h
      push Not at h
      exact hb ⟨n,by rintro m ⟨x,rfl⟩; exact h x⟩
    obtain ⟨b,hb⟩ := hn (s.sup ds.length)
    exact ⟨b,fun x hx => shorter_bruhat ds ((Finset.le_sup hx).trans_lt hb)⟩

end Dihedral
end KLInvariance
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem map_not_alt (i : Bool) (n : ℕ) : (alt i n).map Bool.not = alt (!i) n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [alt_succ,List.map_cons,ih,alt_succ]

 theorem swap_alt (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    swap cs (cs.wordProd (alt i n)) = cs.wordProd (alt (!i) n) := by
  rw [swap_wordProd,map_not_alt]

 theorem length_alt_le_length (cs : CoxeterSystem M W) (i : Bool) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (cs.wordProd (alt i n)) = n := by
  obtain ⟨j,hj⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt j (cs.length w)) := by
    change cs.length (cs.wordProd _) = _
    rw [← hj,length_alt]
  have hn := (reduced_alt_take cs hr h).eq
  rw [length_alt] at hn
  have hi : i=j ∨ i=(!j) := by cases i <;> cases j <;> simp
  rcases hi with rfl|rfl
  · exact hn
  · rw [← swap_alt,length_swap,hn]

 theorem length_indexWord_nat (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (indexWord cs n) = n := by
  rw [indexWord_nat]
  exact length_alt_le_length cs false h

 theorem length_indexWord_neg_nat (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n ≤ cs.length w) : cs.length (indexWord cs (-(n:ℤ))) = n := by
  rw [indexWord_neg_nat]
  exact length_alt_le_length cs true h

 theorem length_indexWord (cs : CoxeterSystem M W) {i : ℤ} {w : W}
    (h : i.natAbs ≤ cs.length w) : cs.length (indexWord cs i) = i.natAbs := by
  obtain hi|hi := le_total 0 i
  · have he : i=(i.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_nonneg hi]
    nth_rw 1 [he]
    exact length_indexWord_nat cs h
  · have he : i= -(i.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_nonpos hi,neg_neg]
    nth_rw 1 [he]
    exact length_indexWord_neg_nat cs h

 theorem leftDescent_alt (cs : CoxeterSystem M W) (i : Bool) {n : ℕ} {w : W}
    (hn : 0<n) (h : n ≤ cs.length w) :
    cs.IsLeftDescent (cs.wordProd (alt i n)) i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  unfold CoxeterSystem.IsLeftDescent
  rw [length_alt_le_length cs i h,alt_succ,cs.wordProd_cons,cs.simple_mul_simple_cancel_left]
  have hh := cs.length_wordProd_le (alt (!i) k)
  rw [length_alt] at hh
  omega

 theorem indexWord_add_even (cs : CoxeterSystem M W) (i n : ℤ) :
    indexWord cs (i+2*n) = rotation cs ^ n * indexWord cs i := by
  have hm : (i+2*n)%2=i%2 := by omega
  have hd : (i+2*n)/2=i/2+n := by omega
  simp only [indexWord,hm,hd,zpow_add]
  split_ifs
  · exact (Commute.zpow_zpow_self (rotation cs) (i/2) n).eq
  · rw [← mul_assoc,(Commute.zpow_zpow_self (rotation cs) (i/2) n).eq,mul_assoc]

/-- The maximal-length case supplies the precise signed period, without an
extra finiteness hypothesis or a numerical cosine restriction. -/
 theorem rotation_pow_max (cs : CoxeterSystem M W) (w : W)
    (hmax : ∀ z, cs.length z ≤ cs.length w) : rotation cs ^ cs.length w = 1 := by
  have hd (i : Bool) : cs.IsLeftDescent w i := by
    have hle := hmax (cs.simple i*w)
    have hne := cs.length_simple_mul w i
    unfold CoxeterSystem.IsLeftDescent
    omega
  have he : indexWord cs (cs.length w) = indexWord cs (-(cs.length w:ℤ)) := by
    rw [indexWord_nat,indexWord_neg_nat,← eq_alt_of_descent cs false (hd false),
      ← eq_alt_of_descent cs true (hd true)]
  have hp := indexWord_add_even cs (-(cs.length w:ℤ)) (cs.length w)
  rw [show -(cs.length w:ℤ)+2*(cs.length w:ℤ)=(cs.length w:ℤ) by ring,
    zpow_natCast,he] at hp
  exact mul_right_cancel (show rotation cs ^ cs.length w * indexWord cs (-(cs.length w:ℤ)) =
      1 * indexWord cs (-(cs.length w:ℤ)) by simpa only [one_mul] using hp.symm)

 theorem indexWord_period (cs : CoxeterSystem M W) {N : ℕ}
    (hN : rotation cs ^ N = 1) (i k : ℤ) :
    indexWord cs (i+2*(N:ℤ)*k) = indexWord cs i := by
  rw [show i+2*(N:ℤ)*k=i+2*((N:ℤ)*k) by ring,indexWord_add_even,zpow_mul,zpow_natCast,hN,
    one_zpow,one_mul]

 theorem indexWord_mod_period (cs : CoxeterSystem M W) {N : ℕ}
    (hN : rotation cs ^ N = 1) (i : ℤ) :
    indexWord cs (i%(2*(N:ℤ))) = indexWord cs i := by
  have hp := indexWord_period cs hN (i%(2*(N:ℤ))) (i/(2*(N:ℤ)))
  rw [Int.emod_add_mul_ediv] at hp
  exact hp.symm

end
end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem natAbs_lt_iff (i j : ℤ) : i.natAbs<j.natAbs ↔ |i| < |j| := by
  rw [← Int.natCast_natAbs,← Int.natCast_natAbs]
  exact (Nat.cast_lt (α := ℤ)).symm

 theorem index_step_iff (cs : CoxeterSystem M W) {i j : ℤ}
    (hi : cs.length (indexWord cs i)=i.natAbs)
    (hj : cs.length (indexWord cs j)=j.natAbs) :
    BruhatStep cs (indexWord cs i) (indexWord cs j) ↔ |i| < |j| ∧ Odd (i+j) := by
  rw [step_iff_odd,hi,hj,natAbs_lt_iff]
  apply and_congr_right
  intro h
  have hnat := (natAbs_lt_iff i j).mpr h
  rw [SignedDihedral.odd_add_abs,Nat.odd_iff,Nat.odd_iff]
  omega

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem indexWord_step (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n+1 ≤ cs.length w) : BruhatStep cs (indexWord cs n) (indexWord cs (n+1:ℕ)) := by
  rw [step_iff_odd,length_indexWord_nat cs (show n≤cs.length w by omega),
    length_indexWord_nat cs h]
  exact ⟨by omega,by simp⟩

 theorem neg_indexWord_step (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (h : n+1 ≤ cs.length w) :
    BruhatStep cs (indexWord cs (-(n:ℤ))) (indexWord cs (-((n+1:ℕ):ℤ))) := by
  rw [step_iff_odd,length_indexWord_neg_nat cs (show n≤cs.length w by omega),
    length_indexWord_neg_nat cs h]
  exact ⟨by omega,by simp⟩

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

 theorem length_indexWord_unbounded (cs : CoxeterSystem M W)
    (hu : ∀ n : ℕ, ∃ w, n ≤ cs.length w) (i : ℤ) :
    cs.length (indexWord cs i) = i.natAbs := by
  obtain ⟨w,hw⟩ := hu i.natAbs
  exact length_indexWord cs hw

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.Dihedral.instDecidableEq_oAI : DecidableEq W := Classical.decEq W

 theorem indexWord_pos_ne_neg (cs : CoxeterSystem M W) {n : ℕ} {w : W}
    (hn : 0<n) (hw : n<cs.length w) : indexWord cs n ≠ indexWord cs (-(n:ℤ)) := by
  have hp := leftDescent_alt cs false hn hw.le
  have hm := leftDescent_alt cs true hn hw.le
  rw [← indexWord_nat] at hp
  rw [← indexWord_neg_nat] at hm
  intro he
  rw [← he] at hm
  have hl := length_indexWord_nat cs hw.le
  obtain ⟨i,_,hi⟩ := unique_leftDescent cs (w := indexWord cs n) (z := w)
    (by rw [hl]; exact hn) (by rw [hl]; exact hw)
  have hf := hi false hp
  have ht := hi true hm
  simp_all

 theorem lower_length_fiber (cs : CoxeterSystem M W) (c : W) {n : ℕ}
    (hc : n<cs.length c) :
    (lowerFinset cs c).filter (fun z => cs.length z=n) =
      {indexWord cs n,indexWord cs (-(n:ℤ))} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := exists_alt cs z
    rw [hz.2] at hi
    cases i
    · exact Or.inl (hi.trans (indexWord_nat cs n).symm)
    · exact Or.inr (hi.trans (indexWord_neg_nat cs n).symm)
  · rintro (rfl|rfl)
    · have hl := length_indexWord_nat cs hc.le
      exact ⟨shorter_bruhat cs (by rw [hl]; exact hc),hl⟩
    · have hl := length_indexWord_neg_nat cs hc.le
      exact ⟨shorter_bruhat cs (by rw [hl]; exact hc),hl⟩

 theorem lower_zero_fiber (cs : CoxeterSystem M W) (c : W) :
    (lowerFinset cs c).filter (fun z => cs.length z=0) = {1} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_singleton]
  constructor
  · exact fun hz => cs.length_eq_zero_iff.mp hz.2
  · rintro rfl
    exact ⟨one_bruhat cs c,cs.length_one⟩

 theorem lower_top_fiber (cs : CoxeterSystem M W) (c : W) :
    (lowerFinset cs c).filter (fun z => cs.length z=cs.length c) = {c} := by
  classical
  ext z
  simp only [Finset.mem_filter,mem_lowerFinset,Finset.mem_singleton]
  constructor
  · intro hz
    by_contra hne
    have hl := length_lt_of_bruhat_ne cs hz.1 hne
    omega
  · rintro rfl
    exact ⟨bruhat_refl cs _,rfl⟩

/-- Actual finite dihedral lower ideals have two internal alternating rays
and a singleton top. The doubled identity contributes zero. -/
 theorem sum_lower_signed (cs : CoxeterSystem M W) (c : W)
    {A : Type*} [AddCommMonoid A] (f : W → A) (h1 : f 1=0) :
    ∑ z ∈ lowerFinset cs c, f z =
      (∑ n ∈ Finset.range (cs.length c),
        (f (indexWord cs n)+f (indexWord cs (-(n:ℤ))))) + f c := by
  classical
  have hmap : ∀ z ∈ lowerFinset cs c, cs.length z ∈ Finset.range (cs.length c+1) := by
    intro z hz
    have hl := length_le_of_bruhat cs ((mem_lowerFinset cs c z).mp hz)
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap f,Finset.sum_range_succ,lower_top_fiber,
    Finset.sum_singleton]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hc := Finset.mem_range.mp hn
  by_cases hz : n=0
  · subst n
    rw [lower_zero_fiber]
    simp only [Finset.sum_singleton,indexWord_nat,indexWord_neg_nat,alt_zero,
      cs.wordProd_nil,h1,add_zero]
  · rw [lower_length_fiber cs c hc,
      Finset.sum_pair (indexWord_pos_ne_neg cs (by omega) hc)]

end
end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 @[expose] def GoodIndex (cs : CoxeterSystem M W) (i : ℤ) : Prop :=
  ∀ w, (∀ z, cs.length z ≤ cs.length w) → -(cs.length w:ℤ) < i ∧ i ≤ (cs.length w:ℤ)

 theorem maximal_or_unbounded (cs : CoxeterSystem M W) :
    (∃ w, ∀ z, cs.length z ≤ cs.length w) ∨ (∀ n : ℕ, ∃ w, n≤cs.length w) := by
  by_cases hb : BddAbove (Set.range cs.length)
  · have hf : (Set.range cs.length).Finite := hb.finite
    obtain ⟨b,hb⟩ := (Set.range_nonempty cs.length).csSup_mem hf
    left
    refine ⟨b,fun z => ?_⟩
    rw [hb]
    exact le_csSup hf.bddAbove (Set.mem_range_self z)
  · right
    intro n
    by_contra h
    push Not at h
    exact hb ⟨n,by rintro m ⟨z,rfl⟩; exact (h z).le⟩

 theorem max_length_positive (cs : CoxeterSystem M W) {w : W}
    (hmax : ∀ z, cs.length z ≤ cs.length w) : 0<cs.length w := by
  have h := hmax (cs.simple false)
  rw [cs.length_simple] at h
  omega

 theorem maximal_eq (cs : CoxeterSystem M W) {w z : W}
    (hmax : ∀ x, cs.length x≤cs.length w) (hz : cs.length z=cs.length w) : z=w := by
  have htop := bruhat_top_of_all_descents cs w (fun i => by
    have h := hmax (cs.simple i*w)
    have h' := cs.length_simple_mul w i
    omega) z
  by_contra hne
  have hl := length_lt_of_bruhat_ne cs htop hne
  omega

 theorem goodIndex_nat (cs : CoxeterSystem M W) {n : ℕ} {c : W}
    (hc : n≤cs.length c) : GoodIndex cs (n:ℤ) := by
  intro w hw
  have h := hw c
  have hp := max_length_positive cs hw
  omega

 theorem goodIndex_neg_nat (cs : CoxeterSystem M W) {n : ℕ} {c : W}
    (hc : n<cs.length c) : GoodIndex cs (-(n:ℤ)) := by
  intro w hw
  have h := hw c
  omega

 theorem exists_good_index (cs : CoxeterSystem M W) (z : W) :
    ∃ i : ℤ, GoodIndex cs i ∧ |i|=(cs.length z:ℤ) ∧ indexWord cs i=z := by
  obtain ⟨i,hi,he⟩ := exists_indexWord cs z
  by_cases hgood : GoodIndex cs i
  · exact ⟨i,hgood,hi,he⟩
  · have hbad : ∃ w, (∀ x, cs.length x≤cs.length w) ∧
        ¬(-(cs.length w:ℤ) < i ∧ i ≤ (cs.length w:ℤ)) := by
      simpa only [GoodIndex,not_forall,exists_prop] using hgood
    obtain ⟨w,hw,hbad⟩ := hbad
    have hl := hw z
    have habs := abs_le.mp (show |i|≤(cs.length w:ℤ) by rw [hi]; exact_mod_cast hl)
    have hi' : i= -(cs.length w:ℤ) := by omega
    have hwz : cs.length w=cs.length z := by rw [hi'] at hi; simpa using hi
    refine ⟨cs.length z,goodIndex_nat cs (c := z) le_rfl,by simp,?_⟩
    have hp := indexWord_period cs (rotation_pow_max cs w hw) (-(cs.length w:ℤ)) 1
    rw [show -(cs.length w:ℤ)+2*(cs.length w:ℤ)*1=(cs.length w:ℤ) by ring] at hp
    rw [← hwz,hp,← hi',he]

end
end KLInvariance.Dihedral
end

end OAI
