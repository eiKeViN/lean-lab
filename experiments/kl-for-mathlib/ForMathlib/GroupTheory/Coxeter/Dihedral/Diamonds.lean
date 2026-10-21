import Mathlib
import ForMathlib.GroupTheory.Coxeter.Bruhat.DiamondClosure
import ForMathlib.GroupTheory.Coxeter.Dihedral.Words
import ForMathlib.Order.Interval.Diamonds

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds. Source spans: ReflectionSchedules:19, ReflectionSchedules:20.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

theorem alt_add_two (i : Bool) (n : ℕ) :
    alt i (n+2) = i :: (!i) :: alt i n := by
  simp only [alt_succ,Bool.not_not]

theorem alt_odd_sandwich (i : Bool) (n : ℕ) :
    alt i (2*(n+1)+1) = i :: (alt (!i) (2*n+1) ++ [i]) := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    have h₁ : 2*(n+1+1)+1 = (2*(n+1)+1)+2 := by omega
    have h₂ : 2*(n+1)+1 = (2*n+1)+2 := by omega
    rw [h₁,alt_add_two,ih,h₂,alt_add_two]
    simp only [Bool.not_not,List.cons_append]

theorem odd_alt_reflection (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    cs.IsReflection (cs.wordProd (alt i (2*n+1))) := by
  induction n generalizing i with
  | zero => simpa [alt] using cs.isReflection_simple i
  | succ n ih =>
    rw [alt_odd_sandwich,cs.wordProd_cons,cs.wordProd_append]
    obtain ⟨w,j,hw⟩ := ih (!i)
    refine ⟨cs.simple i*w,j,?_⟩
    simp only [cs.wordProd_cons,cs.wordProd_nil,mul_one,hw,mul_inv_rev,
      cs.inv_simple]
    group

theorem reflection_iff_odd (cs : CoxeterSystem M W) (w : W) :
    cs.IsReflection w ↔ Odd (cs.length w) := by
  constructor
  · exact fun h => h.odd_length
  · intro h
    obtain ⟨n,hn⟩ := h
    obtain ⟨i,hi⟩ := exists_alt cs w
    rw [hi,hn]
    convert odd_alt_reflection cs i n using 2

theorem step_iff_odd (cs : CoxeterSystem M W) (x y : W) :
    BruhatStep cs x y ↔ cs.length x < cs.length y ∧ Odd (cs.length y-cs.length x) := by
  have hm := cs.length_mul_mod_two y x⁻¹
  rw [cs.length_inv] at hm
  constructor
  · rintro ⟨hlen,t,ht,hprod⟩
    refine ⟨hlen,?_⟩
    have hteq : y*x⁻¹=t := by rw [hprod]; group
    have ho := ht.odd_length
    rw [← hteq,Nat.odd_iff] at ho
    rw [Nat.odd_iff]
    omega
  · rintro ⟨hlen,ho⟩
    refine ⟨hlen,y*x⁻¹,?_,by group⟩
    rw [reflection_iff_odd,Nat.odd_iff]
    rw [Nat.odd_iff] at ho
    omega

theorem two_elements_length (cs : CoxeterSystem M W) {n : ℕ} (hn : 0 < n)
    {w : W} (hw : n < cs.length w) :
    ∃ a b : W, a ≠ b ∧ ∀ z, cs.length z = n ↔ z = a ∨ z = b := by
  obtain ⟨i,hi⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    change cs.length (cs.wordProd _) = _
    rw [← hi,length_alt]
  have hr₁ := reduced_alt_take cs hr (show n+1 ≤ cs.length w by omega)
  have hr₀ := reduced_alt_take cs hr (Nat.le_of_lt hw)
  have hr₂ : cs.IsReduced (alt (!i) n) := by simpa using hr₁.drop 1
  have hlen₀ : cs.length (cs.wordProd (alt i n)) = n := by simpa using hr₀.eq
  have hlen₂ : cs.length (cs.wordProd (alt (!i) n)) = n := by simpa using hr₂.eq
  refine ⟨cs.wordProd (alt i n),cs.wordProd (alt (!i) n),?_,?_⟩
  · intro heq
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hp : cs.wordProd (alt i (k+1+1)) = cs.wordProd (alt (!i) k) := by
      rw [alt_succ,cs.wordProd_cons,← heq,alt_succ,cs.wordProd_cons,
        cs.simple_mul_simple_cancel_left]
    have hlen := cs.length_wordProd_le (alt (!i) k)
    have hred := hr₁.eq
    rw [hp,length_alt] at hred
    rw [length_alt] at hlen
    omega
  · intro z
    constructor
    · intro hz
      obtain ⟨j,hj⟩ := exists_alt cs z
      rw [hz] at hj
      have hj' : j=i ∨ j=(!i) := by cases j <;> cases i <;> simp
      rcases hj' with rfl|rfl
      · exact Or.inl hj
      · exact Or.inr hj
    · rintro (rfl|rfl) <;> assumption

theorem two_step_rank_two (cs : CoxeterSystem M W) {x y : W}
    (hlen : cs.length y = cs.length x+2) :
    ∃ a b : W, a ≠ b ∧
      ∀ z, (BruhatStep cs x z ∧ BruhatStep cs z y) ↔ z=a ∨ z=b := by
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs (by omega : 0 < cs.length x+1)
    (w := y) (by omega)
  refine ⟨a,b,hab,?_⟩
  intro z
  rw [← hab',step_iff_odd,step_iff_odd]
  constructor
  · rintro ⟨⟨hx,_⟩,⟨hy,_⟩⟩
    omega
  · intro hz
    constructor <;> constructor
    · omega
    · rw [Nat.odd_iff]; omega
    · omega
    · rw [Nat.odd_iff]; omega

end KLInvariance.Dihedral
end


section
namespace KLInvariance
variable {I W : Type*} [Group W] {M : CoxeterMatrix I}

theorem interval_covBy_of_length_succ (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : x ≤ y)
    (hlen : cs.length y.val = cs.length x.val+1) : x ⋖ y := by
  apply covBy_iff_lt_and_eq_or_eq.mpr
  refine ⟨lt_iff_le_and_ne.mpr ⟨hxy,?_⟩,?_⟩
  · intro heq
    have := congrArg (fun z : Interval cs u b => cs.length z.val) heq
    omega
  · intro z hxz hzy
    by_cases hz : z=x
    · exact Or.inl hz
    · right
      by_contra hzy'
      have h₁ := length_lt_of_bruhat_ne cs hxz (fun he => hz (Subtype.ext he.symm))
      have h₂ := length_lt_of_bruhat_ne cs hzy (fun he => hzy' (Subtype.ext he))
      omega

namespace Dihedral
variable {M₂ : CoxeterMatrix Bool}

theorem two_interval_elements_length (cs : CoxeterSystem M₂ W)
    {u b : W} (x y : Interval cs u b) {n : ℕ}
    (hn₁ : cs.length x.val < n) (hn₂ : n < cs.length y.val) :
    ∃ a c : Interval cs u b, a ≠ c ∧ cs.length a.val=n ∧ cs.length c.val=n := by
  obtain ⟨a,c,hac,hlevel⟩ := two_elements_length cs (by omega : 0<n) hn₂
  have ha := (hlevel a).mpr (Or.inl rfl)
  have hc := (hlevel c).mpr (Or.inr rfl)
  have hmem (z : W) (hz : cs.length z=n) :
      BruhatLE cs u z ∧ BruhatLE cs z b :=
    ⟨bruhat_trans cs x.property.1 (shorter_bruhat cs (by omega)),
      bruhat_trans cs (shorter_bruhat cs (by omega)) y.property.2⟩
  exact ⟨⟨a,hmem a ha⟩,⟨c,hmem c hc⟩,
    fun he => hac (congrArg Subtype.val he),ha,hc⟩

/-- Completeness of the actual unlabelled eight-edge closure for genuine
rank-two Coxeter systems. This is a necessary local case of Dyer's general
reconstruction, not a replacement main theorem. -/
theorem diamondEdges_of_bruhatStep (cs : CoxeterSystem M₂ W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  suffices ∀ n : ℕ, ∀ x y : Interval cs u b,
      cs.length y.val-cs.length x.val=n → BruhatStep cs x.val y.val →
      DiamondEdges x y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hlen hxy
    have hodd := ((step_iff_odd cs x.val y.val).mp hxy).2
    rw [hlen,Nat.odd_iff] at hodd
    by_cases hn : n=1
    · apply DiamondEdges.cover
      exact interval_covBy_of_length_succ cs (Relation.ReflTransGen.single hxy) (by omega)
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨a,a₂,hab,ha,hb⟩ := two_interval_elements_length cs x y
        (n := cs.length x.val+1) (by omega) (by have := hxy.1; omega)
      obtain ⟨c,d,hcd,hc,hd⟩ := two_interval_elements_length cs x y
        (n := cs.length x.val+2) (by omega) (by have := hxy.1; omega)
      have hcover {p q : Interval cs u b}
          (hpq : cs.length q.val=cs.length p.val+1) : DiamondEdges p q :=
        DiamondEdges.cover (interval_covBy_of_length_succ cs
          (shorter_bruhat cs (by omega)) hpq)
      have htop {p : Interval cs u b} (hp : cs.length p.val=cs.length x.val+2) :
          DiamondEdges p y := by
        apply ih (cs.length y.val-cs.length p.val) (by have := hxy.1; omega) p y rfl
        rw [step_iff_odd]
        constructor
        · have := hxy.1; omega
        · rw [Nat.odd_iff]; have := hxy.1; omega
      exact DiamondEdges.diamond (hcover (by omega)) (hcover (by omega))
        (hcover (by omega)) (hcover (by omega)) (hcover (by omega)) (hcover (by omega))
        (htop hc) (htop hd) hab hcd

end Dihedral
end KLInvariance
end

end OAI
