module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Localization.FiniteCharacters. Source spans: IntegralPairings:25.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.FiniteCharacterLocalization
universe u v w
variable {R : Type u} [CommRing R] {X : Type v}
  {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
noncomputable section

 @[expose] def diagonal (f : X → R) : (∀ x, E x) →ₗ[R] (∀ x, E x) where
  toFun m x := f x • m x
  map_add' := by intro m n; funext x; exact smul_add _ _ _
  map_smul' := by intro r m; funext x; exact smul_comm _ _ _

 @[expose] def stabilizer (L : Submodule R (∀ x, E x)) : Subalgebra R (X → R) where
  carrier := {f | ∀ m ∈ L, diagonal f m ∈ L}
  mul_mem' := by
    intro f g hf hg m hm
    have h := hf _ (hg m hm)
    simpa only [diagonal,LinearMap.coe_mk,AddHom.coe_mk,Pi.mul_apply,mul_smul] using h
  one_mem' := by intro m hm; simpa [diagonal] using hm
  add_mem' := by
    intro f g hf hg m hm
    have he : diagonal (f+g) m = diagonal f m+diagonal g m := by
      funext x
      exact add_smul _ _ _
    rw [he]
    exact L.add_mem (hf m hm) (hg m hm)
  zero_mem' := by
    intro m _
    have he : diagonal (0 : X → R) m=0 := by
      funext x
      exact zero_smul _ _
    rw [he]
    exact L.zero_mem
  algebraMap_mem' := by
    intro r m hm
    exact L.smul_mem r hm

 theorem diagonal_mem {L : Submodule R (∀ x, E x)} {f : X → R}
    (hf : f ∈ stabilizer L) {m : ∀ x, E x} (hm : m ∈ L) :
    diagonal f m ∈ L := hf m hm

/-- The vanishing polynomial of the finite weights is zero on the chosen
block and equals their product off that block when the weight vanishes there.
This pointwise calculation is independent of any stable lattice. -/
theorem projector_product_values (C : Finset X) (f : X → R)
    (hz : ∀ x ∉ C, f x = 0) :
    (∀ x ∈ C, (∏ y ∈ C, (algebraMap R (X → R) (f y)-f)) x = 0) ∧
    (∀ x ∉ C, (∏ y ∈ C, (algebraMap R (X → R) (f y)-f)) x = ∏ y ∈ C, f y) := by
  classical
  constructor
  · intro x hx
    rw [Finset.prod_apply]
    apply Finset.prod_eq_zero hx
    simp
  · intro x hx
    rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro y _
    simp [hz x hx]

/-- A polynomial in stable diagonal weights which kills the complement of
`C` and is a common scalar on `C`. Its scalar is a product, not a quotient. -/
 theorem uniform_projector (L : Submodule R (∀ x, E x)) (C : Finset X)
    (f : X → R) (hf : f ∈ stabilizer L) (hz : ∀ x ∉ C, f x=0) :
    ∃ g ∈ stabilizer L,
      (∀ x ∈ C, g x=∏ y ∈ C, f y) ∧ (∀ x ∉ C, g x=0) := by
  classical
  let d : R := ∏ y ∈ C, f y
  let h : X → R := ∏ y ∈ C, (algebraMap R (X → R) (f y)-f)
  have hh : h ∈ stabilizer L := by
    exact (stabilizer L).prod_mem fun y _ =>
      (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem (f y)) hf
  refine ⟨algebraMap R (X → R) d-h,
    (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem d) hh,?_,?_⟩
  · intro x hx
    change d-h x=d
    suffices h x=0 by rw [this,sub_zero]
    exact (projector_product_values C f hz).1 x hx
  · intro x hx
    change d-h x=0
    suffices h x=d by rw [this,sub_self]
    exact (projector_product_values C f hz).2 x hx

/-- The product of separating test values on a residue block is not divisible
by the prime when each test is nondivisible at the reference point and congruent
throughout the block. Only coordinate congruences enter this product argument. -/
theorem class_product_not_dvd [Fintype X] [DecidableEq X] (p : R) (hp : Prime p)
    (C : Finset X) (x : X) (test : X → X → R)
    (hunit : ∀ y ∉ C, ¬ p ∣ test y x)
    (hcongr : ∀ z ∈ C, ∀ y, p ∣ test y z-test y x)
    (z : X) (hz : z ∈ C) : ¬ p ∣ (∏ y ∈ Finset.univ \ C, test y) z := by
  classical
  rw [Finset.prod_apply]
  apply hp.not_dvd_finsetProd
  intro y hy
  have hyC := (Finset.mem_sdiff.mp hy).2
  intro h
  apply hunit y hyC
  simpa only [sub_sub_cancel] using dvd_sub h (hcongr z hz y)

/-- Separate one residue-character class from its complement without
inverting any element of the coefficient domain. -/
 theorem class_projector [Fintype X] (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (C : Finset X) (x : X)
    (test : X → X → R) (htest : ∀ y, test y ∈ stabilizer L)
    (hzero : ∀ y ∉ C, test y y=0)
    (hunit : ∀ y ∉ C, ¬ p ∣ test y x)
    (hcongr : ∀ z ∈ C, ∀ y, p ∣ test y z-test y x) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z ∈ C, g z=d) ∧ (∀ z ∉ C, g z=0) := by
  classical
  let f : X → R := ∏ y ∈ Finset.univ \ C, test y
  have hf : f ∈ stabilizer L :=
    (stabilizer L).prod_mem fun y _ => htest y
  have hfu (z : X) (hz : z ∈ C) : ¬ p ∣ f z :=
    class_product_not_dvd p hp C x test hunit hcongr z hz
  have hfz (z : X) (hz : z ∉ C) : f z=0 := by
    dsimp [f]
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩) (hzero z hz)
  obtain ⟨g,hg,hgc,hgz⟩ := uniform_projector L C f hf hfz
  refine ⟨∏ z ∈ C, f z,?_,g,hg,hgc,hgz⟩
  exact hp.not_dvd_finsetProd (fun z hz => hfu z hz)

/-- The complementary denominator products assemble disjoint character-block
lifts into one scalar multiple of the target. Primality and stable lattice
membership are deliberately absent from this pointwise partition identity. -/
theorem partition_diagonal_sum {Q : Type*} [Fintype Q] [DecidableEq Q]
    (q : X → Q) (z : ∀ x, E x) (d : Q → R) (g : Q → X → R)
    (hgin : ∀ j x, q x=j → g j x=d j)
    (hgout : ∀ j x, q x≠j → g j x=0)
    (m : Q → ∀ x, E x) (hmatch : ∀ j x, q x=j → m j x=z x) :
    (∏ j, d j) • z = ∑ j : Q, (∏ k ∈ Finset.univ.erase j, d k) • diagonal (g j) (m j) := by
  classical
  funext x
  simp only [Pi.smul_apply,Finset.sum_apply]
  rw [Finset.sum_eq_single (q x)]
  · change (∏ j, d j) • z x = (∏ k ∈ Finset.univ.erase (q x),d k) •
      (g (q x) x • m (q x) x)
    rw [hgin _ _ rfl,hmatch _ _ rfl,← mul_smul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  · intro j _ hj
    change (∏ k ∈ Finset.univ.erase j,d k) • (g j x • m j x)=0
    rw [hgout j x (Ne.symm hj),zero_smul,smul_zero]
  · simp

/-- Local lifts on each finite character block assemble after a single
scalar denominator away from the prime. -/
 theorem partition_local_denominator {Q : Type*} [Fintype Q]
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p) (q : X → Q)
    (z : ∀ x, E x) (d : Q → R) (hd : ∀ j, ¬ p ∣ d j)
    (g : Q → X → R) (hg : ∀ j, g j ∈ stabilizer L)
    (hgin : ∀ j x, q x=j → g j x=d j)
    (hgout : ∀ j x, q x≠j → g j x=0)
    (m : Q → ∀ x, E x) (hm : ∀ j, m j ∈ L)
    (hmatch : ∀ j x, q x=j → m j x=z x) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  refine ⟨∏ j, d j,hp.not_dvd_finsetProd (fun j _ => hd j),?_⟩
  rw [partition_diagonal_sum q z d g hgin hgout m hmatch]
  exact L.sum_mem fun j _ => L.smul_mem _ (hg j _ (hm j))

 @[expose] def residueSetoid {A : Type*} (p : R) (χ : A → X → R) : Setoid X where
  r x y := ∀ a, p ∣ χ a x-χ a y
  iseqv := ⟨fun x a => by rw [sub_self]; exact dvd_zero _,
    fun h a => by simpa only [neg_sub] using dvd_neg.mpr (h a),
    fun h h' a => by simpa only [sub_add_sub_cancel] using dvd_add (h a) (h' a)⟩

/-- A point outside a residue-character class admits a stable test that
vanishes there and is prime-nondivisible at the reference point. The chosen tests
remain congruent across the class; finiteness and primeness are not needed here. -/
theorem exists_character_separators {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (χ : A → X → R)
    (hχ : ∀ a, χ a ∈ stabilizer L) (x : X) :
    ∃ test : X → X → R,
      (∀ y, test y ∈ stabilizer L) ∧
      (∀ y, ¬ (residueSetoid p χ).r x y → test y y=0) ∧
      (∀ y, ¬ (residueSetoid p χ).r x y → ¬ p ∣ test y x) ∧
      (∀ z, (residueSetoid p χ).r x z → ∀ y, p ∣ test y z-test y x) := by
  classical
  have ha : ∀ y : {y : X // ¬ (residueSetoid p χ).r x y}, ∃ a, ¬ p ∣ χ a x-χ a y.val := by
    intro y
    exact not_forall.mp y.property
  choose a ha using ha
  let test (y : X) : X → R := if hy : ¬ (residueSetoid p χ).r x y then
    χ (a ⟨y,hy⟩)-algebraMap R (X → R) (χ (a ⟨y,hy⟩) y) else 0
  refine ⟨test,?_,?_,?_,?_⟩
  · intro y
    by_cases hy : ¬ (residueSetoid p χ).r x y
    · simp only [test,dite_eq_left hy]
      exact (stabilizer L).sub_mem (hχ _) ((stabilizer L).algebraMap_mem _)
    · simp only [test,dite_eq_right hy]
      exact (stabilizer L).zero_mem
  · intro y hy
    simp [test,hy]
  · intro y hy
    simpa [test,hy] using ha ⟨y,hy⟩
  · intro z hz y
    by_cases hy : ¬ (residueSetoid p χ).r x y
    · simp only [test,dite_eq_left hy]
      change p ∣ (χ (a ⟨y,hy⟩) z-χ (a ⟨y,hy⟩) y)-
        (χ (a ⟨y,hy⟩) x-χ (a ⟨y,hy⟩) y)
      rw [sub_sub_sub_cancel_right]
      exact (residueSetoid p χ).symm hz _
    · simp only [test,dite_eq_right hy,Pi.zero_apply,sub_self]
      exact dvd_zero _

 theorem character_class_projector [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (x : X) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z, (residueSetoid p χ).r x z → g z=d) ∧
      (∀ z, ¬ (residueSetoid p χ).r x z → g z=0) := by
  classical
  let C : Finset X := Finset.univ.filter ((residueSetoid p χ).r x)
  have hc (z : X) : z ∈ C ↔ (residueSetoid p χ).r x z := by simp [C]
  obtain ⟨test,ht,hz,hu,hcon⟩ := exists_character_separators L p χ hχ x
  obtain ⟨d,hd,g,hg,hgc,hgz⟩ := class_projector L p hp C x test ht
    (fun y hy => hz y (fun h => hy ((hc y).mpr h)))
    (fun y hy => hu y (fun h => hy ((hc y).mpr h)))
    (fun z hz y => hcon z ((hc z).mp hz) y)
  exact ⟨d,hd,g,hg,fun z h => hgc z ((hc z).mpr h),
    fun z h => hgz z (fun hz => h ((hc z).mp hz))⟩

/-- Pair/blockwise liftability at a prime suffices for integral local
membership in a finite character-stable lattice. -/
 theorem character_local_denominator [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (z : ∀ x, E x)
    (hlift : ∀ x, ∃ m ∈ L, ∀ y, (residueSetoid p χ).r x y → m y=z y) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  let Q := Quotient (residueSetoid p χ)
  let : Fintype Q := Fintype.ofFinite Q
  let q : X → Q := Quotient.mk''
  have hq (j : Q) (y : X) : q y=j ↔ (residueSetoid p χ).r j.out y := by
    constructor
    · intro h
      exact (residueSetoid p χ).symm (Quotient.exact (h.trans (Quotient.out_eq j).symm))
    · intro h
      exact (Quotient.sound ((residueSetoid p χ).symm h)).trans (Quotient.out_eq j)
  have hproj (j : Q) := character_class_projector L p hp χ hχ j.out
  choose d hd g hg hgin hgout using hproj
  have hm (j : Q) := hlift j.out
  choose m hm hmatch using hm
  exact partition_local_denominator L p hp q z d hd g hg
    (fun j y h => hgin j y ((hq j y).mp h))
    (fun j y h => hgout j y (fun hh => h ((hq j y).mpr hh)))
    m hm (fun j y h => hmatch j y ((hq j y).mp h))

end
end KLInvariance.FiniteCharacterLocalization
end

end OAI
