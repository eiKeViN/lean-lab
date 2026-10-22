module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords
public import ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder. Source spans: DihedralIntervals:10, DihedralIntervals:13, DihedralIntervals:14.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 @[expose] def prefixRoot (w : planeSubgroup M cs P) (n : ℕ) : PositiveRoot M cs :=
  if h : n < B.system.length w then B.edgeRoot (indexWord_step B.system h) else B.left

 @[expose] def negPrefixRoot (w : planeSubgroup M cs P) (n : ℕ) : PositiveRoot M cs :=
  if h : n < B.system.length w then B.edgeRoot (neg_indexWord_step B.system h) else B.right

 theorem prefixRoot_strictMono (w : planeSubgroup M cs P) :
    StrictMonoOn (fun n => geometricSlope (B.prefixRoot w n)) (Set.Iio (B.system.length w)) := by
  apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
  intro n _ hn hn'
  change n < B.system.length w at hn
  change n+1 < B.system.length w at hn'
  change geometricSlope (B.prefixRoot w n) < geometricSlope (B.prefixRoot w (n+1))
  rw [prefixRoot,prefixRoot,dite_eq_left hn,dite_eq_left hn']
  apply (B.edgeRoot_slopes_iff _ _).mpr
  rw [indexWord_nat]
  exact leftDescent_alt B.system false (by omega) hn'.le

 theorem negPrefixRoot_strictAnti (w : planeSubgroup M cs P) :
    StrictAntiOn (fun n => geometricSlope (B.negPrefixRoot w n))
      (Set.Iio (B.system.length w)) := by
  apply strictAntiOn_of_succ_lt Set.ordConnected_Iio
  intro n _ hn hn'
  change n < B.system.length w at hn
  change n+1 < B.system.length w at hn'
  change geometricSlope (B.negPrefixRoot w (n+1)) < geometricSlope (B.negPrefixRoot w n)
  rw [negPrefixRoot,negPrefixRoot,dite_eq_left hn,dite_eq_left hn']
  have ht : B.system.IsLeftDescent (indexWord B.system (-((n+1:ℕ):ℤ))) true := by
    rw [indexWord_neg_nat]
    exact leftDescent_alt B.system true (by omega) hn'.le
  have hlen := length_indexWord_neg_nat B.system hn'.le
  have hu := unique_leftDescent B.system (w := indexWord B.system (-((n+1:ℕ):ℤ)))
    (z := w) (by rw [hlen]; omega) (by rw [hlen]; omega)
  have hf : ¬B.system.IsLeftDescent (indexWord B.system (-((n+1:ℕ):ℤ))) false := by
    intro hf
    obtain ⟨i,_,hi⟩ := hu
    have h1 := hi true ht
    have h2 := hi false hf
    simp_all
  have hnlt := (B.edgeRoot_slopes_iff (neg_indexWord_step B.system hn)
    (neg_indexWord_step B.system hn')).not.mpr hf
  apply lt_of_le_of_ne (le_of_not_gt hnlt)
  intro he
  have he' := geometricSlope_injective he
  exact graphRoot_ne_of_path
    ((B.bruhatStep_iff _ _).mpr (neg_indexWord_step B.system hn))
    ((B.bruhatStep_iff _ _).mpr (neg_indexWord_step B.system hn')) he'.symm

 theorem edgeRoot_eq_of_label {x y z w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzw : BruhatStep B.system z w)
    (he : y*x⁻¹=w*z⁻¹) : B.edgeRoot hxy = B.edgeRoot hzw := by
  unfold edgeRoot graphRoot
  apply congrArg (positiveRoot M cs)
  apply Subtype.ext
  exact congrArg (fun z : planeSubgroup M cs P => (z : W)) he

 theorem prefixRoot_eq_edgeRoot {x y w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) {n : ℕ} (hn : n<B.system.length w)
    (he : y*x⁻¹=indexWord B.system (2*(n:ℤ)+1)) :
    B.prefixRoot w n = B.edgeRoot hxy := by
  rw [prefixRoot,dite_eq_left hn]
  apply B.edgeRoot_eq_of_label
  rw [he,indexWord_label B.system (by rw [Int.odd_iff]; omega)]
  congr 1
  push_cast
  ring

 theorem negPrefixRoot_eq_edgeRoot {x y w : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) {n : ℕ} (hn : n<B.system.length w)
    (he : y*x⁻¹=indexWord B.system (-(2*(n:ℤ)+1))) :
    B.negPrefixRoot w n = B.edgeRoot hxy := by
  rw [negPrefixRoot,dite_eq_left hn]
  apply B.edgeRoot_eq_of_label
  rw [he,indexWord_label B.system (by rw [Int.odd_iff]; omega)]
  congr 1
  push_cast
  ring

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem edgeRoot_inverted_iff {x y : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (w : planeSubgroup M cs P) :
    rootInverted (w:W) (B.edgeRoot hxy) ↔ B.system.length ((y*x⁻¹)*w)<B.system.length w := by
  have hh := B.inversion_iff (t := y*x⁻¹)
    (graphRoot_represents ((B.bruhatStep_iff x y).mpr hxy))
    (B.edgeRoot_plane hxy) (B.edgeRoot hxy).property.2 w
  change rootInverted (w:W) (B.edgeRoot hxy) ↔ _ at hh
  rw [hh]
  exact and_iff_right hxy.label_reflection

 theorem edgeRoot_positive_lt_negative
    (hu : ∀ n : ℕ, ∃ w, n ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    (k l : ℕ)
    (hx : y*x⁻¹=indexWord B.system (2*(k:ℤ)+1))
    (hz : t*z⁻¹=indexWord B.system (-(2*(l:ℤ)+1))) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) := by
  let w := indexWord B.system ((k+1:ℕ):ℤ)
  have hi : rootInverted (w:W) (B.edgeRoot hxy) := by
    rw [B.edgeRoot_inverted_iff,hx]
    unfold w
    rw [indexWord_reflection_mul B.system (by rw [Int.odd_iff]; omega),
      length_indexWord_unbounded B.system hu,length_indexWord_unbounded B.system hu]
    have he : 2*(k:ℤ)+1-((k+1:ℕ):ℤ)=(k:ℤ) := by omega
    rw [he]
    simp only [Int.natAbs_natCast]
    omega
  have hn : ¬rootInverted (w:W) (B.edgeRoot hzt) := by
    rw [B.edgeRoot_inverted_iff,hz]
    unfold w
    rw [indexWord_reflection_mul B.system (by rw [Int.odd_iff]; omega),
      length_indexWord_unbounded B.system hu,length_indexWord_unbounded B.system hu]
    have he : -(2*(l:ℤ)+1)-((k+1:ℕ):ℤ) = -((2*l+k+2:ℕ):ℤ) := by omega
    rw [he]
    simp only [Int.natAbs_neg,Int.natAbs_natCast]
    omega
  have hd : B.system.IsLeftDescent w false := by
    obtain ⟨w',hw'⟩ := hu (k+1)
    change B.system.IsLeftDescent (indexWord B.system ((k+1:ℕ):ℤ)) false
    rw [indexWord_nat]
    exact leftDescent_alt B.system false (by omega) hw'
  have hm : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  have hl : rootInverted (w:W) B.left := by
    have hh := (B.simpleRoot_inverted_coset_iff hm w false).mpr hd
    simpa only [mul_one,simpleRoot,Bool.false_eq_true,↓reduceIte] using hh
  exact B.slope_lt_of_inverted_left (w:W) hl _ _ (B.edgeRoot_plane hxy)
    (B.edgeRoot_plane hzt) hi hn

/-- The two angular rays of an infinite canonical dihedral subsystem, with
actual ambient labels, have precisely the source's signed-midpoint order. -/
 theorem edgeRoot_infinite_order
    (hu : ∀ n : ℕ, ∃ w, n ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    {a b : ℤ} (ha : Odd a) (hb : Odd b)
    (hx : y*x⁻¹=indexWord B.system a) (hz : t*z⁻¹=indexWord B.system b) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) ↔
      SignedDihedral.Before a b := by
  have repr (q : ℤ) (hq : Odd q) :
      ∃ k : ℕ, q=2*(k:ℤ)+1 ∨ q= -(2*(k:ℤ)+1) := by
    have habs := Int.natCast_natAbs q
    have ho : q.natAbs % 2=1 := by
      rw [Int.odd_iff] at hq
      rcases le_total 0 q with h|h
      · rw [abs_of_nonneg h] at habs
        omega
      · rw [abs_of_nonpos h] at habs
        omega
    refine ⟨q.natAbs/2,?_⟩
    rcases le_total 0 q with h|h
    · left
      rw [abs_of_nonneg h] at habs
      omega
    · right
      rw [abs_of_nonpos h] at habs
      omega
  obtain ⟨k,hk|hk⟩ := repr a ha <;> obtain ⟨l,hl|hl⟩ := repr b hb
  · obtain ⟨w,hw⟩ := hu (max k l+1)
    have hk' : k<B.system.length w := by omega
    have hl' : l<B.system.length w := by omega
    rw [hk] at hx
    rw [hl] at hz
    rw [← B.prefixRoot_eq_edgeRoot hxy hk' hx,← B.prefixRoot_eq_edgeRoot hzt hl' hz]
    have hs := B.prefixRoot_strictMono w
    have he : geometricSlope (B.prefixRoot w k) < geometricSlope (B.prefixRoot w l) ↔ k<l :=
      hs.lt_iff_lt hk' hl'
    rw [he,hk,hl]
    unfold SignedDihedral.Before
    omega
  · rw [hk] at hx
    rw [hl] at hz
    have hh := B.edgeRoot_positive_lt_negative hu hxy hzt k l hx hz
    have hbefore : SignedDihedral.Before a b := by
      rw [hk,hl]
      unfold SignedDihedral.Before
      omega
    exact iff_of_true hh hbefore
  · rw [hk] at hx
    rw [hl] at hz
    have hh := B.edgeRoot_positive_lt_negative hu hzt hxy l k hz hx
    have hn := not_lt_of_gt hh
    have hbefore : ¬SignedDihedral.Before a b := by
      rw [hk,hl]
      unfold SignedDihedral.Before
      omega
    exact iff_of_false hn hbefore
  · obtain ⟨w,hw⟩ := hu (max k l+1)
    have hk' : k<B.system.length w := by omega
    have hl' : l<B.system.length w := by omega
    rw [hk] at hx
    rw [hl] at hz
    rw [← B.negPrefixRoot_eq_edgeRoot hxy hk' hx,← B.negPrefixRoot_eq_edgeRoot hzt hl' hz]
    have hs := B.negPrefixRoot_strictAnti w
    have he : geometricSlope (B.negPrefixRoot w k) < geometricSlope (B.negPrefixRoot w l) ↔ l<k := by
      constructor
      · intro h
        by_contra hn
        rcases lt_or_eq_of_le (le_of_not_gt hn) with hkl | rfl
        · exact (not_lt_of_gt (hs hk' hl' hkl)) h
        · exact (lt_irrefl _) h
      · exact hs hl' hk'
    rw [he,hk,hl]
    unfold SignedDihedral.Before
    omega

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem max_length_pos (w : planeSubgroup M cs P)
    (hmax : ∀ z, B.system.length z ≤ B.system.length w) : 0 < B.system.length w := by
  have h := hmax (B.system.simple false)
  rw [B.system.length_simple] at h
  omega

 theorem odd_residue_repr {N : ℕ} (hN : 0<N) {a : ℤ} (ha : Odd a) :
    ∃ k : ℕ, k<N ∧ a % (2*(N:ℤ)) = 2*(k:ℤ)+1 := by
  have hl := Int.emod_nonneg a (by omega : (2*(N:ℤ))≠0)
  have hu := Int.emod_lt_of_pos a (by omega : 0<2*(N:ℤ))
  have hp : (a%(2*(N:ℤ)))%2=1 := by
    rw [Int.emod_emod_of_dvd a (by exact dvd_mul_right 2 (N:ℤ))]
    exact Int.odd_iff.mp ha
  refine ⟨(a%(2*(N:ℤ))).toNat/2, ?_, ?_⟩ <;> omega

/-- The actual ambient angular order in a finite canonical plane subsystem
is the increasing residue order on odd doubled midpoints. -/
 theorem edgeRoot_finite_order
    (w : planeSubgroup M cs P) (hmax : ∀ z, B.system.length z ≤ B.system.length w)
    {x y z t : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hzt : BruhatStep B.system z t)
    {a b : ℤ} (ha : Odd a) (hb : Odd b)
    (hx : y*x⁻¹=indexWord B.system a) (hz : t*z⁻¹=indexWord B.system b) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hzt) ↔
      a % (2*(B.system.length w:ℤ)) < b % (2*(B.system.length w:ℤ)) := by
  obtain ⟨k,hk,he⟩ := odd_residue_repr (B.max_length_pos w hmax) ha
  obtain ⟨l,hl,hf⟩ := odd_residue_repr (B.max_length_pos w hmax) hb
  have hp := rotation_pow_max B.system w hmax
  rw [← indexWord_mod_period B.system hp a, he] at hx
  rw [← indexWord_mod_period B.system hp b, hf] at hz
  rw [← B.prefixRoot_eq_edgeRoot hxy hk hx,← B.prefixRoot_eq_edgeRoot hzt hl hz]
  rw [(B.prefixRoot_strictMono w).lt_iff_lt hk hl,he,hf]
  omega

end
end KLInvariance.TitsSpace.PlaneBasis
end

end OAI
