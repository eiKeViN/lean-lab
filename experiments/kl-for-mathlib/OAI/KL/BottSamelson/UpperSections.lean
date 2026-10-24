module
public import Mathlib
public import ForMathlib.Algebra.Module.Localization.FiniteCharacters
public import ForMathlib.Algebra.Module.Localization.ProjectiveLattice
public import ForMathlib.Algebra.Module.Projective.Range
public import ForMathlib.Algebra.Module.ReflectionPair.TensorDescent
public import ForMathlib.LinearAlgebra.KernelCoordinates
public import ForMathlib.LinearAlgebra.PairProjection
public import ForMathlib.LinearAlgebra.Reflection.Classification
public import OAI.KL.BottSamelson.Stalks

public section

/-! Semantic home: OAI.KL.BottSamelson.UpperSections. Source spans: IntegralPairings:23, IntegralPairings:24, IntegralPairings:6, IntegralPairings:27, IntegralPairings:10, IntegralPairings:13, IntegralPairings:14, IntegralPairings:19, IntegralPairings:17, IntegralPairings:18, IntegralPairings:21, IntegralPairings:28.
See migration.json and MIGRATION.md for exact provenance.
Images of Bott word sections on Bruhat upper sets, local-denominator gluing and projectivity of those section images. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem reflection_character_congruence_iff {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (x y : W) :
    (∀ p : SymmetricCoefficient (M := M),
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
        coefficientAction cs x p-coefficientAction cs y p) ↔
      x=y ∨ y=t*x := by
  constructor
  · intro hp
    let w := y*x⁻¹
    have hline (v : Extended M) :
        extendedAction M cs w v-v ∈ Submodule.span ℝ {embed M a} := by
      let p := (coefficientAction cs x).symm (SymmetricAlgebra.ι ℝ (Extended M) v)
      have hx : coefficientAction cs x p=SymmetricAlgebra.ι ℝ (Extended M) v :=
        AlgEquiv.apply_symm_apply _ _
      have hy : coefficientAction cs y p =
          coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) v) := by
        have h := coefficientAction_mul cs w x p
        rw [show w*x=y by dsimp [w]; group,hx] at h
        exact h
      have h := hp p
      rw [hx,hy,coefficientAction_ι,← map_sub] at h
      have hs := (EdgeAlgebra.symmetric_ι_dvd_iff (embed M a)
        (v-extendedAction M cs w v)).mp h
      simpa only [neg_sub,EdgeAlgebra.rootLine] using (EdgeAlgebra.rootLine (k := ℝ) (embed M a)).neg_mem hs
    have hnorm : extendedForm M (embed M a) (embed M a)=2 := by
      rw [(extendedForm_spec M).2.2]
      exact ha.isRoot.norm
    rcases Realization.orthogonal_eq_id_or_rootReflection
      (extendedForm M) (embed M a) hnorm (extendedAction M cs w)
      (extendedAction_preserves M cs w) hline with hid | href
    · left
      have hw : w=1 := by
        apply extendedAction_injective M cs
        apply LinearEquiv.ext
        intro v
        change extendedAction M cs w v=extendedAction M cs 1 v
        rw [map_one]
        change extendedAction M cs w v=v
        exact LinearMap.congr_fun hid v
      exact (mul_inv_eq_one.mp hw).symm
    · right
      have hw : w=t := by
        apply extendedAction_injective M cs
        apply LinearEquiv.ext
        intro v
        rw [ha.extendedAction_eq]
        exact href v
      exact mul_inv_eq_iff_eq_mul.mp hw
  · rintro (rfl | rfl)
    · intro p
      rw [sub_self]
      exact dvd_zero _
    · intro p
      rw [coefficientAction_mul]
      exact reflectionCoefficient_divisible cs ha (coefficientAction cs x p)

 theorem reflection_character_separates {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) {x y : W} (hxy : x ≠ y) (ht : y ≠ t*x) :
    ∃ p : SymmetricCoefficient (M := M),
      ¬ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
        coefficientAction cs x p-coefficientAction cs y p := by
  by_contra! h
  exact (reflection_character_congruence_iff cs ha x y).mp h |>.elim hxy ht

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem isReflection_of_prime_character_congruence
    (p : SymmetricCoefficient (M := M)) (hp : Prime p)
    {x y : W} (hxy : x ≠ y)
    (hcon : ∀ a, p ∣ coefficientAction cs x a-coefficientAction cs y a) :
    cs.IsReflection (y*x⁻¹) := by
  let w := y*x⁻¹
  have hw : w ≠ 1 := by
    intro h
    exact hxy (mul_inv_eq_one.mp h).symm
  have hex : ∃ v : Extended M, extendedAction M cs w v-v ≠ 0 := by
    by_contra! h
    apply hw
    apply extendedAction_injective M cs
    apply LinearEquiv.ext
    intro v
    rw [map_one]
    exact sub_eq_zero.mp (h v)
  obtain ⟨v,hv⟩ := hex
  let d := extendedAction M cs w v-v
  have hd : d ≠ 0 := hv
  have hdiv (z : Extended M) : p ∣ SymmetricAlgebra.ι ℝ (Extended M)
      (extendedAction M cs w z-z) := by
    let a := (coefficientAction cs x).symm (SymmetricAlgebra.ι ℝ (Extended M) z)
    have hx : coefficientAction cs x a=SymmetricAlgebra.ι ℝ (Extended M) z :=
      AlgEquiv.apply_symm_apply _ _
    have hy : coefficientAction cs y a =
        coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) z) := by
      have h := coefficientAction_mul cs w x a
      rw [show w*x=y by dsimp [w]; group,hx] at h
      exact h
    have h := hcon a
    rw [hx,hy,coefficientAction_ι,← map_sub] at h
    simpa only [← map_neg,neg_sub] using dvd_neg.mpr h
  have hassoc := hp.associated_of_dvd (EdgeAlgebra.symmetric_ι_prime d hd) (hdiv v)
  have heq : LinearMap.range ((extendedAction M cs w).toLinearMap-LinearMap.id) =
      Submodule.span ℝ {d} := by
    apply le_antisymm
    · rintro z ⟨a,rfl⟩
      change extendedAction M cs w a-a ∈ Submodule.span ℝ {d}
      exact (EdgeAlgebra.symmetric_ι_dvd_iff d _).mp
        (dvd_trans hassoc.symm.dvd (hdiv a))
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact ⟨v,rfl⟩
  apply isReflection_of_moving_rank_one M cs w
  rw [heq,finrank_span_singleton hd]

 theorem prime_character_class (p : SymmetricCoefficient (M := M)) (hp : Prime p)
    {x y : W} (hxy : x ≠ y)
    (hcon : ∀ a, p ∣ coefficientAction cs x a-coefficientAction cs y a) :
    ∃ t : W, cs.IsReflection t ∧ y=t*x ∧
      ∀ z, (∀ a, p ∣ coefficientAction cs x a-coefficientAction cs z a) ↔
        x=z ∨ z=t*x := by
  let t := y*x⁻¹
  have ht := isReflection_of_prime_character_congruence cs p hp hxy hcon
  let a := (positiveRoot M cs ⟨t,ht⟩).val
  have ha : Represents M cs t a := positiveRoot_represents M cs ⟨t,ht⟩
  have he : t*x=y := by dsimp [t]; group
  obtain ⟨c,hc⟩ := reflectionCoefficient_difference cs ha x
  rw [he] at hc
  have hpa : p ∣ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := hc ▸ hcon c
  have hane : embed M a ≠ 0 := by
    intro h
    have hn : extendedForm M (embed M a) (embed M a)=2 := by
      rw [(extendedForm_spec M).2.2]
      exact ha.isRoot.norm
    rw [h,map_zero] at hn
    norm_num at hn
  have hassoc := hp.associated_of_dvd (EdgeAlgebra.symmetric_ι_prime (embed M a) hane) hpa
  refine ⟨t,ht,he.symm,?_⟩
  intro z
  rw [← reflection_character_congruence_iff cs ha x z]
  exact forall_congr' fun c => ⟨fun h => dvd_trans hassoc.symm.dvd h,
    fun h => dvd_trans hassoc.dvd h⟩

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [klPreservedInstance11 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 @[expose] def BruhatUpper (U : Set W) : Prop :=
  ∀ {x y}, BruhatLE cs x y → x∈U → y∈U

 @[expose] def simpleUnion (i : I) (U : Set W) : Set W := {x | x∈U ∨ cs.simple i*x∈U}
 @[expose] def simpleInter (i : I) (U : Set W) : Set W := {x | x∈U ∧ cs.simple i*x∈U}

 omit [Fintype I] in
 theorem BruhatUpper.mem_simpleUnion (U : Set W) (hU : BruhatUpper cs U) (i : I) (x : W) :
    x∈simpleUnion cs i U ↔ upperSimple cs i x∈U := by
  constructor
  · rintro (hx|hx)
    · exact hU (le_upperSimple cs i x) hx
    · have hh := hU (le_upperSimple cs i (cs.simple i*x)) hx
      simpa only [upperSimple_mul] using hh
  · intro hx
    classical
    unfold upperSimple at hx
    split_ifs at hx with h
    · exact Or.inl hx
    · exact Or.inr hx

 omit [Fintype I] in
 theorem BruhatUpper.mem_simpleInter (U : Set W) (hU : BruhatUpper cs U) (i : I) (x : W) :
    x∈simpleInter cs i U ↔ lowerSimple cs i x∈U := by
  constructor
  · rintro ⟨hx,hsx⟩
    classical
    unfold lowerSimple
    split_ifs <;> assumption
  · intro hx
    refine ⟨hU (lowerSimple_le cs i x) hx,?_⟩
    have he : lowerSimple cs i (cs.simple i*x)∈U := by simpa only [lowerSimple_mul] using hx
    exact hU (lowerSimple_le cs i (cs.simple i*x)) he

include klPreservedInstance11 in
 theorem BruhatUpper.simpleUnion (U : Set W) (hU : BruhatUpper cs U) (i : I) :
    BruhatUpper cs (simpleUnion cs i U) := by
  have _ := klPreservedInstance11
  intro x y hxy hx
  exact (hU.mem_simpleUnion cs U i y).mpr
    (hU (upperSimple_mono cs i hxy) ((hU.mem_simpleUnion cs U i x).mp hx))

include klPreservedInstance11 in
 theorem BruhatUpper.simpleInter (U : Set W) (hU : BruhatUpper cs U) (i : I) :
    BruhatUpper cs (simpleInter cs i U) := by
  have _ := klPreservedInstance11
  intro x y hxy hx
  exact (hU.mem_simpleInter cs U i y).mpr
    (hU (lowerSimple_mono cs i hxy) ((hU.mem_simpleInter cs U i x).mp hx))

 omit [Fintype I] in
 theorem simpleUnion_stable (i : I) (U : Set W) (x : W) :
    cs.simple i*x∈simpleUnion cs i U ↔ x∈simpleUnion cs i U := by
  change (cs.simple i*x∈U ∨ cs.simple i*(cs.simple i*x)∈U) ↔ (x∈U ∨ cs.simple i*x∈U)
  rw [cs.simple_mul_simple_cancel_left,or_comm]

 omit [Fintype I] in
 theorem simpleInter_stable (i : I) (U : Set W) (x : W) :
    cs.simple i*x∈simpleInter cs i U ↔ x∈simpleInter cs i U := by
  change (cs.simple i*x∈U ∧ cs.simple i*(cs.simple i*x)∈U) ↔ (x∈U ∧ cs.simple i*x∈U)
  rw [cs.simple_mul_simple_cancel_left,and_comm]

 omit [Fintype I] in
 theorem cross_edge_is_simple (U : Set W) (hU : BruhatUpper cs U) (i : I)
    {x y : W} (hxy : BruhatStep cs x y) (hsx : cs.simple i*x∈U)
    (hsy : cs.simple i*y∉U) : y=cs.simple i*x := by
  by_contra he
  exact hsy (hU (.single (bruhatStep_simple_mul cs hxy i he)) hsx)

 @[expose] def bottSetImage (l : List I) (U : Set W) := image (bottStalkProjection cs l) U
 instance bottSetImageAddCommGroup (l : List I) (U : Set W) : AddCommGroup (bottSetImage cs l U) :=
  Submodule.addCommGroup _
 instance bottSetImageModule (l : List I) (U : Set W) : Module (SymmetricCoefficient (M := M)) (bottSetImage cs l U) :=
  Submodule.module _

 @[expose] def bottSetProjection (l : List I) (U : Set W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] bottSetImage cs l U := project (bottStalkProjection cs l) U

 @[expose] def BottCompatible (l : List I) (U : Set W) (z : ∀ x : U, bottStalk cs l x.val) : Prop :=
  ∀ (x y : W) (hx : x∈U) (hy : y∈U), BruhatStep cs x y →
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x m=z ⟨x,hx⟩ ∧ bottStalkProjection cs l y m=z ⟨y,hy⟩

 @[expose] def BottFlabby (l : List I) : Prop :=
  ∀ U, BruhatUpper cs U → ∀ z, BottCompatible cs l U z → z∈bottSetImage cs l U

 @[expose] def BottProjectiveUpper (l : List I) : Prop :=
  ∀ U, BruhatUpper cs U → Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSet_scaled (l : List I) (U : Set W)
    (z : ∀ x : U, bottStalk cs l x.val) :
    bottCoordinateDenominator cs l • z ∈ bottSetImage cs l U := by
  classical
  let c (e : BottIndex l) : SymmetricCoefficient (M := M) :=
    if h : bottWeight cs l e∈U then (z ⟨bottWeight cs l e,h⟩).val ⟨e,rfl⟩ else 0
  obtain ⟨m,hm⟩ := bottEvaluation_contains_scaled_coordinates cs l c
  refine ⟨m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  change bottEvaluation cs l e m=bottCoordinateDenominator cs l * (z ⟨bottWeight cs l e,hx⟩).val ⟨e,rfl⟩
  simpa only [c,dite_eq_left hx] using hm e

 theorem BottCompatible.reflection_lift {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (x y : U) (t : W) (ht : cs.IsReflection t) (he : t*x.val=y.val) :
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x.val m=z x ∧ bottStalkProjection cs l y.val m=z y := by
  have he' : t*y.val=x.val := by rw [← he,← mul_assoc,ht.mul_self,one_mul]
  have hne : cs.length y.val ≠ cs.length x.val := by
    rw [← he]
    exact ht.length_mul_right_ne x.val
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨m,hm,hn⟩ := hz y.val x.val y.property x.property ⟨hlt,t,ht,he'.symm⟩
    exact ⟨m,hn,hm⟩
  · exact hz x.val y.val x.property y.property ⟨hlt,t,ht,he.symm⟩

 theorem BottCompatible.prime_lift {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) (x : U) :
    ∃ m : BottSamelsonModule cs l, ∀ y : U,
      (∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a) →
      bottStalkProjection cs l y.val m=z y := by
  classical
  by_cases hx : ∃ y : U, x≠y ∧
      ∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a
  · obtain ⟨y,hxy,hcon⟩ := hx
    obtain ⟨t,ht,he,hclass⟩ := prime_character_class cs p hp
      (fun h => hxy (Subtype.ext h)) hcon
    obtain ⟨m,hm,hn⟩ := hz.reflection_lift cs x y t ht he.symm
    refine ⟨m,?_⟩
    intro w hw
    rcases (hclass w.val).mp hw with hxw | hwy
    · have h : w=x := Subtype.ext hxw.symm
      subst w
      exact hm
    · have h : w=y := Subtype.ext (hwy.trans he.symm)
      subst w
      exact hn
  · obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val (z x)
    refine ⟨m,?_⟩
    intro y hy
    have h : y=x := by
      by_contra h
      exact hx ⟨y,Ne.symm h,hy⟩
    subst y
    exact hm

 @[expose] def BottUpperIndex (l : List I) (U : Set W) := {e : BottIndex l // bottWeight cs l e∈U}

 @[expose] def bottIndexSetEval (l : List I) (U : Set W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    (∀ e : BottUpperIndex cs l U, bottStalk cs l (bottWeight cs l e.val)) :=
  LinearMap.pi (fun e => bottStalkProjection cs l (bottWeight cs l e.val))

 theorem bottIndexSetEval_stable (l : List I) (U : Set W)
    (a : SymmetricCoefficient (M := M)) :
    (fun e : BottUpperIndex cs l U => coefficientAction cs (bottWeight cs l e.val) a) ∈
      stabilizer (LinearMap.range (bottIndexSetEval cs l U)) := by
  rintro z ⟨m,rfl⟩
  refine ⟨bottSamelsonRight cs l a m,?_⟩
  funext e
  exact bottStalkProjection_right cs l _ a m

 theorem BottCompatible.local_denominator {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) :
    ∃ a : SymmetricCoefficient (M := M), ¬p ∣ a ∧ a • z∈bottSetImage cs l U := by
  classical
  let : Fintype (BottUpperIndex cs l U) := inferInstanceAs (Fintype {e : BottIndex l // bottWeight cs l e∈U})
  let zz : ∀ e : BottUpperIndex cs l U, bottStalk cs l (bottWeight cs l e.val) :=
    fun e => z ⟨bottWeight cs l e.val,e.property⟩
  have hlift : ∀ e : BottUpperIndex cs l U, ∃ m ∈ LinearMap.range (bottIndexSetEval cs l U),
      ∀ f, (residueSetoid p (fun a e => coefficientAction cs (bottWeight cs l e.val) a)).r e f → m f=zz f := by
    intro e
    obtain ⟨m,hm⟩ := hz.prime_lift cs p hp ⟨bottWeight cs l e.val,e.property⟩
    exact ⟨bottIndexSetEval cs l U m,⟨m,rfl⟩,fun f hf => hm ⟨bottWeight cs l f.val,f.property⟩ hf⟩
  obtain ⟨a,ha,m,hm⟩ := character_local_denominator
    (LinearMap.range (bottIndexSetEval cs l U)) p hp
    (fun a e => coefficientAction cs (bottWeight cs l e.val) a)
    (bottIndexSetEval_stable cs l U) zz hlift
  refine ⟨a,ha,m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  have hh := congrArg (fun q => (q ⟨e,hx⟩).val ⟨e,rfl⟩) hm
  exact hh

 theorem bottFlabby_of_projective (l : List I) (H : BottProjectiveUpper cs l) :
    BottFlabby cs l := by
  intro U hU z hz
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := H U hU
  let : UniqueFactorizationMonoid (SymmetricCoefficient (M := M)) :=
    (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis ℝ (Extended M))).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact ProjectiveLattice.mem_of_prime_local_membership (bottSetImage cs l U) z
    ⟨bottCoordinateDenominator cs l,bottCoordinateDenominator_ne_zero cs l,bottSet_scaled cs l U z⟩
    (hz.local_denominator cs)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
open CoordinateProjection ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 @[expose] def simplePull (i : I) (U : Set W) : Set W := {x | cs.simple i*x∈U}

 theorem bottSetProjection_zero_iff (l : List I) (U : Set W) (m : BottSamelsonModule cs l) :
    bottSetProjection cs l U m=0 ↔ ∀ x∈U, bottStalkProjection cs l x m=0 :=
  project_zero_iff _ _ _

 theorem bottSetProjection_surjective (l : List I) (U : Set W) :
    Function.Surjective (bottSetProjection cs l U) := project_surjective _ _

 theorem bottStalkProjection_zero_of_eq (l : List I) {x y : W} (h : x=y)
    (m : BottSamelsonModule cs l) (hm : bottStalkProjection cs l x m=0) :
    bottStalkProjection cs l y m=0 := by
  subst y
  exact hm

 theorem bottHeadSet_zero_iff (i : I) (l : List I) (U : Set W)
    (m : BottSamelsonModule cs (i::l)) :
    bottSetProjection cs (i::l) U m=0 ↔
      bottSetProjection cs l U (bottHeadTail cs i l m)=0 ∧
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val=0 := by
  constructor
  · intro hm
    have h := (bottSetProjection_zero_iff cs (i::l) U m).mp hm
    refine ⟨?_,?_⟩
    · apply (bottSetProjection_zero_iff cs l U _).mpr
      intro x hx
      exact congrArg Prod.fst ((bottHeadLocalPair_zero_iff cs i l x m).mp (h x hx))
    · apply (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mpr
      intro x hx
      have hh : bottStalkProjection cs l (cs.simple i*(cs.simple i*x))
          (bottHeadReflectedTail cs i l m).val=0 := congrArg (fun z => z.2.val)
        ((bottHeadLocalPair_zero_iff cs i l (cs.simple i*x) m).mp (h _ hx))
      exact bottStalkProjection_zero_of_eq cs l (cs.simple_mul_simple_cancel_left i) _ hh
  · rintro ⟨hp,hq⟩
    apply (bottSetProjection_zero_iff cs (i::l) U m).mpr
    intro x hx
    apply (bottHeadLocalPair_zero_iff cs i l x m).mpr
    apply Prod.ext
    · exact (bottSetProjection_zero_iff cs l U _).mp hp x hx
    · apply Twist.ext
      exact (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mp hq (cs.simple i*x)
        (by simpa only [simplePull,Set.mem_ofPred_eq,cs.simple_mul_simple_cancel_left] using hx)

 @[expose] def bottSetFirst (i : I) (l : List I) (U : Set W) : bottSetImage cs (i::l) U →ₗ[
    SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  descend (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    ((bottSetProjection cs l U).comp (bottHeadTail cs i l))
    (fun m hm => ((bottHeadSet_zero_iff cs i l U m).mp hm).1)

 @[expose] def bottSetSecond (i : I) (l : List I) (U : Set W) : bottSetImage cs (i::l) U →ₗ[
    SymmetricCoefficient (M := M)]
    Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottSetImage cs l (simplePull cs i U)) :=
  descend (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    ((twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottSetProjection cs l (simplePull cs i U))).comp (bottHeadReflectedTail cs i l))
    (fun m hm => Twist.ext (((bottHeadSet_zero_iff cs i l U m).mp hm).2))

 theorem bottSetFirst_project (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    bottSetFirst cs i l U (bottSetProjection cs (i::l) U m)=
      bottSetProjection cs l U (bottHeadTail cs i l m) := descend_apply _ _ _ _ m

 theorem bottSetSecond_project (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    bottSetSecond cs i l U (bottSetProjection cs (i::l) U m)=
      Twist.mk (bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val) :=
  descend_apply _ _ _ _ m

 theorem bottSetComponents_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective ((bottSetFirst cs i l U).prod (bottSetSecond cs i l U)) := by
  apply injective_of_zero_lift (bottSetProjection cs (i::l) U)
    (bottSetProjection_surjective cs (i::l) U)
  intro m hz
  apply (bottHeadSet_zero_iff cs i l U m).mpr
  have hp := congrArg Prod.fst hz
  have hq := congrArg (fun z => z.2.val) hz
  exact ⟨(bottSetFirst_project cs i l U m).symm.trans hp,
    (congrArg Twist.val (bottSetSecond_project cs i l U m)).symm.trans hq⟩

 @[expose] def bottTensorEnd (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l)) :
    Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs (i::l)) :=
  AlgebraTensorModule.map (LinearMap.id : SymmetricCoefficient (M := M) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)) (e.restrictScalars (simpleFixed cs i))

 theorem bottTensorEnd_seed (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (n : BottSamelsonModule cs l) :
    bottTensorEnd cs i l e ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      (1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] e n := rfl

 theorem bottTensorEnd_first (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadTail cs i l (bottTensorEnd cs i l e m)=e (bottHeadTail cs i l m) :=
  tensorFirst_map e m

 theorem bottTensorEnd_second (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadReflectedTail cs i l (bottTensorEnd cs i l e m)=
      twistMap (coefficientAction cs (cs.simple i)).toRingEquiv e (bottHeadReflectedTail cs i l m) :=
  tensorSecond_map (coefficientAction cs (cs.simple i)).toRingEquiv (fun c => c.property) e m

 theorem bottHead_components_injective (i : I) (l : List I)
    (m : BottSamelsonModule cs (i::l))
    (hp : bottHeadTail cs i l m=0) (hq : bottHeadReflectedTail cs i l m=0) : m=0 := by
  apply bottEvaluation_injective cs (i::l)
  funext e
  have hz : bottStalkProjection cs (i::l) (bottWeight cs (i::l) e) m=0 := by
    apply (bottHeadLocalPair_zero_iff cs i l _ m).mpr
    rw [bottHeadLocalPair_value,hp,hq]
    apply Prod.ext
    · exact map_zero _
    · apply Twist.ext
      exact map_zero _
  exact congrArg (fun z => z.val ⟨e,rfl⟩) hz

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
open FrobeniusDuality ReflectionFrobenius
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHead_difference (i : I) (l : List I) (m : BottSamelsonModule cs (i::l)) :
    ∃ n : BottSamelsonModule cs l,
      bottHeadTail cs i l m-(bottHeadReflectedTail cs i l m).val=simpleRootPolynomial (M := M) i • n :=
  tensor_difference (coefficientAction cs (cs.simple i)).toRingEquiv (fun c => c.property)
    (simpleRootPolynomial (M := M) i) (simple_divisible cs i) m

 @[expose] def bottHeadPatch (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    ∀ x : simpleUnion cs i U, bottStalk cs l x.val := by
  classical
  exact fun x => if x.val∈U then bottStalkProjection cs l x.val (bottHeadTail cs i l m)
    else bottStalkProjection cs l x.val (bottHeadReflectedTail cs i l m).val

 theorem bottHeadPatch_compatible (i : I) (l : List I) (U : Set W) (hU : BruhatUpper cs U)
    (m : BottSamelsonModule cs (i::l))
    (hJ : ∀ x∈simpleInter cs i U,
      bottStalkProjection cs l x (bottHeadTail cs i l m)=
        bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) :
    BottCompatible cs l (simpleUnion cs i U) (bottHeadPatch cs i l U m) := by
  classical
  intro x y hx hy hxy
  by_cases hxU : x∈U
  · have hyU := hU (.single hxy) hxU
    simp only [bottHeadPatch,ite_eq_left hxU,ite_eq_left hyU]
    exact ⟨bottHeadTail cs i l m,rfl,rfl⟩
  · by_cases hyU : y∈U
    · simp only [bottHeadPatch,ite_eq_right hxU,ite_eq_left hyU]
      by_cases hsy : cs.simple i*y∈U
      · exact ⟨(bottHeadReflectedTail cs i l m).val,rfl,(hJ y ⟨hyU,hsy⟩).symm⟩
      · have he := cross_edge_is_simple cs U hU i hxy (hx.resolve_left hxU) hsy
        subst y
        exact PairProjection.cross_lift _ _ (simpleRootPolynomial (M := M) i)
          (bottReflectionEdge_annihilated cs l x (cs.simple i) (simple_represents cs i))
          (bottHeadTail cs i l m) (bottHeadReflectedTail cs i l m).val (bottHead_difference cs i l m)
    · simp only [bottHeadPatch,ite_eq_right hxU,ite_eq_right hyU]
      exact ⟨(bottHeadReflectedTail cs i l m).val,rfl,rfl⟩

 theorem bottHeadPatch_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hJ : ∀ x∈simpleInter cs i U,
      bottStalkProjection cs l x (bottHeadTail cs i l m)=
        bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) :
    ∃ n : BottSamelsonModule cs l,
      (∀ x∈U, bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m)) ∧
      (∀ x∈simplePull cs i U,
        bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) := by
  classical
  obtain ⟨n,hn⟩ := H (simpleUnion cs i U) (hU.simpleUnion cs U i)
    (bottHeadPatch cs i l U m) (bottHeadPatch_compatible cs i l U hU m hJ)
  refine ⟨n,?_,?_⟩
  · intro x hx
    have hh := congrFun hn ⟨x,Or.inl hx⟩
    simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_left hx] using hh
  · intro x hx
    have hh := congrFun hn ⟨x,Or.inr hx⟩
    by_cases hxU : x∈U
    · have hh' : bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m) := by
        simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_left hxU] using hh
      exact hh'.trans (hJ x ⟨hxU,hx⟩)
    · simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_right hxU] using hh

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module TensorProduct CoordinateProjection ReflectionPairTranslation
open FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 @[expose] def bottSetRestrict (l : List I) {U K : Set W} (h : U⊆K) :
    bottSetImage cs l K →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  restrict (bottStalkProjection cs l) h

 theorem bottSetRestrict_project (l : List I) {U K : Set W} (h : U⊆K)
    (n : BottSamelsonModule cs l) :
    bottSetRestrict cs l h (bottSetProjection cs l K n)=bottSetProjection cs l U n := rfl

 theorem bottSetRestrict_surjective (l : List I) {U K : Set W} (h : U⊆K) :
    Function.Surjective (bottSetRestrict cs l h) := restrict_surjective _ h

 theorem bottSetRestrict_zero_iff (l : List I) {U K : Set W} (h : U⊆K)
    (z : bottSetImage cs l K) : bottSetRestrict cs l h z=0 ↔
      ∀ x hx, x∈U → z.val ⟨x,hx⟩=0 := restrict_zero_iff (bottStalkProjection cs l) h z

 @[expose] def bottSeed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    BottSamelsonModule cs (i::l) := (1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n

 theorem bottSeed_first (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadTail cs i l (bottSeed cs i l n)=n := bottHeadTail_seed cs i l n

 theorem bottSeed_second (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadReflectedTail cs i l (bottSeed cs i l n)=Twist.mk n := bottHeadReflectedTail_seed cs i l n

 theorem bottSetFirst_seed (i : I) (l : List I) (U : Set W) (n : BottSamelsonModule cs l) :
    bottSetFirst cs i l U (bottSetProjection cs (i::l) U (bottSeed cs i l n))=
      bottSetProjection cs l U n :=
  (bottSetFirst_project cs i l U _).trans
    (congrArg (bottSetProjection cs l U) (bottSeed_first cs i l n))

 theorem bottSetSecond_seed (i : I) (l : List I) (U : Set W) (n : BottSamelsonModule cs l) :
    bottSetSecond cs i l U (bottSetProjection cs (i::l) U (bottSeed cs i l n))=
      Twist.mk (bottSetProjection cs l (simplePull cs i U) n) :=
  (bottSetSecond_project cs i l U _).trans
    (congrArg (fun t => Twist.mk (bottSetProjection cs l (simplePull cs i U) t.val))
      (bottSeed_second cs i l n))

 theorem bottSeed_zero_stable (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (n : BottSamelsonModule cs l) (hn : bottSetProjection cs l U n=0) :
    bottSetProjection cs (i::l) U (bottSeed cs i l n)=0 := by
  apply (bottHeadSet_zero_iff cs i l U _).mpr
  constructor
  · exact (congrArg (bottSetProjection cs l U) (bottSeed_first cs i l n)).trans hn
  · apply ((congrArg (fun t => bottSetProjection cs l (simplePull cs i U) t.val)
      (bottSeed_second cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simplePull cs i U) n).mpr
    intro x hx
    exact (bottSetProjection_zero_iff cs l U n).mp hn x ((hU x).mp hx)

 theorem bottSetFirst_restrict (i : I) (l : List I) {U K : Set W} (h : U⊆K)
    (z : bottSetImage cs (i::l) K) :
    bottSetFirst cs i l U (bottSetRestrict cs (i::l) h z)=
      bottSetRestrict cs l h (bottSetFirst cs i l K z) := by
  refine functions_eq_of_surjective (bottSetProjection cs (i::l) K)
    (bottSetProjection_surjective cs (i::l) K)
    (fun z => bottSetFirst cs i l U (bottSetRestrict cs (i::l) h z))
    (fun z => bottSetRestrict cs l h (bottSetFirst cs i l K z)) ?_ z
  intro m
  exact (bottSetFirst_project cs i l U m).trans
    (congrArg (bottSetRestrict cs l h) (bottSetFirst_project cs i l K m)).symm

 theorem bottSeed_zero_inter (i : I) (l : List I) (U : Set W)
    (n : BottSamelsonModule cs l) (hn : bottSetProjection cs l U n=0) :
    bottSetProjection cs (i::l) (simpleInter cs i U) (bottSeed cs i l n)=0 := by
  apply (bottHeadSet_zero_iff cs i l (simpleInter cs i U) _).mpr
  have h := (bottSetProjection_zero_iff cs l U n).mp hn
  constructor
  · apply ((congrArg (bottSetProjection cs l (simpleInter cs i U))
      (bottSeed_first cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simpleInter cs i U) n).mpr
    intro x hx
    exact h x hx.1
  · apply ((congrArg (fun t => bottSetProjection cs l (simplePull cs i (simpleInter cs i U)) t.val)
      (bottSeed_second cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simplePull cs i (simpleInter cs i U)) n).mpr
    intro x hx
    exact h x (by simpa only [cs.simple_mul_simple_cancel_left] using hx.2)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ProjectiveRange ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottHeadLocalPair_eq_iff (i : I) (l : List I) (x : W)
    (m n : BottSamelsonModule cs (i::l)) :
    bottStalkProjection cs (i::l) x m=bottStalkProjection cs (i::l) x n ↔
      bottHeadLocalPair cs i l x m=bottHeadLocalPair cs i l x n :=
  maps_eq_iff_of_zero_iff _ _ (bottHeadLocalPair_zero_iff cs i l x) m n

 theorem bottTensorEnd_set_preserve (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (he : ∀ n x, x∈U → bottStalkProjection cs l x (e n)=bottStalkProjection cs l x n)
    (m : BottSamelsonModule cs (i::l)) :
    bottSetProjection cs (i::l) U (bottTensorEnd cs i l e m)=bottSetProjection cs (i::l) U m := by
  apply Subtype.ext
  funext x
  apply (bottHeadLocalPair_eq_iff cs i l x.val _ _).mpr
  apply (bottHeadLocalPair_value cs i l x.val _).trans
  apply Eq.trans ?_ (bottHeadLocalPair_value cs i l x.val m).symm
  apply Prod.ext
  · exact (congrArg (bottStalkProjection cs l x.val) (bottTensorEnd_first cs i l e m)).trans
      (he _ x.val x.property)
  · apply Twist.ext
    exact (congrArg (fun t => bottStalkProjection cs l (cs.simple i*x.val) t.val)
      (bottTensorEnd_second cs i l e m)).trans
      (he _ (cs.simple i*x.val) ((hU x.val).mpr x.property))

 theorem bottTensorEnd_set_kills (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hz : ∀ n, bottSetProjection cs l U n=0 → e n=0)
    (m : BottSamelsonModule cs (i::l)) (hm : bottSetProjection cs (i::l) U m=0) :
    bottTensorEnd cs i l e m=0 := by
  have hmpq := (bottHeadSet_zero_iff cs i l U m).mp hm
  have hqzero : bottSetProjection cs l U (bottHeadReflectedTail cs i l m).val=0 := by
    apply (bottSetProjection_zero_iff cs l U _).mpr
    intro x hx
    exact (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mp hmpq.2 x ((hU x).mpr hx)
  apply bottHead_components_injective cs i l
  · exact (bottTensorEnd_first cs i l e m).trans (hz _ hmpq.1)
  · apply Twist.ext
    exact (congrArg Twist.val (bottTensorEnd_second cs i l e m)).trans (hz _ hqzero)

 theorem bottStableUpper_projective (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    [Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U)] :
    Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) U) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property (bottSetProjection cs l U)
    (LinearMap.id : bottSetImage cs l U →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U)
    (bottSetProjection_surjective cs l U)
  have hs' : ∀ p, bottSetProjection cs l U (s p)=p := LinearMap.congr_fun hs
  let e := s.comp (bottSetProjection cs l U)
  have he : ∀ n x, x∈U → bottStalkProjection cs l x (e n)=bottStalkProjection cs l x n := by
    intro n x hx
    exact congrArg (fun z : bottSetImage cs l U => z.val ⟨x,hx⟩) (hs' (bottSetProjection cs l U n))
  have hz : ∀ n, bottSetProjection cs l U n=0 → e n=0 := by
    intro n hn
    exact (congrArg s hn).trans s.map_zero
  exact projective_of_end (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    (bottTensorEnd cs i l e) (bottTensorEnd_set_preserve cs i l U hU e he)
    (bottTensorEnd_set_kills cs i l U hU e hz)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 @[expose] def bottInterRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l U →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l (simpleInter cs i U) :=
  bottSetRestrict cs l (fun _ h => h.1)

 @[expose] def bottUnionRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l (simpleUnion cs i U) →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  bottSetRestrict cs l (fun _ h => Or.inl h)

 @[expose] def bottUnionPullRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l (simpleUnion cs i U) →ₗ[SymmetricCoefficient (M := M)]
      bottSetImage cs l (simplePull cs i U) :=
  bottSetRestrict cs l (fun _ h => Or.inr h)

 @[expose] def bottCommonKernel (i : I) (l : List I) (U : Set W) :
    Submodule (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) U) :=
  LinearMap.ker (bottInterRestriction cs i (i::l) U) ⊓ LinearMap.ker (bottSetFirst cs i l U)

 @[expose] def bottCommonSecond (i : I) (l : List I) (U : Set W) :
    bottCommonKernel cs i l U →ₗ[SymmetricCoefficient (M := M)]
      Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottSetImage cs l (simplePull cs i U)) :=
  (bottSetSecond cs i l U).comp (bottCommonKernel cs i l U).subtype

 theorem bottCommonSecond_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective (bottCommonSecond cs i l U) :=
  common_kernel_coordinate_injective _ _ _ (bottSetComponents_injective cs i l U)

 @[expose] def bottUnionKernelSecond (i : I) (l : List I) (U : Set W) :
    LinearMap.ker (bottUnionRestriction cs i l U) →ₗ[SymmetricCoefficient (M := M)]
      bottSetImage cs l (simplePull cs i U) :=
  (bottUnionPullRestriction cs i l U).comp (LinearMap.ker (bottUnionRestriction cs i l U)).subtype

 theorem bottUnionKernelSecond_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective (bottUnionKernelSecond cs i l U) := by
  apply kernel_coordinate_injective
  exact restrict_joint_injective (bottStalkProjection cs l)
    (fun _ h => Or.inl h) (fun _ h => Or.inr h) (fun _ h => h)

 theorem bottHeadPatch_lift_of_zero_inter (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hm : bottSetProjection cs (i::l) (simpleInter cs i U) m=0) :
    ∃ n : BottSamelsonModule cs l,
      (∀ x∈U, bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m)) ∧
      (∀ x∈simplePull cs i U,
        bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) := by
  apply bottHeadPatch_lift cs i l H U hU m
  have hz := (bottHeadSet_zero_iff cs i l (simpleInter cs i U) m).mp hm
  intro x hx
  apply ((bottSetProjection_zero_iff cs l (simpleInter cs i U) _).mp hz.1 x hx).trans
  exact ((bottSetProjection_zero_iff cs l (simplePull cs i (simpleInter cs i U)) _).mp hz.2 x
    ((simpleInter_stable cs i U x).mpr hx)).symm

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottCommon_lift (i : I) (l : List I) (U : Set W)
    (z : bottCommonKernel cs i l U) :
    ∃ m : BottSamelsonModule cs (i::l),
      bottSetProjection cs (i::l) U m=z.val ∧
      bottSetProjection cs (i::l) (simpleInter cs i U) m=0 ∧
      bottSetProjection cs l U (bottHeadTail cs i l m)=0 := by
  let m : BottSamelsonModule cs (i::l) :=
    (bottSetProjection_surjective cs (i::l) U z.val).choose
  have hm : bottSetProjection cs (i::l) U m=z.val :=
    (bottSetProjection_surjective cs (i::l) U z.val).choose_spec
  refine ⟨m,hm,?_,?_⟩
  · exact (congrArg (bottInterRestriction cs i (i::l) U) hm).trans z.property.1
  · exact (bottSetFirst_project cs i l U m).symm.trans
      ((congrArg (bottSetFirst cs i l U) hm).trans z.property.2)

 theorem bottCommon_patch_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hmJ : bottSetProjection cs (i::l) (simpleInter cs i U) m=0)
    (hmp : bottSetProjection cs l U (bottHeadTail cs i l m)=0) :
    ∃ n : BottSamelsonModule cs l, bottSetProjection cs l U n=0 ∧
      bottSetProjection cs l (simplePull cs i U) n=
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val := by
  let n : BottSamelsonModule cs l := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose
  have hnp := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose_spec.1
  have hnq := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose_spec.2
  refine ⟨n,?_,Subtype.ext (funext fun x => hnq x.val x.property)⟩
  apply (bottSetProjection_zero_iff cs l U n).mpr
  intro x hx
  exact (hnp x hx).trans ((bottSetProjection_zero_iff cs l U _).mp hmp x hx)

 theorem bottCommon_range_of_patch (i : I) (l : List I) (U : Set W)
    (z : bottCommonKernel cs i l U) (m : BottSamelsonModule cs (i::l))
    (hm : bottSetProjection cs (i::l) U m=z.val) (n : BottSamelsonModule cs l)
    (hnU : bottSetProjection cs l U n=0)
    (hnq : bottSetProjection cs l (simplePull cs i U) n=
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  let d : LinearMap.ker (bottUnionRestriction cs i l U) :=
    ⟨bottSetProjection cs l (simpleUnion cs i U) n,hnU⟩
  refine ⟨Twist.mk d,?_⟩
  change bottSetSecond cs i l U z.val=Twist.mk (bottSetProjection cs l (simplePull cs i U) n)
  exact ((congrArg (bottSetSecond cs i l U) hm).symm.trans
    (bottSetSecond_project cs i l U m)).trans (congrArg Twist.mk hnq.symm)

 theorem bottCommon_range_of_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (z : bottCommonKernel cs i l U)
    (m : BottSamelsonModule cs (i::l)) (hm : bottSetProjection cs (i::l) U m=z.val)
    (hmJ : bottSetProjection cs (i::l) (simpleInter cs i U) m=0)
    (hmp : bottSetProjection cs l U (bottHeadTail cs i l m)=0) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  exact bottCommon_range_of_patch cs i l U z m hm _
    (bottCommon_patch_lift cs i l H U hU m hmJ hmp).choose_spec.1
    (bottCommon_patch_lift cs i l H U hU m hmJ hmp).choose_spec.2

 theorem bottCommon_range_forward (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (z : bottCommonKernel cs i l U) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d :=
  bottCommon_range_of_lift cs i l H U hU z _ (bottCommon_lift cs i l U z).choose_spec.1
    (bottCommon_lift cs i l U z).choose_spec.2.1
    (bottCommon_lift cs i l U z).choose_spec.2.2

 theorem bottCommon_range_backward (i : I) (l : List I) (U : Set W)
    (d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (LinearMap.ker (bottUnionRestriction cs i l U))) :
    ∃ z : bottCommonKernel cs i l U,
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  let n : BottSamelsonModule cs l :=
    (bottSetProjection_surjective cs l (simpleUnion cs i U) d.val.val).choose
  have hn : bottSetProjection cs l (simpleUnion cs i U) n=d.val.val :=
    (bottSetProjection_surjective cs l (simpleUnion cs i U) d.val.val).choose_spec
  have hnU : bottSetProjection cs l U n=0 :=
    (congrArg (bottUnionRestriction cs i l U) hn).trans d.val.property
  let z : bottCommonKernel cs i l U :=
    ⟨bottSetProjection cs (i::l) U (bottSeed cs i l n),
      bottSeed_zero_inter cs i l U n hnU,(bottSetFirst_seed cs i l U n).trans hnU⟩
  refine ⟨z,?_⟩
  exact (bottSetSecond_seed cs i l U n).trans
    (congrArg Twist.mk (congrArg (bottUnionPullRestriction cs i l U) hn))

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottInter_first_zero (i : I) (l : List I) (U : Set W)
    (z : bottSetImage cs (i::l) U) (hz : bottInterRestriction cs i (i::l) U z=0) :
    bottInterRestriction cs i l U (bottSetFirst cs i l U z)=0 :=
  (bottSetFirst_restrict cs i l (fun _ h => h.1) z).symm.trans
    ((congrArg (bottSetFirst cs i l (simpleInter cs i U)) hz).trans (map_zero _))

 theorem bottInterKernelFirst_surjective (i : I) (l : List I) (U : Set W) :
    Function.Surjective (onKernel (bottInterRestriction cs i (i::l) U) (bottSetFirst cs i l U)
      (bottInterRestriction cs i l U) (bottInter_first_zero cs i l U)) := by
  intro z
  let n : BottSamelsonModule cs l := (bottSetProjection_surjective cs l U z.val).choose
  have hn : bottSetProjection cs l U n=z.val := (bottSetProjection_surjective cs l U z.val).choose_spec
  have hnJ : bottSetProjection cs l (simpleInter cs i U) n=0 :=
    (congrArg (bottInterRestriction cs i l U) hn).trans z.property
  let w : LinearMap.ker (bottInterRestriction cs i (i::l) U) :=
    ⟨bottSetProjection cs (i::l) U (bottSeed cs i l n),
      bottSeed_zero_stable cs i l (simpleInter cs i U) (simpleInter_stable cs i U) n hnJ⟩
  exact ⟨w,Subtype.ext ((bottSetFirst_seed cs i l U n).trans hn)⟩

 theorem bottCommon_projective (i : I) (l : List I) (HP : BottProjectiveUpper cs l)
    (HF : BottFlabby cs l) (U : Set W) (hU : BruhatUpper cs U) :
    Module.Projective (SymmetricCoefficient (M := M)) (bottCommonKernel cs i l U) := by
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := HP U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l (simpleUnion cs i U)) :=
    HP (simpleUnion cs i U) (hU.simpleUnion cs U i)
  let : Module.Projective (SymmetricCoefficient (M := M)) (LinearMap.ker (bottUnionRestriction cs i l U)) :=
    kernel_projective (bottUnionRestriction cs i l U) (bottSetRestrict_surjective cs l (fun _ h => Or.inl h))
  let : Module.Projective (SymmetricCoefficient (M := M))
      (Twist (coefficientAction cs (cs.simple i)).toRingEquiv (LinearMap.ker (bottUnionRestriction cs i l U))) :=
    Twist.projective _
  exact projective_of_coordinates (bottCommonSecond cs i l U) (bottCommonSecond_injective cs i l U)
    (twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U))
    (twistMap_injective _ _ (bottUnionKernelSecond_injective cs i l U))
    (bottCommon_range_forward cs i l HF U hU) (bottCommon_range_backward cs i l U)

 theorem bottProjectiveUpper_cons (i : I) (l : List I) (HP : BottProjectiveUpper cs l)
    (HF : BottFlabby cs l) : BottProjectiveUpper cs (i::l) := by
  intro U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := HP U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l (simpleInter cs i U)) :=
    HP (simpleInter cs i U) (hU.simpleInter cs U i)
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) (simpleInter cs i U)) :=
    bottStableUpper_projective cs i l (simpleInter cs i U) (simpleInter_stable cs i U)
  let : Module.Projective (SymmetricCoefficient (M := M)) (LinearMap.ker (bottInterRestriction cs i l U)) :=
    kernel_projective (bottInterRestriction cs i l U) (bottSetRestrict_surjective cs l (fun _ h => h.1))
  let : Module.Projective (SymmetricCoefficient (M := M))
      ↥(LinearMap.ker (bottInterRestriction cs i (i::l) U) ⊓ LinearMap.ker (bottSetFirst cs i l U)) :=
    bottCommon_projective cs i l HP HF U hU
  exact projective_of_two_stage (bottInterRestriction cs i (i::l) U) (bottSetFirst cs i l U)
    (bottInterRestriction cs i l U) (bottInter_first_zero cs i l U)
    (bottSetRestrict_surjective cs (i::l) (fun _ h => h.1)) (bottInterKernelFirst_surjective cs i l U)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSetProjection_nil_injective (U : Set W) (hU : (1 : W)∈U) :
    Function.Injective (bottSetProjection cs [] U) := by
  intro m n h
  apply bottEvaluation_injective cs []
  funext e
  exact congrArg (fun z : bottSetImage cs [] U => (z.val ⟨1,hU⟩).val ⟨e,rfl⟩) h

 theorem bottSetImage_nil_subsingleton (U : Set W) (hU : (1 : W)∉U) :
    Subsingleton (bottSetImage cs [] U) := by
  constructor
  intro p q
  apply Subtype.ext
  funext x
  have hx : x.val≠1 := fun h => hU (h ▸ x.property)
  let := bottStalk_nil_subsingleton cs x.val hx
  exact Subsingleton.elim _ _

 theorem bottSetImage_nil_projective (U : Set W) :
    Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs [] U) := by
  by_cases hU : (1 : W)∈U
  · exact Module.Projective.of_equiv (LinearEquiv.ofBijective (bottSetProjection cs [] U)
      ⟨bottSetProjection_nil_injective cs U hU,bottSetProjection_surjective cs [] U⟩)
  · let := bottSetImage_nil_subsingleton cs U hU
    infer_instance

 theorem bottProjectiveUpper (l : List I) : BottProjectiveUpper cs l := by
  induction l with
  | nil => exact fun U _ => bottSetImage_nil_projective cs U
  | cons i l ih => exact bottProjectiveUpper_cons cs i l ih (bottFlabby_of_projective cs l ih)

 theorem bottFlabby (l : List I) : BottFlabby cs l :=
  bottFlabby_of_projective cs l (bottProjectiveUpper cs l)

end
end KLInvariance.TitsSpace
end

end OAI
