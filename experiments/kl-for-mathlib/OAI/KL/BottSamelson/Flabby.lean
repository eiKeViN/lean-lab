module
public import Mathlib
public import OAI.KL.BottSamelson.UpperSections

public section

/-! Semantic home: OAI.KL.BottSamelson.Flabby. Source spans: IntegralPairings:29.
See migration.json and MIGRATION.md for exact provenance.
From global Bott upper-section flabbiness to the projection sheaf on a finite Bruhat interval, via extension of interval assignments. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_subsingleton_of_not_bruhat (l : List I) (hl : cs.IsReduced l)
    (x : W) (hx : ¬BruhatLE cs x (cs.wordProd l)) : Subsingleton (bottStalk cs l x) := by
  constructor
  intro p q
  apply Subtype.ext
  funext e
  exact (hx (e.property ▸ bottWeight_bruhat cs l hl e.val)).elim

 @[expose] def intervalUpperClosure (b : W) (U : Set (Interval cs 1 b)) : Set W :=
  {x | ∃ a : Interval cs 1 b, a∈U ∧ BruhatLE cs a.val x}

 omit [Fintype I] in
 theorem intervalUpperClosure_upper (b : W) (U : Set (Interval cs 1 b)) :
    BruhatUpper cs (intervalUpperClosure cs b U) := by
  rintro x y hxy ⟨a,ha,hax⟩
  exact ⟨a,ha,bruhat_trans cs hax hxy⟩

 omit [Fintype I] in
 theorem intervalUpperClosure_member (b : W) (U : Set (Interval cs 1 b)) (hU : IsUpperSet U)
    (x : W) (hx : x∈intervalUpperClosure cs b U) (hxb : BruhatLE cs x b) :
    (⟨x,one_bruhat cs x,hxb⟩ : Interval cs 1 b)∈U := by
  obtain ⟨a,ha,hax⟩ := hx
  exact hU hax ha

 @[expose] def bottIntervalExtension (l : List I) (U : Set (Interval cs 1 (cs.wordProd l)))
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (x : intervalUpperClosure cs (cs.wordProd l) U) : bottStalk cs l x.val := by
  classical
  exact if h : BruhatLE cs x.val (cs.wordProd l) then f ⟨x.val,one_bruhat cs x.val,h⟩ else 0

 theorem bottIntervalExtension_apply (l : List I) (U : Set (Interval cs 1 (cs.wordProd l)))
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (x : Interval cs 1 (cs.wordProd l)) (hx : x.val∈intervalUpperClosure cs (cs.wordProd l) U) :
    bottIntervalExtension cs l U f ⟨x.val,hx⟩=f x := by
  classical
  dsimp only [bottIntervalExtension]
  exact dite_eq_left x.property.2

 theorem bottIntervalExtension_compatible (l : List I) (hl : cs.IsReduced l)
    (U : Set (Interval cs 1 (cs.wordProd l))) (hU : IsUpperSet U)
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (hf : (bottProjectionSheaf cs l 1 (cs.wordProd l)).CompatibleOn U f) :
    BottCompatible cs l (intervalUpperClosure cs (cs.wordProd l) U) (bottIntervalExtension cs l U f) := by
  intro x y hx hy hxy
  by_cases hyb : BruhatLE cs y (cs.wordProd l)
  · have hxb : BruhatLE cs x (cs.wordProd l) := bruhat_trans cs (.single hxy) hyb
    let xx : Interval cs 1 (cs.wordProd l) := ⟨x,one_bruhat cs x,hxb⟩
    let yy : Interval cs 1 (cs.wordProd l) := ⟨y,one_bruhat cs y,hyb⟩
    let e : Edge cs 1 (cs.wordProd l) := ⟨(xx,yy),hxy⟩
    have hh := hf e (intervalUpperClosure_member cs _ U hU x hx hxb)
      (intervalUpperClosure_member cs _ U hU y hy hyb)
    obtain ⟨m,hm,hn⟩ := (PairProjection.compatible_iff _ _ _ _).mp hh
    exact ⟨m,hm.trans (bottIntervalExtension_apply cs l U f xx hx).symm,
      hn.trans (bottIntervalExtension_apply cs l U f yy hy).symm⟩
  · let := bottStalk_subsingleton_of_not_bruhat cs l hl y hyb
    obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x (bottIntervalExtension cs l U f ⟨x,hx⟩)
    exact ⟨m,hm,Subsingleton.elim _ _⟩

 theorem bottProjectionSheaf_flabby (l : List I) (hl : cs.IsReduced l) :
    (bottProjectionSheaf cs l 1 (cs.wordProd l)).Flabby := by
  intro U hU f hf
  obtain ⟨m,hm⟩ := bottFlabby cs l _ (intervalUpperClosure_upper cs _ U)
    (bottIntervalExtension cs l U f) (bottIntervalExtension_compatible cs l hl U hU f hf)
  refine ⟨(bottSection cs l 1 (cs.wordProd l) m).val,(bottSection cs l 1 (cs.wordProd l) m).property,?_⟩
  intro x hx
  exact (congrFun hm ⟨x.val,x,hx,bruhat_refl cs x.val⟩).trans
    (bottIntervalExtension_apply cs l U f x ⟨x,hx,bruhat_refl cs x.val⟩)

end
end KLInvariance.TitsSpace
end

end OAI
