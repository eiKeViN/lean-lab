import Mathlib
import ForMathlib.GroupTheory.Coxeter.Bruhat.Basic

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Bruhat.Transport. Source spans: Dihedral:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance

universe u₁ v₁ u₂ v₂
variable {B : Type u₁} {W : Type v₁} [Group W] {M : CoxeterMatrix B}
variable {B' : Type u₂} {W' : Type v₂} [Group W'] {M' : CoxeterMatrix B'}

/-- Restriction of the actual interval isomorphism to any subinterval. This
is the same unlabeled map, not a new isomorphism with extra structure. -/
def intervalIso_restrict (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (ι : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    Interval cs x.val y.val ≃o Interval cs' (ι x).val (ι y).val where
  toFun z :=
    let zI : Interval cs u b := ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
      bruhat_trans cs z.property.2 y.property.2⟩
    ⟨(ι zI).val, ι.monotone (show x ≤ zI from z.property.1),
      ι.monotone (show zI ≤ y from z.property.2)⟩
  invFun z :=
    let zI : Interval cs' u' b' := ⟨z.val,
      bruhat_trans cs' (ι x).property.1 z.property.1,
      bruhat_trans cs' z.property.2 (ι y).property.2⟩
    ⟨(ι.symm zI).val,
      by
        change x ≤ ι.symm zI
        simpa only [OrderIso.symm_apply_apply] using
          ι.symm.monotone (show ι x ≤ zI from z.property.1),
      by
        change ι.symm zI ≤ y
        simpa only [OrderIso.symm_apply_apply] using
          ι.symm.monotone (show zI ≤ ι y from z.property.2)⟩
  left_inv z := by
    apply Subtype.ext
    let zI : Interval cs u b := ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
      bruhat_trans cs z.property.2 y.property.2⟩
    change (ι.symm (ι zI)).val = zI.val
    rw [ι.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    let zI : Interval cs' u' b' := ⟨z.val,
      bruhat_trans cs' (ι x).property.1 z.property.1,
      bruhat_trans cs' z.property.2 (ι y).property.2⟩
    change (ι (ι.symm zI)).val = zI.val
    rw [ι.apply_symm_apply]
  map_rel_iff' := by
    intro z w
    exact ι.map_rel_iff

@[simp] theorem intervalIso_restrict_val (cs : CoxeterSystem M W)
    (cs' : CoxeterSystem M' W') {u b : W} {u' b' : W'}
    (ι : Interval cs u b ≃o Interval cs' u' b') (x y : Interval cs u b)
    (z : Interval cs x.val y.val) :
    (intervalIso_restrict cs cs' ι x y z).val =
      (ι ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
        bruhat_trans cs z.property.2 y.property.2⟩).val := rfl

end KLInvariance
end

end OAI
