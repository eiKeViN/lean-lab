module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel
public import ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Bruhat.PlaneModel. Source spans: DihedralIntervals:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 @[expose] def modelLabel (b : planeSubgroup M cs P) (e : Edge B.system 1 b) : MvPolynomial σ ℝ :=
  Dihedral.inducedLabel B.system cs (planeSubgroup M cs P).subtype
    (fun t => (B.reflection_iff t).mp) basis b e

 theorem model_flabby (b : planeSubgroup M cs P) [Fintype (Edge B.system 1 b)]
    [DecidableEq (Interval B.system 1 b)] (c : Interval B.system 1 b) :
    (structureSheaf (graph B.system 1 b) (B.modelLabel basis b) c).Flabby :=
  Dihedral.model_flabby B.system cs (planeSubgroup M cs P).subtype
    (fun t => (B.reflection_iff t).mp) basis b Subtype.val_injective c

 theorem model_generated (b : planeSubgroup M cs P) (c : Interval B.system 1 b) :
    (structureSheaf (graph B.system 1 b) (B.modelLabel basis b) c).Generated :=
  structureSheaf_generated _ _ _

 theorem model_quotient (b : planeSubgroup M cs P) (c : Interval B.system 1 b) :
    (structureSheaf (graph B.system 1 b) (B.modelLabel basis b) c).UpperQuotient
      (B.modelLabel basis b) := structureSheaf_upperQuotient _ _ _

end
end KLInvariance.TitsSpace.PlaneBasis
end

end OAI
