import Mathlib
import ForMathlib.Combinatorics.DirectedPaths.Basic

/-! Semantic home: ForMathlib.Combinatorics.DirectedPaths.ScalarMap. Source spans: EdgeLocalization:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SchedulePaths
universe u v w w'
variable {V : Type u} {E : Type v} {R : Type w} {S : Type w'}
  [Semiring R] [Semiring S] (source target : E → V)
noncomputable section
local instance _root_.OAI.KLInvariance.SchedulePaths.instDecidable_oAI_5 (p : Prop) : Decidable p := Classical.propDecidable p

 theorem dispatch_map (f : R →+* S) (T : R) (v : V → R) (p : List E) (x : V) :
    f (dispatch source target T v p x) =
      dispatch source target (f T) (fun z => f (v z)) p x := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,step,map_add]
    split_ifs <;> simp only [map_mul,map_zero,ih]

end
end KLInvariance.SchedulePaths
end

end OAI
