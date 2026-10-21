import Mathlib
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized

/-! Semantic home: ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR. Source spans: Bruhat:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}


noncomputable def rPolynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  (klFamilies cs).1 x y

end KLInvariance

end OAI
