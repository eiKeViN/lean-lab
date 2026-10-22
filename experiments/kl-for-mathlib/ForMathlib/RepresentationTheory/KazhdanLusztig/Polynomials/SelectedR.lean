module
public import Mathlib
public import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized

public section

/-! Semantic home: ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR. Source spans: Bruhat:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}


@[expose] noncomputable def rPolynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  (klFamilies cs).1 x y

end KLInvariance

end OAI
