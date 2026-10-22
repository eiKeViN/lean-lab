module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Bruhat.Basic

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset. Source spans: Hecke:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


@[expose] noncomputable local instance _root_.OAI.KLInvariance.instDecidableEq_oAI : DecidableEq W := Classical.decEq W

/-- A concrete finite lower ideal of the genuine Bruhat order. -/
@[expose] noncomputable def lowerFinset (cs : CoxeterSystem M W) (y : W) : Finset W :=
  (finite_bruhat_lower cs y).toFinset

@[simp] theorem mem_lowerFinset (cs : CoxeterSystem M W) (y x : W) :
    x ∈ lowerFinset cs y ↔ BruhatLE cs x y := by
  classical
  exact Set.Finite.mem_toFinset _

end KLInvariance

end OAI
