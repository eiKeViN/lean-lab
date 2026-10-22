module
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Cover

public section

/-! Semantic home: ForMathlib.Order.Interval.Diamonds. Source spans: ReflectionSchedules:18.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe u

/-- The entirely unlabelled closure used in graph reconstruction. Its
completeness for Bruhat graphs is a separate obligation; this definition
neither changes Bruhat order nor defines the R/KL polynomials. -/
inductive DiamondEdges {X : Type u} [PartialOrder X] : X → X → Prop
  | cover {x y : X} : x ⋖ y → DiamondEdges x y
  | diamond {x a b c d z : X} :
      DiamondEdges x a → DiamondEdges x b →
      DiamondEdges a c → DiamondEdges a d →
      DiamondEdges b c → DiamondEdges b d →
      DiamondEdges c z → DiamondEdges d z →
      a ≠ b → c ≠ d → DiamondEdges x z

 theorem DiamondEdges.map {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    (e : X ≃o Y) {x y : X} (h : DiamondEdges x y) : DiamondEdges (e x) (e y) := by
  induction h with
  | cover h => exact DiamondEdges.cover ((apply_covBy_apply_iff e).mpr h)
  | diamond _ _ _ _ _ _ _ _ hab hcd hxa hxb hac had hbc hbd hcz hdz =>
    exact DiamondEdges.diamond hxa hxb hac had hbc hbd hcz hdz
      (fun he => hab (e.injective he)) (fun he => hcd (e.injective he))

 theorem DiamondEdges.map_iff {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    (e : X ≃o Y) {x y : X} : DiamondEdges (e x) (e y) ↔ DiamondEdges x y := by
  constructor
  · intro h
    simpa only [OrderIso.symm_apply_apply] using h.map e.symm
  · exact DiamondEdges.map e

end KLInvariance
end

end OAI
