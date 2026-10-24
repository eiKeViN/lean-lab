module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection
public import ForMathlib.LinearAlgebra.Quotient.Transport

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.Range. Source spans: BalancedPairings:13, BalancedPairings:25, BalancedPairings:10.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {M N : ModuleData.{uk,ua,um} 𝓐}
noncomputable section

 @[expose] def rangeMap (e : Hom M M) (f : Hom N N) (g : Hom M N)
    (h : ∀ m, f.map (g.map m)=g.map (e.map m)) : Hom (range e) (range f) where
  map := (g.map.domRestrict e.map.range).codRestrict f.map.range (by
    rintro ⟨_,m,rfl⟩
    exact ⟨g.map m,h m⟩)
  graded n m hm := g.graded n m.val hm

 @[expose] def rangeInclusion (e : Hom M M) : Hom (range e) M where
  map := e.map.range.subtype
  graded _ _ hm := hm

 @[expose] def rangeProjection (e : Hom M M) : Hom M (range e) where
  map := e.map.rangeRestrict
  graded n m hm := e.graded n m hm

/-- The map induced on ranges agrees with the original commuting map. -/
@[simp] theorem rangeMap_val (e : Hom M M) (f : Hom N N) (g : Hom M N)
    (h : ∀ m, f.map (g.map m)=g.map (e.map m)) (v : range e) :
    ((rangeMap e f g h).map v).val = g.map v.val := by rfl

/-- The range factorization of an endomorphism retains its value. -/
@[simp] theorem rangeProjection_val (e : Hom M M) (v : M) :
    ((rangeProjection e).map v).val = e.map v := by rfl

/-- Inclusion of a range is its underlying vector. -/
@[simp] theorem rangeInclusion_apply (e : Hom M M) (v : range e) :
    (rangeInclusion e).map v = v.val := by rfl

/-- An idempotent acts as the identity on its range. -/
theorem range_fixed (e : Hom M M) (he : ∀ v, e.map (e.map v)=e.map v)
    (v : range e) : e.map v.val = v.val := by
  obtain ⟨m,hm⟩ := v.property
  rw [← hm,he]

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M N : ModuleData.{uk,ua,um} 𝓐}
 theorem Hom.eq_of_map_eq (f g : Hom M N) (h : f.map=g.map) : f=g := by
  cases f
  cases g
  cases h
  rfl
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
open PairProjection LinearDescent
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (e : Hom M M) (f : Hom M X) (g : Hom M Y)
  (hf : Function.Surjective f.map) (hg : Function.Surjective g.map)
  (hef : ∀ m, f.map m=0 → f.map (e.map m)=0)
  (heg : ∀ m, g.map m=0 → g.map (e.map m)=0)
noncomputable section

 @[expose] def descended : Hom X X where
  map := descend f.map hf e.map hef
  graded := by
    intro n x hx
    obtain ⟨m,hm,rfl⟩ := f.homogeneous_lift hf n x hx
    rw [descend_apply]
    exact f.graded n _ (e.graded n m hm)

include heg in
 theorem lower_kernel_preserved (x : X) (hx : lower f.map g.map x=0) :
    lower f.map g.map ((descended e f hf hef).map x)=0 := by
  obtain ⟨m,hm,hn⟩ := (kernel_lower f.map g.map x).mp hx
  apply (kernel_lower f.map g.map _).mpr
  refine ⟨e.map m,?_,heg m hn⟩
  rw [← hm]
  exact (descend_apply f.map hf e.map hef m).symm

 @[expose] def descendedEdge : Hom (pairEdge f g hg) (pairEdge f g hg) where
  map := descend (lower f.map g.map) (lower_surjective f.map g.map hg)
    (descended e f hf hef).map (lower_kernel_preserved e f g hf hef heg)
  graded := by
    intro n z hz
    obtain ⟨x,hx,rfl⟩ := hz
    refine ⟨(descended e f hf hef).map x,(descended e f hf hef).graded n x hx,?_⟩
    exact (descend_apply (lower f.map g.map) (lower_surjective f.map g.map hg)
      (descended e f hf hef).map (lower_kernel_preserved e f g hf hef heg) x).symm

 theorem descendedEdge_lower (x : X) :
    (descendedEdge e f g hf hg hef heg).map (lower f.map g.map x)=
      lower f.map g.map ((descended e f hf hef).map x) :=
  descend_apply _ _ _ _ x

 theorem descendedEdge_upper (y : Y) :
    (descendedEdge e f g hf hg hef heg).map (upper f.map g.map y)=
      upper f.map g.map ((descended e g hg heg).map y) := by
  obtain ⟨m,rfl⟩ := hg y
  rw [← compatible f.map g.map m,descendedEdge_lower]
  change lower f.map g.map (descend f.map hf e.map hef (f.map m)) =
    upper f.map g.map (descend g.map hg e.map heg (g.map m))
  rw [descend_apply,descend_apply]
  exact compatible f.map g.map (e.map m)

end
end KLInvariance.Graded.ModuleData
end

end OAI
