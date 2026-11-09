module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso
public import ForMathlib.Algebra.Module.Submodule.PiIdeal

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi. Source spans: GradedSheaves:10, GradedSheaves:12.
See migration.json and MIGRATION.md for exact provenance.
Dependent products of sheaves: sections, generation, flabbiness, kernels and minimality. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i}

/-- Finite direct sums represented by products, as used in the plane localization. -/
@[expose] def pi (B : ι → Sheaf.{u,v,w,z} (R := R) G) : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (∀ i, (B i).vertex x)
  edge e := ModuleCat.of R (∀ i, (B i).edge e)
  lower e := LinearMap.pi (fun i => ((B i).lower e).comp (LinearMap.proj i))
  upper e := LinearMap.pi (fun i => ((B i).upper e).comp (LinearMap.proj i))

/-- Stalk constraints of a dependent product are coordinatewise constraints. -/
@[simp] theorem pi_stalkMap_apply (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (x : V) (f : (pi B).vertex x) (e : Outgoing (G := G) x) (i : ι) :
    (pi B).stalkMap x f e i = (B i).stalkMap x (f i) e := by
  rcases e with ⟨e,he⟩
  subst x
  rfl

lemma pi_compatible (B : ι → Sheaf.{u,v,w,z} (R := R) G) (Ω : Set V)
    (f : (pi B).Assignment) :
    (pi B).CompatibleOn Ω f ↔ ∀ i, (B i).CompatibleOn Ω (fun x => f x i) := by
  constructor
  · intro h i e hs ht
    exact congrFun (h e hs ht) i
  · intro h e hs ht
    funext i
    exact h i e hs ht

lemma pi_generated (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Generated) : (pi B).Generated := by
  intro x v
  classical
  choose f hf hfx using fun i => h i x (v i)
  exact ⟨fun y i => f i y,(pi_compatible B Set.univ _).mpr hf,funext hfx⟩

lemma pi_flabby (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (h : ∀ i, (B i).Flabby) : (pi B).Flabby := by
  intro Ω hΩ f hf
  classical
  choose g hg hgf using fun i => h i Ω hΩ (fun x => f x i) ((pi_compatible B Ω f).mp hf i)
  exact ⟨fun y i => g i y,(pi_compatible B Set.univ _).mpr hg,fun x hx => funext (fun i => hgf i x hx)⟩

lemma pi_kernel_iff (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V)
    (f : (pi B).vertex x) :
    f ∈ LinearMap.ker ((pi B).stalkMap x) ↔ ∀ i, f i ∈ LinearMap.ker ((B i).stalkMap x) := by
  simp only [← upwardKernel_univ, mem_upwardKernel_iff]
  constructor
  · intro h i e he
    exact (pi_stalkMap_apply B x f e i).symm.trans (congrFun (h e he) i)
  · intro h e he
    funext i
    exact (pi_stalkMap_apply B x f e i).trans (h i e he)

end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z i
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E} {ι : Type i} [Fintype ι]

lemma pi_minimal (B : ι → Sheaf.{u,v,w,z} (R := R) G) (x : V) (I : Ideal R)
    (h : ∀ i, LinearMap.ker ((B i).stalkMap x) ≤ I • (⊤ : Submodule R ((B i).vertex x))) :
    LinearMap.ker ((pi B).stalkMap x) ≤ I • (⊤ : Submodule R ((pi B).vertex x)) := by
  intro f hf
  exact LocalCover.pi_mem_ideal_smul (fun i => (B i).vertex x) I f
    (fun i => h i ((pi_kernel_iff B x f).mp hf i))

end KLInvariance.MomentGraph.Sheaf
end

end OAI
