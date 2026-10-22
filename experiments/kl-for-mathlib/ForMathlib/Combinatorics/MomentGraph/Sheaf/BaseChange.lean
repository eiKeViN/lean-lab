import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange. Source spans: MinimalExtensions:15, MinimalExtensions:17, MinimalExtensions:16.
See migration.json and MIGRATION.md for exact provenance.
Scalar extension of sheaves and their sections, flat base change of flabbiness and vertex/edge properties. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

noncomputable def baseChange : Sheaf (R := S) G where
  vertex x := ModuleCat.of S (S ⊗[R] B.vertex x)
  edge e := ModuleCat.of S (S ⊗[R] B.edge e)
  lower e := AlgebraTensorModule.lTensor S S (B.lower e)
  upper e := AlgebraTensorModule.lTensor S S (B.upper e)

noncomputable def tensorAssignments : S ⊗[R] B.Assignment →ₗ[S] (B.baseChange S).Assignment :=
  TensorProduct.piRightHom R S S (fun x => B.vertex x)

@[simp] theorem tensorAssignments_tmul (s : S) (f : B.Assignment) (x : V) :
    B.tensorAssignments S (s ⊗ₜ f) x = s ⊗ₜ f x := rfl

lemma baseChange_tmul_compatible (Ω : Set V) (s : S) (f : B.Assignment)
    (hf : B.CompatibleOn Ω f) : (B.baseChange S).CompatibleOn Ω (fun x => s ⊗ₜ f x) := by
  intro e hs ht
  change s ⊗ₜ[R] B.lower e (f (G.source e)) = s ⊗ₜ[R] B.upper e (f (G.target e))
  rw [hf e hs ht]

noncomputable def tensorSections (Ω : Set V) :
    S ⊗[R] B.sections Ω →ₗ[S] (B.baseChange S).sections Ω :=
  ((B.tensorAssignments S).comp (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype)).codRestrict
    ((B.baseChange S).sections Ω) (by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul s f => exact B.baseChange_tmul_compatible S Ω s f.val f.property
      | add z t hz ht => simpa only [map_add] using Submodule.add_mem _ hz ht)

@[simp] theorem tensorSections_tmul (Ω : Set V) (s : S) (f : B.sections Ω) (x : V) :
    (B.tensorSections S Ω (s ⊗ₜ f)).val x = s ⊗ₜ f.val x := rfl

theorem baseChange_generated (h : B.Generated) : (B.baseChange S).Generated := by
  intro x v
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    obtain ⟨f,hf,hx⟩ := h x v
    exact ⟨fun y => s ⊗ₜ f y,B.baseChange_tmul_compatible S Set.univ s f hf,congrArg (fun v => s ⊗ₜ[R] v) hx⟩
  | add v w hv hw =>
    obtain ⟨f,hf,hfv⟩ := hv
    obtain ⟨g,hg,hgw⟩ := hw
    exact ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,congrArg₂ (·+·) hfv hgw⟩

/-- The finite section constraint whose kernel is the actual section module. -/
noncomputable def constraint (Ω : Set V) : B.Assignment →ₗ[R]
    (∀ e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω}, B.edge e.val) :=
  LinearMap.pi (fun e => (B.lower e.val).comp (LinearMap.proj (G.source e.val)) -
    (B.upper e.val).comp (LinearMap.proj (G.target e.val)))

lemma ker_constraint (Ω : Set V) : LinearMap.ker (B.constraint Ω) = B.sections Ω := by
  ext f
  constructor
  · intro h e hs ht
    have hh := congrFun (LinearMap.mem_ker.mp h) ⟨e,hs,ht⟩
    exact sub_eq_zero.mp hh
  · intro h
    apply LinearMap.mem_ker.mpr
    funext e
    exact sub_eq_zero.mpr (h e.val e.property.1 e.property.2)

end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)
noncomputable section

 theorem tensorAssignments_bijective [Finite V] : Function.Bijective (B.tensorAssignments S) := by
  classical
  let := Fintype.ofFinite V
  exact (TensorProduct.piRight R S S (fun x => B.vertex x)).bijective

 theorem constraint_tensorAssignments (Ω : Set V) (z : S ⊗[R] B.Assignment) :
    (B.baseChange S).constraint Ω (B.tensorAssignments S z) =
      TensorProduct.piRightHom R S S (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} =>
        B.edge e.val) (AlgebraTensorModule.lTensor S S (B.constraint Ω) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    ext e
    change s ⊗ₜ[R] B.lower e.val (f (G.source e.val)) -
      s ⊗ₜ[R] B.upper e.val (f (G.target e.val)) =
      s ⊗ₜ[R] (B.lower e.val (f (G.source e.val)) -
        B.upper e.val (f (G.target e.val)))
    exact (tmul_sub _ _ _).symm
  | add z w hz hw => simp only [map_add,hz,hw]; rfl

/-- The tensored finite section constraint vanishes exactly on compatible
tensored assignments. This uses the finite edge product comparison, without
flatness or a finite vertex set. -/
theorem tensorAssignments_mem_sections_iff [Finite E] (Ω : Set V)
    (z : S ⊗[R] B.Assignment) :
    B.tensorAssignments S z ∈ (B.baseChange S).sections Ω ↔
      AlgebraTensorModule.lTensor S S (B.constraint Ω) z = 0 := by
  classical
  let := Fintype.ofFinite E
  rw [← (B.baseChange S).ker_constraint Ω,LinearMap.mem_ker,B.constraint_tensorAssignments S]
  exact (TensorProduct.piRight R S S
    (fun e : {e : E // G.source e ∈ Ω ∧ G.target e ∈ Ω} => B.edge e.val)).map_eq_zero_iff

 theorem tensorSections_surjective [Finite V] [Finite E] [Module.Flat R S] (Ω : Set V) :
    Function.Surjective (B.tensorSections S Ω) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  intro f
  obtain ⟨z,hz⟩ := (B.tensorAssignments_bijective S).2 f.val
  have he := (B.tensorAssignments_mem_sections_iff S Ω z).mp (by rw [hz]; exact f.property)
  have hex : Function.Exact (B.sections Ω).subtype (B.constraint Ω) := by
    rw [← B.ker_constraint Ω]
    exact (B.constraint Ω).exact_subtype_ker_map
  obtain ⟨w,hw⟩ := (Module.Flat.lTensor_exact S hex z).mp he
  refine ⟨w,?_⟩
  apply Subtype.ext
  change B.tensorAssignments S (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype w) = _
  exact (congrArg (B.tensorAssignments S) hw).trans hz

 theorem tensorSections_injective [Finite V] [Module.Flat R S] (Ω : Set V) :
    Function.Injective (B.tensorSections S Ω) := by
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (B.sections Ω).subtype (B.sections Ω).injective_subtype
  apply (B.tensorAssignments_bijective S).1
  exact congrArg Subtype.val h

/-- Sections over every vertex subset commute with flat extension of scalars
for a finite moment graph. No freeness or BMP character input is used. -/
 def tensorSectionsEquiv [Finite V] [Finite E] [Module.Flat R S] (Ω : Set V) :
    S ⊗[R] B.sections Ω ≃ₗ[S] (B.baseChange S).sections Ω :=
  LinearEquiv.ofBijective (B.tensorSections S Ω)
    ⟨B.tensorSections_injective S Ω,B.tensorSections_surjective S Ω⟩

/-- A section already represented as a tensor of sections extends globally
when the original sheaf is flabby. Finiteness and flatness are needed to represent
arbitrary sections, not for this extension of a given tensor. -/
theorem tensorSection_extend (hb : B.Flabby) (Ω : Set V) (hΩ : IsUpperSet Ω)
    (z : S ⊗[R] B.sections Ω) :
    ∃ g : (B.baseChange S).Assignment, (B.baseChange S).IsGlobal g ∧
      ∀ x ∈ Ω, g x = (B.tensorSections S Ω z).val x := by
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    obtain ⟨g,hg,hgf⟩ := hb Ω hΩ f.val f.property
    refine ⟨fun x => s ⊗ₜ g x,B.baseChange_tmul_compatible S Set.univ s g hg,?_⟩
    intro x hx
    change s ⊗ₜ[R] g x = s ⊗ₜ[R] f.val x
    rw [hgf x hx]
  | add z w hz hw =>
    obtain ⟨f,hf,hfz⟩ := hz
    obtain ⟨g,hg,hgw⟩ := hw
    refine ⟨f+g,Submodule.add_mem ((B.baseChange S).sections Set.univ) hf hg,?_⟩
    intro x hx
    simp only [map_add,Submodule.coe_add,Pi.add_apply]
    rw [hfz x hx,hgw x hx]

 theorem baseChange_flabby [Finite V] [Finite E] [Module.Flat R S]
    (hb : B.Flabby) : (B.baseChange S).Flabby := by
  intro Ω hΩ f hf
  obtain ⟨z,hz⟩ := B.tensorSections_surjective S Ω ⟨f,hf⟩
  suffices ∃ g : (B.baseChange S).Assignment, (B.baseChange S).IsGlobal g ∧
      ∀ x ∈ Ω, g x = (B.tensorSections S Ω z).val x by
    simpa only [hz] using this
  exact B.tensorSection_extend S hb Ω hΩ z

end
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem baseChange_vertex_free (x : V) [Module.Free R (B.vertex x)] :
    Module.Free S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Free S (S ⊗[R] B.vertex x))

 theorem baseChange_vertex_finite (x : V) [Module.Finite R (B.vertex x)] :
    Module.Finite S ((B.baseChange S).vertex x) :=
  inferInstanceAs (Module.Finite S (S ⊗[R] B.vertex x))

/-- The upper quotient condition is the exact scalar-kernel sequence at an
edge. This presents the original module relation before any extension of scalars
or flatness argument. -/
theorem upperQuotient_exact (α : E → R) (h : B.UpperQuotient α) (e : E) :
    Function.Exact (DistribSMul.toLinearMap R (B.vertex (G.target e)) (α e)) (B.upper e) := by
  intro v
  exact ((h e).2 v).trans (by simp only [Set.mem_range, DistribSMul.toLinearMap_apply,eq_comm])

 theorem baseChange_upperQuotient [Module.Flat R S] (α : E → R)
    (h : B.UpperQuotient α) : (B.baseChange S).UpperQuotient (fun e => algebraMap R S (α e)) := by
  intro e
  refine ⟨LinearMap.lTensor_surjective S (h e).1, ?_⟩
  have hs := B.upperQuotient_exact α h e
  have ht := Module.Flat.lTensor_exact S hs
  intro v
  change (B.upper e).lTensor S v = 0 ↔ ∃ w, v = algebraMap R S (α e) • w
  rw [ht v, LinearMap.lTensor_smul_action]
  change (∃ w : S ⊗[R] B.vertex (G.target e), α e • w = v) ↔
    ∃ w : S ⊗[R] B.vertex (G.target e), v = algebraMap R S (α e) • w
  simp only [IsScalarTower.algebraMap_smul]
  constructor <;> rintro ⟨w,hw⟩ <;> exact ⟨w,hw.symm⟩

end KLInvariance.MomentGraph.Sheaf
end

end OAI
