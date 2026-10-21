import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Products

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Models. Source spans: CharacterReciprocity:6, CharacterReciprocity:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {V : Type v} [PartialOrder V] {E : Type w} {G : OrderedGraph V E}


instance zeroVertex_subsingleton (x : V) : Subsingleton ((zero (R := R) (G := G)).vertex x) :=
  inferInstanceAs (Subsingleton PUnit)

instance zeroEdge_subsingleton (e : E) : Subsingleton ((zero (R := R) (G := G)).edge e) :=
  inferInstanceAs (Subsingleton PUnit)

structure LocalModels (α : E → R) where
  sheaf : V → Sheaf.{u,v,w,z} (R := R) G
  free : ∀ c x, Module.Free R ((sheaf c).vertex x)
  finite : ∀ c x, Module.Finite R ((sheaf c).vertex x)
  quotient : ∀ c, (sheaf c).UpperQuotient α
  generated : ∀ c, (sheaf c).Generated
  flabby : ∀ c, (sheaf c).Flabby
  support : ∀ c x, ¬x ≤ c → Subsingleton ((sheaf c).vertex x)
  top : ∀ c, (sheaf c).vertex c ≃ₗ[R] R
  minimal : ∀ c x, x ≠ c → LinearMap.ker ((sheaf c).stalkMap x) ≤
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R ((sheaf c).vertex x))

inductive ModelSum (O : V → Sheaf.{u,v,w,z} (R := R) G) (U : Set V) :
    Sheaf.{u,v,w,z} (R := R) G → Prop where
  | zero : ModelSum O U zero
  | add {B} : ModelSum O U B → ∀ c ∈ U, ∀ n : ℕ,
      ModelSum O U (prod B (pi (fun _ : Fin n => O c)))

namespace ModelSum
variable {α : E → R} (O : LocalModels.{u,v,w,z} (G := G) α)
  {U : Set V} {B : Sheaf.{u,v,w,z} (R := R) G}

omit [IsLocalRing R] in
lemma mono {O : V → Sheaf.{u,v,w,z} (R := R) G} (h : ModelSum O U B)
    {T : Set V} (hUT : U ⊆ T) : ModelSum O T B := by
  induction h with
  | zero => exact .zero
  | add _ c hc n ih => exact .add ih c (hUT hc) n

lemma free (h : ModelSum O.sheaf U B) (x : V) : Module.Free R (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Free R PUnit.{z+1})
  | @add C _ c _ n ih =>
    let _ : Module.Free R (C.vertex x) := ih
    let _ := O.free c x
    change Module.Free R (C.vertex x × (Fin n → (O.sheaf c).vertex x))
    infer_instance

lemma finite (h : ModelSum O.sheaf U B) (x : V) : Module.Finite R (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Finite R PUnit.{z+1})
  | @add C _ c _ n ih =>
    let _ : Module.Finite R (C.vertex x) := ih
    let _ := O.finite c x
    change Module.Finite R (C.vertex x × (Fin n → (O.sheaf c).vertex x))
    infer_instance

lemma quotient (h : ModelSum O.sheaf U B) : B.UpperQuotient α := by
  induction h with
  | zero =>
    intro e
    exact ⟨fun v => ⟨0,Subsingleton.elim _ _⟩,fun v => ⟨fun _ => ⟨0,Subsingleton.elim _ _⟩,fun _ => Subsingleton.elim _ _⟩⟩
  | add _ c _ n ih => exact prod_upperQuotient _ _ α ih (pi_upperQuotient _ α (fun _ => O.quotient c))

lemma generated (h : ModelSum O.sheaf U B) : B.Generated := by
  induction h with
  | zero => exact fun x v => ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩
  | add _ c _ n ih => exact prod_generated _ _ ih (pi_generated _ (fun _ => O.generated c))

lemma flabby (h : ModelSum O.sheaf U B) : B.Flabby := by
  induction h with
  | zero => exact fun U _ f _ => ⟨f,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | add _ c _ n ih => exact prod_flabby _ _ ih (pi_flabby _ (fun _ => O.flabby c))

lemma minimal (h : ModelSum O.sheaf U B) (x : V) (hx : x ∉ U) :
    LinearMap.ker (B.stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (B.vertex x)) := by
  induction h with
  | zero =>
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  | add _ c hc n ih =>
    exact prod_minimal _ _ x _ ih (pi_minimal _ x _
      (fun _ => O.minimal c x (fun he => hx (he ▸ hc))))

end ModelSum
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
open scoped Pointwise
universe ur uv ue uz
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E}

/-- Equality of embedded images with a scalar on the upper image. -/
def ScaledImages (B : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) : Prop :=
  ∀ z : B.edge e,
    (∃ v ∈ B.upwardKernel (G.source e) F, B.lower e v=z) ↔
    ∃ w ∈ B.upwardKernel (G.target e) H, r • B.upper e w=z

theorem scaledImages_iff (B : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) :
    B.ScaledImages e F H r ↔
      (B.upwardKernel (G.source e) F).map (B.lower e) =
        r • (B.upwardKernel (G.target e) H).map (B.upper e) := by
  constructor
  · intro h
    ext z
    rw [Submodule.mem_smul_pointwise_iff_exists]
    change (∃ v, v ∈ B.upwardKernel (G.source e) F ∧ B.lower e v=z) ↔ _
    rw [h z]
    constructor
    · rintro ⟨w,hw,he⟩
      exact ⟨B.upper e w,⟨w,hw,rfl⟩,he⟩
    · rintro ⟨t,⟨w,hw,rfl⟩,he⟩
      exact ⟨w,hw,he⟩
  · intro h z
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hv' : B.lower e v ∈ r • (B.upwardKernel (G.target e) H).map (B.upper e) :=
        h ▸ (show B.lower e v ∈ (B.upwardKernel (G.source e) F).map (B.lower e) from ⟨v,hv,rfl⟩)
      obtain ⟨t,⟨w,hw,rfl⟩,he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv'
      exact ⟨w,hw,he⟩
    · rintro ⟨w,hw,rfl⟩
      have hw' : r • B.upper e w ∈ r • (B.upwardKernel (G.target e) H).map (B.upper e) :=
        (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨B.upper e w,⟨w,hw,rfl⟩,rfl⟩
      rw [← h] at hw'
      exact hw'

theorem prod_upwardKernel_iff (B C : Sheaf.{ur,uv,ue,uz} (R := R) G)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : (prod B C).vertex x) :
    v ∈ (prod B C).upwardKernel x F ↔
      v.1 ∈ B.upwardKernel x F ∧ v.2 ∈ C.upwardKernel x F := by
  constructor
  · intro h
    constructor
    · rintro ⟨e,heq⟩ he
      subst x
      exact congrArg Prod.fst (h ⟨e,rfl⟩ he)
    · rintro ⟨e,heq⟩ he
      subst x
      exact congrArg Prod.snd (h ⟨e,rfl⟩ he)
  · rintro ⟨hB,hC⟩ ⟨e,heq⟩ he
    subst x
    exact Prod.ext (hB ⟨e,rfl⟩ he) (hC ⟨e,rfl⟩ he)

theorem pi_upwardKernel_iff {ι : Type*} (B : ι → Sheaf.{ur,uv,ue,uz} (R := R) G)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : (pi B).vertex x) :
    v ∈ (pi B).upwardKernel x F ↔ ∀ i, v i ∈ (B i).upwardKernel x F := by
  constructor
  · rintro h i ⟨e,heq⟩ he
    subst x
    exact congrFun (h ⟨e,rfl⟩ he) i
  · rintro h ⟨e,heq⟩ he
    subst x
    exact funext (fun i => h i ⟨e,rfl⟩ he)

theorem prod_scaledImages (B C : Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hB : B.ScaledImages e F H r) (hC : C.ScaledImages e F H r) :
    (prod B C).ScaledImages e F H r := by
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' := (prod_upwardKernel_iff B C _ F v).mp hv
    obtain ⟨b,hb,hbe⟩ := (hB z.1).mp ⟨v.1,hv'.1,congrArg Prod.fst he⟩
    obtain ⟨c,hc,hce⟩ := (hC z.2).mp ⟨v.2,hv'.2,congrArg Prod.snd he⟩
    exact ⟨(b,c),(prod_upwardKernel_iff B C _ H _).mpr ⟨hb,hc⟩,Prod.ext hbe hce⟩
  · rintro ⟨v,hv,he⟩
    have hv' := (prod_upwardKernel_iff B C _ H v).mp hv
    obtain ⟨b,hb,hbe⟩ := (hB z.1).mpr ⟨v.1,hv'.1,congrArg Prod.fst he⟩
    obtain ⟨c,hc,hce⟩ := (hC z.2).mpr ⟨v.2,hv'.2,congrArg Prod.snd he⟩
    exact ⟨(b,c),(prod_upwardKernel_iff B C _ F _).mpr ⟨hb,hc⟩,Prod.ext hbe hce⟩

theorem pi_scaledImages {ι : Type*} (B : ι → Sheaf.{ur,uv,ue,uz} (R := R) G) (e : E)
    (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hB : ∀ i, (B i).ScaledImages e F H r) : (pi B).ScaledImages e F H r := by
  classical
  intro z
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' := (pi_upwardKernel_iff B _ F v).mp hv
    choose w hw hwe using fun i => (hB i (z i)).mp ⟨v i,hv' i,congrFun he i⟩
    exact ⟨w,(pi_upwardKernel_iff B _ H _).mpr hw,funext hwe⟩
  · rintro ⟨v,hv,he⟩
    have hv' := (pi_upwardKernel_iff B _ H v).mp hv
    choose w hw hwe using fun i => (hB i (z i)).mpr ⟨v i,hv' i,congrFun he i⟩
    exact ⟨w,(pi_upwardKernel_iff B _ F _).mpr hw,funext hwe⟩

theorem zero_scaledImages (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R) :
    (zero : Sheaf.{ur,uv,ue,uz} (R := R) G).ScaledImages e F H r := by
  intro z
  constructor <;> intro _ <;> exact ⟨0,Submodule.zero_mem _,Subsingleton.elim _ _⟩

theorem ModelSum.scaledImages {O : V → Sheaf.{ur,uv,ue,uz} (R := R) G}
    {U : Set V} {B : Sheaf.{ur,uv,ue,uz} (R := R) G} (h : ModelSum O U B)
    (e : E) (F : Set (Outgoing (G := G) (G.source e)))
    (H : Set (Outgoing (G := G) (G.target e))) (r : R)
    (hO : ∀ c ∈ U, (O c).ScaledImages e F H r) : B.ScaledImages e F H r := by
  induction h with
  | zero => exact zero_scaledImages e F H r
  | add _ c hc n ih =>
    exact prod_scaledImages _ _ e F H r ih
      (pi_scaledImages (fun _ : Fin n => O c) e F H r (fun _ => hO c hc))

end KLInvariance.MomentGraph.Sheaf
end

end OAI
