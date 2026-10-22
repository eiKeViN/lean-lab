module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.Generators

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.FinitePieces. Source spans: BottSamelson:25.
See migration.json and MIGRATION.md for exact provenance.
Finiteness of graded pieces under submodules and finite dependent products. -/

namespace OAI

section
namespace KLInvariance.Graded
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

 @[expose] instance subPiece_finite (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (n : ℤ)
    [Module.Finite k (𝓜 n)] : Module.Finite k (subPiece 𝓜 S n) := by
  let f : subPiece 𝓜 S n →ₗ[k] 𝓜 n :=
    { toFun := fun v => ⟨v.val.val,v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : 𝓜 n => z.val) h

 variable {ι : Type ui} [Finite ι] {P : ι → Type um}
   [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]

 @[expose] instance piPiece_finite (𝓟 : ∀ i, ℤ → Submodule k (P i)) (n : ℤ)
    [∀ i, Module.Finite k (𝓟 i n)] : Module.Finite k (piPiece 𝓟 n) := by
  let f : piPiece 𝓟 n →ₗ[k] (∀ i, 𝓟 i n) :=
    { toFun := fun v i => ⟨v.val i,v.property i (Set.mem_univ i)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

end KLInvariance.Graded
end

end OAI
