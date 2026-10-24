module
public import Mathlib
public import ForMathlib.Algebra.Module.CoefficientChange.Basic
public import ForMathlib.Algebra.Module.Graded.ModuleData.Basic

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic. Source spans: BottSamelson:28.
See migration.json and MIGRATION.md for exact provenance.
Changing coefficients of graded module data and their homomorphisms through a grading-preserving algebra equivalence. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 @[expose] def changePiece (M : ModuleData.{uk,ua,um} 𝓐) : ℤ → Submodule k (CoefficientChange e M) :=
  fun n => (M.piece n).map (CoefficientChange.kEquiv e M).toLinearMap

 theorem mem_changePiece (M : ModuleData.{uk,ua,um} 𝓐) (n : ℤ) (m : CoefficientChange e M) :
    m ∈ changePiece e M n ↔ m.val ∈ M.piece n := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    change CoefficientChange.mk x=m at hxm
    exact (congrArg CoefficientChange.val hxm) ▸ hx
  · intro hm
    exact ⟨m.val,hm,rfl⟩

 @[expose] def change (M : ModuleData.{uk,ua,um} 𝓐) : ModuleData.{uk,ua,um} 𝓑 where
  obj := ModuleCat.of B (CoefficientChange e M)
  kModule := inferInstance
  tower := inferInstance
  piece := changePiece e M
  decomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    apply image_isInternal M.piece (CoefficientChange.kEquiv e M).toLinearMap
      (CoefficientChange.kEquiv e M).surjective
    intro n m hm
    have hz : m=0 := congrArg CoefficientChange.val hm
    subst m
    simp only [map_zero]
  graded := by
    constructor
    intro i j b m hb hm
    apply (mem_changePiece e M (i+j) _).mpr
    change e.symm b • m.val ∈ M.piece (i+j)
    have ha : e.symm b ∈ 𝓐 i := (he i _).mpr (by simpa using hb)
    exact SetLike.GradedSMul.smul_mem ha ((mem_changePiece e M j m).mp hm)
  nonneg n hn := by simp only [changePiece,M.nonneg n hn,Submodule.map_bot]
  finite := inferInstance

 @[expose] def changeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) :
    Hom (change e he M) (change e he N) where
  map := CoefficientChange.map e f.map
  graded n m hm := by
    apply (mem_changePiece e N n _).mpr
    exact (CoefficientChange.val_map e f.map m).symm ▸
      f.graded n m.val ((mem_changePiece e M n m).mp hm)

 theorem change_free (M : ModuleData.{uk,ua,um} 𝓐) [Module.Free A M] :
    Module.Free B (change e he M) := inferInstanceAs (Module.Free B (CoefficientChange e M))

end
end KLInvariance.Graded.ModuleData
end

end OAI
