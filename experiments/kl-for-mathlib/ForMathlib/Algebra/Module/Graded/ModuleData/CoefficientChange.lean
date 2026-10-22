import Mathlib
import ForMathlib.Algebra.Module.Graded.ModuleData.Duality
import ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange. Source spans: CharacterReciprocity:25, CharacterReciprocity:24, CharacterReciprocity:27.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 def unchangeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom (change e he M) (change e he N)) :
    Hom M N where
  map :=
    { toFun m := (f.map (CoefficientChange.mk m)).val
      map_add' m n := congrArg CoefficientChange.val (map_add f.map (CoefficientChange.mk m) (CoefficientChange.mk n))
      map_smul' a m := by
        have hh := congrArg CoefficientChange.val (map_smul f.map (e a) (CoefficientChange.mk m))
        change (f.map (CoefficientChange.mk (e.symm (e a) • m))).val=
          e.symm (e a) • (f.map (CoefficientChange.mk m)).val at hh
        simpa only [e.symm_apply_apply, RingHom.id_apply] using hh }
  graded n m hm := (mem_changePiece e N n _).mp
    (f.graded n (CoefficientChange.mk m) ((mem_changePiece e M n _).mpr hm))

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  (hA : ∀ n<0,𝓐 n=⊥) (hB : ∀ n<0,𝓑 n=⊥)
noncomputable section

 def changeUnitHom : Hom (change e he (unit.{uk,ua,um} hA)) (unit hB) where
  map :=
    { toFun m j := e (m.val j)
      map_add' m n := funext fun j => map_add e (m.val j) (n.val j)
      map_smul' b m := by
        funext j
        change e (e.symm b * m.val j)=b * e (m.val j)
        rw [map_mul,e.apply_symm_apply] }
  graded := by
    intro n m hm j
    exact (he (n-0) _).mp ((mem_changePiece e (unit hA) n m).mp hm j)

 def changeUnitInvHom : Hom (unit.{uk,ua,um} hB) (change e he (unit hA)) where
  map :=
    { toFun m := CoefficientChange.mk (fun j => e.symm (m j))
      map_add' m n := CoefficientChange.ext (funext fun j => map_add e.symm (m j) (n j))
      map_smul' b m := by
        apply CoefficientChange.ext
        funext j
        exact map_mul e.symm b (m j) }
  graded := by
    intro n m hm
    apply (mem_changePiece e (unit hA) n _).mpr
    intro j
    apply (he (n-0) _).mpr
    change e (e.symm (m j)) ∈ 𝓑 (n-0)
    rw [e.apply_symm_apply]
    exact hm j

 theorem changeUnitHom_inv (m : unit.{uk,ua,um} hB) :
    (changeUnitHom e he hA hB).map ((changeUnitInvHom e he hA hB).map m)=m :=
  funext fun j => e.apply_symm_apply (m j)

 theorem changeUnitInvHom_hom (m : change e he (unit.{uk,ua,um} hA)) :
    (changeUnitInvHom e he hA hB).map ((changeUnitHom e he hA hB).map m)=m :=
  CoefficientChange.ext (funext fun j => e.symm_apply_apply (m.val j))

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {hA : ∀ n<0,𝓐 n=⊥} {hB : ∀ n<0,𝓑 n=⊥}
  {M : ModuleData.{uk,ua,um} 𝓐} (hM : M=unit hA)
  {N : ModuleData.{uk,ua,um} 𝓑} (hN : N=unit hB)
noncomputable section

 def changeTopInclusion : Hom N (change e he M) :=
  (changeHom e he (homOfEq hM.symm)).comp
    ((changeUnitInvHom e he hA hB).comp (homOfEq hN))

 def changeTopProjection : Hom (change e he M) N :=
  (homOfEq hN.symm).comp
    ((changeUnitHom e he hA hB).comp (changeHom e he (homOfEq hM)))

 theorem changeTop_split (n : N) :
    (changeTopProjection e he hM hN).map ((changeTopInclusion e he hM hN).map n)=n := by
  subst M
  subst N
  change (changeUnitHom e he hA hB).map ((changeUnitInvHom e he hA hB).map n)=n
  exact changeUnitHom_inv e he hA hB n

end
end KLInvariance.Graded.ModuleData
end

end OAI
