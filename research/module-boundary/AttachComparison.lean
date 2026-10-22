module
public import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
public section
open OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {M N : ModuleData.{uk,ua,um} 𝓐}
  (f : ModuleData.Hom M N) (C : ModuleData.MinimalCover (ModuleData.range f))
noncomputable def genericAttach : ModuleData.Hom C.source N :=
  (ModuleData.subtype N _
    (range_homogeneous _ _ f.map 0 (by simpa using f.graded))).comp C.hom

@[expose] noncomputable def explicitAttach : ModuleData.Hom C.source N :=
  (ModuleData.subtype N _
    (range_homogeneous M.piece N.piece f.map 0 (by simpa using f.graded))).comp C.hom

private theorem attach_eq : genericAttach f C = explicitAttach f C := rfl
 theorem attach_map (z : C.source) : (explicitAttach f C).map z = (C.hom.map z).val := rfl
#print axioms attach_eq
#print axioms attach_map
