module
public import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
public section
open OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {M N : ModuleData.{uk,ua,um} 𝓐}
  (f : ModuleData.Hom M N) (C : ModuleData.MinimalCover (ModuleData.range f))
@[expose] noncomputable def genericAttach : ModuleData.Hom C.source N :=
  (ModuleData.subtype N _
    (range_homogeneous M.piece N.piece f.map 0 (by simpa using f.graded))).comp C.hom
