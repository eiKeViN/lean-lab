import QEC.Coding.HypergraphProduct.Core

/-! # The two actual source check matrices
Source: source.md A. These are the supplied HGP boundary matrices with the
second boundary transposed to index its rows by Z checks.
-/
noncomputable section
namespace Paper.HGP
open QEC.Coding.HypergraphProduct
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- Source A's X-check matrix on the two actual physical blocks. -/
abbrev xChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) := boundary1Matrix H

/-- Source A's Z-check matrix on the two actual physical blocks. -/
abbrev zChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) := (boundary2Matrix H).transpose

end Paper.HGP
