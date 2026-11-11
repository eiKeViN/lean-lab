import QEC.Coding.HypergraphProduct.Parameters

/-!
# The actual binary hypergraph-product model

Source: `source.md`, A. All constructions are aliases of the frozen QECert
hypergraph product. In particular the logical spaces are actual quotients of
cycle submodules by the check-row submodules, rather than numerical parameters.
-/

noncomputable section

namespace Paper.HGP

open QEC.Coding

universe u

/-- The two input binary parity-check matrices of source A. -/
abbrev Data (R₁ C₁ R₂ C₂ : Type u) :=
  QEC.Coding.HypergraphProduct.Data (ZMod 2) R₁ C₁ R₂ C₂

/-- Physical qubits: variable-variable and check-check coordinates, source A. -/
abbrev QubitIndex (R₁ C₁ R₂ C₂ : Type u) :=
  QEC.Coding.HypergraphProduct.QubitIndex R₁ C₁ R₂ C₂

variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- The X check `P` of source A, with its literal binary block entries. -/
abbrev xCheck (H : Data R₁ C₁ R₂ C₂) :
    Matrix (R₁ × C₂) (QubitIndex R₁ C₁ R₂ C₂) (ZMod 2) :=
  QEC.Coding.HypergraphProduct.boundary1Matrix H

/-- The Z check `D` of source A, whose transpose is the second boundary. -/
abbrev zCheck (H : Data R₁ C₁ R₂ C₂) :
    Matrix (C₁ × R₂) (QubitIndex R₁ C₁ R₂ C₂) (ZMod 2) :=
  (QEC.Coding.HypergraphProduct.boundary2Matrix H).transpose

/-- The chain complex of the same two actual checks, source A. -/
abbrev complex (H : Data R₁ C₁ R₂ C₂) :=
  QEC.Coding.HypergraphProduct.chainComplex H

/-- Z logical classes: the actual quotient `ker P / row D`, source A. -/
abbrev zLogical (H : Data R₁ C₁ R₂ C₂) := (complex H).middleHomology

/-- X logical classes: the actual quotient `ker D / row P`, source A. -/
abbrev xLogical (H : Data R₁ C₁ R₂ C₂) := (complex H).middleCohomology

/-- The first input kernel code `K₁`, source A. -/
abbrev firstKernel (H : Data R₁ C₁ R₂ C₂) :=
  QEC.Coding.HypergraphProduct.firstCode H

/-- The second input kernel code `K₂`, source A. -/
abbrev secondKernel (H : Data R₁ C₁ R₂ C₂) :=
  QEC.Coding.HypergraphProduct.secondCode H

/-- The first transposed input kernel code `T₁`, source A. -/
abbrev firstTransposeKernel (H : Data R₁ C₁ R₂ C₂) :=
  QEC.Coding.HypergraphProduct.firstTransposeCode H

/-- The second transposed input kernel code `T₂`, source A. -/
abbrev secondTransposeKernel (H : Data R₁ C₁ R₂ C₂) :=
  QEC.Coding.HypergraphProduct.secondTransposeCode H

end Paper.HGP
