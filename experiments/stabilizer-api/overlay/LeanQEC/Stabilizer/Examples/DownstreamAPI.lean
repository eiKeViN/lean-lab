import LeanQEC.Stabilizer.API

/-!
# Downstream use cases

These examples exercise the public import and complete workflows. In particular,
the user code never installs an algebraic instance with `letI`.
-/

noncomputable section

namespace StabilizerDownstreamExamples

variable {n k : ℕ} {ι : Type*}

-- A literal code still retains its identity in the stable carrier's type.
example (S : Subgroup (PauliGroup_group n)) (hm : negIdPauli n ∉ S)
    (a b : (StabCode.mk S hm).Stabilizer) : a * b = b * a :=
  mul_comm a b

-- The new structure adds the law while keeping all the original group data.
example (C : StabCode n) :
    (StabCode.instStabilizerCommGroup C).toGroup =
      (inferInstanceAs (Group C.stabs)) := rfl

example (C : StabCode n) (s : Finset ι) (f g : ι → C.Stabilizer) :
    (∏ i ∈ s, f i * g i) = (∏ i ∈ s, f i) * ∏ i ∈ s, g i :=
  Finset.prod_mul_distrib

-- Existing ambient elements can stay ambient.
example (C : StabCode n) (a b : PauliGroup_group n)
    (ha : a ∈ C.stabs) (hb : b ∈ C.stabs) : Commute a b :=
  C.commute_of_mem ha hb

-- Negative instance synthesis is profiled separately. A timeout is not evidence
-- that instance search completed and established absence of an instance.

-- A nonzero common fixed vector certifies the generated code directly.
example (g : ι → PauliGroup_group n) (ψ : PState n) (hψ : ψ ≠ 0)
    (hg : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) :
    ψ ∈ (StabCode.ofStabilizedGenerators g ψ hψ hg).space := by
  exact StabCode.mem_space_ofStabilizedVector _ ψ hψ
    (PauliGroup.closure_stabilizes_of_generators g ψ hg)

-- From generator coefficients all the way to an operator stabilizing a codeword.
example [Fintype ι] (C : StabCode n) (P : C.Presentation ι) (c : ι → ZMod 2)
    (ψ : PState n) (hψ : ψ ∈ C.space) :
    stabilizes (C.toUnitary (P.combination c)) ψ :=
  P.combination_stabilizes c hψ

example (C : StabCode n) (P : C.Presentation ι) (ψ : PState n)
    (h : ∀ i, stabilizes (C.toUnitary (P.generator i)) ψ) : ψ ∈ C.space :=
  (P.mem_space_iff ψ).mpr h

-- Binary lifting returns the signed code member, and the round trip simplifies.
example (C : StabCode n) (s : C.Stabilizer) :
    C.ofBinary (C.toBinary s) = s := by
  simp

example (C : StabCode n) (a b : Additive C.Stabilizer) (c : ZMod 2) :
    C.binaryLinearEquiv (c • (a + b)) =
      c • (C.binaryLinearEquiv a + C.binaryLinearEquiv b) := by
  simp

-- Check-matrix users supply their existing independent-row certificate.
example (B : BinSympMatrix k n) (hc : B.isCommuting)
    (hi : LinearIndependent (ZMod 2) B.row) (c : Fin k → ZMod 2) :
    Pauli_toBinSympPauli ((StabCode.ofIndependentRows B hc hi).toPauli
      ((B.independentPresentation hc hi).combination c)) =
      (B.X.transpose.mulVec c, B.Z.transpose.mulVec c) :=
  B.presentation_combination_binaryImage _ c

-- CSS data provides both the code and its generating family.
example {k₁ k₂ : ℕ} (css : CSS_pair n k₁ k₂) (i : Fin (k₁ + k₂)) :
    css.toStabCode.toPauli (css.presentation.generator i) ∈ css.toStabCode.stabs := by
  simp

-- Qubit relabeling transports products and the distance theorem with the code.
example (C : StabCode n) (σ : Equiv.Perm (Fin n)) (s t : C.Stabilizer) :
    C.reindexStabilizer σ (s * t) =
      C.reindexStabilizer σ s * C.reindexStabilizer σ t :=
  map_mul _ _ _

example [Fintype ι] (C : StabCode n) (P : C.Presentation ι)
    (σ : Equiv.Perm (Fin n)) (c : ι → ZMod 2) :
    (P.reindexQubits σ).combination c = C.reindexStabilizer σ (P.combination c) :=
  P.map_combination _ _ c

example (C : StabCode n) (σ : Equiv.Perm (Fin n)) (d : ℕ) (h : d ≤ C.distance) :
    d ≤ (C.reindex σ).distance := by simpa using h

-- Zero-qubit and zero-generator carriers still receive the ordinary algebraic API.
example (C : StabCode 0) : Fintype C.Stabilizer := inferInstance

def oneQubitZ : StabCode 1 :=
  cssStabCode (fun (_ : Fin 1) (_ : Fin 1) => 1)
    (fun (i : Fin 0) => Fin.elim0 i) (by intro _ j; exact Fin.elim0 j)

example (s t : oneQubitZ.Stabilizer) : s * t = t * s := mul_comm s t

end StabilizerDownstreamExamples

#print axioms PauliGroup.isMulCommutative_of_negId_not_mem
#print axioms BinSympMatrix.negId_not_mem_of_linearIndependent
#print axioms StabCode.binaryLinearEquiv
#print axioms PauliGroup.reindex
#print axioms StabCode.reindex_distance
