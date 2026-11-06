import LeanQEC.Stabilizer.Constructors

/-!
# Generating presentations and their downstream operations

The code is independent of a choice of generators. A `C.Presentation ι` keeps
that choice and its generation theorem together, and returns typed stabilizers.
-/

namespace StabCode

variable {n : ℕ}

/-- A generating family, with its relationship to the mathematical code. -/
structure Presentation (C : StabCode n) (ι : Type*) where
  generator : ι → C.Stabilizer
  generates : Subgroup.closure (Set.range (fun i => C.toPauli (generator i))) = C.stabs

/-- A family of ambient Paulis whose generated subgroup has been certified valid. -/
def ofGenerators {ι : Type*} (g : ι → PauliGroup_group n)
    (hm : negIdPauli n ∉ Subgroup.closure (Set.range g)) : StabCode n :=
  ofSubgroup (Subgroup.closure (Set.range g)) hm

/-- The chosen generators, already typed as members of the newly constructed code. -/
def ofGeneratorsPresentation {ι : Type*} (g : ι → PauliGroup_group n)
    (hm : negIdPauli n ∉ Subgroup.closure (Set.range g)) :
    (ofGenerators g hm).Presentation ι where
  generator i := (ofGenerators g hm).ofMem (g i) (Subgroup.subset_closure ⟨i, rfl⟩)
  generates := rfl

/-- Construct from generators fixing one nonzero vector; all closure proofs are internal. -/
def ofStabilizedGenerators {ι : Type*} (g : ι → PauliGroup_group n)
    (ψ : PState n) (hψ : ψ ≠ 0) (hg : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) : StabCode n :=
  ofStabilizedVector (Subgroup.closure (Set.range g)) ψ hψ
    (PauliGroup.closure_stabilizes_of_generators g ψ hg)

/-- Keep the supplied generators available after construction from a fixed vector. -/
def stabilizedPresentation {ι : Type*} (g : ι → PauliGroup_group n)
    (ψ : PState n) (hψ : ψ ≠ 0) (hg : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) :
    (ofStabilizedGenerators g ψ hψ hg).Presentation ι :=
  ofGeneratorsPresentation g (PauliGroup.negId_not_mem_of_stabilizes _ ψ hψ
    (PauliGroup.closure_stabilizes_of_generators g ψ hg))

namespace Presentation

variable {C : StabCode n} {ι : Type*}

@[simp]
theorem generator_mem (P : C.Presentation ι) (i : ι) :
    C.toPauli (P.generator i) ∈ C.stabs := C.stabilizer_mem _

/-- Form any finite product inside the commutative stabilizer carrier. -/
def prod (P : C.Presentation ι) (s : Finset ι) : C.Stabilizer :=
  ∏ i ∈ s, P.generator i

@[simp]
theorem prod_mem (P : C.Presentation ι) (s : Finset ι) :
    C.toPauli (P.prod s) ∈ C.stabs := C.stabilizer_mem _

/-- Binary coefficients select generators without exposing intermediate certificates. -/
def combination [Fintype ι] (P : C.Presentation ι) (c : ι → ZMod 2) : C.Stabilizer :=
  ∏ i, if c i = 1 then P.generator i else 1

@[simp]
theorem combination_mem [Fintype ι] (P : C.Presentation ι) (c : ι → ZMod 2) :
    C.toPauli (P.combination c) ∈ C.stabs := C.stabilizer_mem _

theorem prod_stabilizes (P : C.Presentation ι) (s : Finset ι)
    {ψ : PState n} (hψ : ψ ∈ C.space) :
    stabilizes (C.toUnitary (P.prod s)) ψ :=
  C.stabilizes_of_mem_space _ hψ

theorem combination_stabilizes [Fintype ι] (P : C.Presentation ι) (c : ι → ZMod 2)
    {ψ : PState n} (hψ : ψ ∈ C.space) :
    stabilizes (C.toUnitary (P.combination c)) ψ :=
  C.stabilizes_of_mem_space _ hψ

/-- Codespace membership is checked on the stored generating family. -/
theorem mem_space_iff (P : C.Presentation ι) (ψ : PState n) :
    ψ ∈ C.space ↔ ∀ i, stabilizes (C.toUnitary (P.generator i)) ψ := by
  rw [C.mem_space_of_closure P.generates]
  simp only [Set.forall_mem_range]
  rfl

/-- Ambient commutation only needs to be checked on these generators. -/
theorem mem_normalizer_iff (P : C.Presentation ι) (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔ ∀ i, Commute E (C.toPauli (P.generator i)) := by
  rw [C.mem_normalizerGroup_of_closure P.generates]
  constructor
  · intro h i
    exact (commute_iff_commute _ _).mp (h _ ⟨i, rfl⟩)
  · intro h s hs
    obtain ⟨i, rfl⟩ := hs
    exact (commute_iff_commute _ _).mpr (h i)

end Presentation
end StabCode

namespace BinSympMatrix

variable {n k : ℕ}

/-- A matrix row, directly available as a member of its certified code. -/
noncomputable def stabilizer (B : BinSympMatrix k n) (hm : negIdPauli n ∉ B.pauliSubgroup)
    (i : Fin k) : (StabCode.ofBinSympMatrix B hm).Stabilizer :=
  (StabCode.ofBinSympMatrix B hm).ofMem _ (B.row_mem_pauliSubgroup i)

@[simp]
theorem toPauli_stabilizer (B : BinSympMatrix k n) (hm : negIdPauli n ∉ B.pauliSubgroup)
    (i : Fin k) :
    (StabCode.ofBinSympMatrix B hm).toPauli (B.stabilizer hm i) =
      BinSympPauli_toPauli (B.row i) := rfl

/-- The matrix's generating presentation carries all row membership proofs. -/
noncomputable def presentation (B : BinSympMatrix k n) (hm : negIdPauli n ∉ B.pauliSubgroup) :
    (StabCode.ofBinSympMatrix B hm).Presentation (Fin k) where
  generator := B.stabilizer hm
  generates := by
    classical
    change Subgroup.closure (Set.range (fun i => BinSympPauli_toPauli (B.row i))) =
      B.pauliSubgroup
    unfold pauliSubgroup
    congr 1
    ext x
    simp

/-- Independent commuting rows already carry the validity proof needed by the presentation. -/
noncomputable def independentPresentation (B : BinSympMatrix k n) (hc : B.isCommuting)
    (hi : LinearIndependent (ZMod 2) B.row) :
    (StabCode.ofIndependentRows B hc hi).Presentation (Fin k) :=
  B.presentation (B.negId_not_mem_of_linearIndependent hc hi)

end BinSympMatrix
