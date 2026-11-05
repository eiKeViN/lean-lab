import LeanQEC.Stabilizer.API

/-!
# A complete consumer workflow, independent of check-matrix construction

Construct from a nonzero common fixed vector, work with redundant generators,
analyze coefficient relations with linear algebra, relabel generators and qubits,
then reuse code-distance bounds. All plumbing stays in the public API.
-/

noncomputable section

namespace PresentationWorkflow

variable {n : ℕ} {ι κ : Type*}

def code (g : ι → PauliGroup_group n) (ψ : PState n) (hψ : ψ ≠ 0)
    (hg : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) : StabCode n :=
  StabCode.ofStabilizedGenerators g ψ hψ hg

def presentation (g : ι → PauliGroup_group n) (ψ : PState n) (hψ : ψ ≠ 0)
    (hg : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) : (code g ψ hψ hg).Presentation ι :=
  StabCode.stabilizedPresentation g ψ hψ hg

example [Fintype ι] (g : ι → PauliGroup_group n) (ψ : PState n) (hψ : ψ ≠ 0)
    (hg : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) :
    Function.Surjective (presentation g ψ hψ hg).coefficientLinearMap :=
  (presentation g ψ hψ hg).coefficientLinearMap_surjective

-- This statement needs no independence assumption on the generating family.
theorem relations_dimension [Fintype ι] (C : StabCode n) (P : C.Presentation ι) :
    Module.finrank (ZMod 2) (LinearMap.ker P.coefficientLinearMap) + C.numGenerators =
      Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker P.coefficientLinearMap
  rw [P.range_coefficientLinearMap, finrank_top, C.binaryLinearEquiv.finrank_eq] at h
  simpa [StabCode.numGenerators, add_comm] using h

-- A genuine redundant family from the fixed-vector constructor.
def repeatedPresentation (s : PauliGroup_group n) (ψ : PState n) (hψ : ψ ≠ 0)
    (hs : stabilizes (s : 𝐔ₙ[n]) ψ) :=
  presentation (fun _ : Fin 2 => s) ψ hψ (fun _ => hs)

theorem repeated_relation (s : PauliGroup_group n) (ψ : PState n) (hψ : ψ ≠ 0)
    (hs : stabilizes (s : 𝐔ₙ[n]) ψ) :
    (repeatedPresentation s ψ hψ hs).coefficientLinearMap (fun _ => 1) = 0 := by
  let P := repeatedPresentation s ψ hψ hs
  have hgen : P.generator 0 = P.generator 1 := rfl
  change P.coefficientLinearMap (fun _ => 1) = 0
  simp [StabCode.Presentation.combination, Fin.prod_univ_two, hgen]

example : (fun _ : Fin 2 => (1 : ZMod 2)) ≠ 0 := by
  intro h
  have hi := congrFun h 0
  norm_num at hi

-- A relation follows the generator and qubit relabelings without reconstruction.
example [Fintype ι] [Fintype κ] (C : StabCode n) (P : C.Presentation ι)
    (e : ι ≃ κ) (σ : Equiv.Perm (Fin n)) (c : ι → ZMod 2) :
    ((P.reindex e).reindexQubits σ).combination (fun j => c (e.symm j)) =
      C.reindexStabilizer σ (P.combination c) := by
  rw [StabCode.Presentation.reindexQubits_combination, P.reindex_combination]

example [Fintype ι] (C : StabCode n) (P : C.Presentation ι)
    (e : PauliGroup_group n ≃* PauliGroup_group n)
    (he : e (negIdPauli n) = negIdPauli n) (c : ι → ZMod 2)
    (hc : c ∈ LinearMap.ker P.coefficientLinearMap) :
    c ∈ LinearMap.ker (P.map e he).coefficientLinearMap := by
  rw [LinearMap.mem_ker] at hc ⊢
  rw [P.coefficientLinearMap_map, LinearMap.comp_apply, hc, map_zero]

-- Identity, composition and undo are available at both object and presentation levels.
example (C : StabCode n) : C.reindex (Equiv.refl _) = C := by simp

example (C : StabCode n) (σ τ : Equiv.Perm (Fin n)) :
    (C.reindex σ).reindex τ = C.reindex (σ.trans τ) := by simp

example (C : StabCode n) (P : C.Presentation ι) (σ : Equiv.Perm (Fin n)) :
    ((P.reindexQubits σ).reindexQubits σ.symm).congrCode (C.reindex_symm σ) = P := by
  simp

example (C : StabCode n) (σ : Equiv.Perm (Fin n)) (s : C.Stabilizer) :
    StabCode.stabilizerCongr (C.reindex_symm σ)
      ((C.reindex σ).reindexStabilizer σ.symm (C.reindexStabilizer σ s)) = s := by
  simp

example (C : StabCode n) (σ τ : Equiv.Perm (Fin n)) (d : ℕ) (hd : d ≤ C.distance) :
    d ≤ ((C.reindex σ).reindex τ).distance := by simpa using hd

-- Products retain commutative algebra even after several intermediate operations.
example (C : StabCode n) (s t : Finset ι) (f g : ι → C.Stabilizer) :
    C.prod s f * C.prod t g = C.prod t g * C.prod s f := mul_comm _ _

example (C : StabCode n) (s : PauliGroup_group n) (hs : s ∈ C.stabs) :
    C.toUnitary (C.ofMem s hs) = (s : 𝐔ₙ[n]) := by simp

end PresentationWorkflow

#print axioms StabCode.Presentation.coefficientLinearMap_surjective
#print axioms StabCode.mapStabilizerLinearEquiv
#print axioms StabCode.Presentation.reindexQubits_symm
#print axioms PresentationWorkflow.relations_dimension
#print axioms PresentationWorkflow.repeated_relation
