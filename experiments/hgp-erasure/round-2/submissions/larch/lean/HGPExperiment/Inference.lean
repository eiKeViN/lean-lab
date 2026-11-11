import HGPExperiment.Erasure
import QEC.Coding.HypergraphProduct.Distance

noncomputable section
namespace HGPExperiment
open QEC.Coding QEC.Coding.HypergraphProduct
universe u v w t
variable {F : Type u} {Q : Type v} {R : Type w} {S : Type t}
variable [Field F] [Fintype Q] [Fintype R] [Fintype S]

/-- The two independent Pauli components, in X,Z order. -/
abbrev ErrorPair (F Q : Type*) := (Q → F) × (Q → F)

def pairSupported (E : Set Q) (a : ErrorPair F Q) : Prop :=
  a.1 ∈ coordinateSpace E ∧ a.2 ∈ coordinateSpace E

def syndrome (P : Matrix R Q F) (D : Matrix S Q F) (a : ErrorPair F Q) :=
  (D.mulVecLin a.1, P.mulVecLin a.2)

/-- Equality of errors modulo the X and Z stabilizer row spaces. -/
def errorEquivalent (P : Matrix R Q F) (D : Matrix S Q F)
    (a b : ErrorPair F Q) : Prop :=
  a.1 - b.1 ∈ boundaries P ∧ a.2 - b.2 ∈ boundaries D

/-- Every syndrome determines one equivalence class among errors on E. -/
def erasureSucceeds (P : Matrix R Q F) (D : Matrix S Q F) (E : Set Q) : Prop :=
  ∀ a b : ErrorPair F Q, pairSupported E a → pairSupported E b →
    syndrome P D a = syndrome P D b → errorEquivalent P D a b

def erasureFails (P : Matrix R Q F) (D : Matrix S Q F) (E : Set Q) : Prop :=
  ¬ erasureSucceeds P D E

/-- The ambiguity criterion, for both actual supported logical images. -/
theorem erasureSucceeds_iff (P : Matrix R Q F) (D : Matrix S Q F) (E : Set Q) :
    erasureSucceeds P D E ↔ xDim P D E = 0 ∧ zDim P D E = 0 := by
  rw [xDim, zDim, zDim, supportedDim_eq_zero_iff, supportedDim_eq_zero_iff]
  constructor
  · intro h
    constructor
    · intro v hv
      have hs : syndrome P D (v, 0) = syndrome P D (0, 0) := by
        apply Prod.ext
        · exact (LinearMap.mem_ker.mp hv.1).trans (map_zero _).symm
        · rfl
      have he := h (v, 0) (0, 0) ⟨hv.2, (coordinateSpace E).zero_mem⟩
        ⟨(coordinateSpace E).zero_mem, (coordinateSpace E).zero_mem⟩ hs
      simpa [errorEquivalent] using he.1
    · intro v hv
      have hs : syndrome P D (0, v) = syndrome P D (0, 0) := by
        apply Prod.ext
        · rfl
        · exact (LinearMap.mem_ker.mp hv.1).trans (map_zero _).symm
      have he := h (0, v) (0, 0) ⟨(coordinateSpace E).zero_mem, hv.2⟩
        ⟨(coordinateSpace E).zero_mem, (coordinateSpace E).zero_mem⟩ hs
      simpa [errorEquivalent] using he.2
  · rintro ⟨hx, hz⟩ a b ha hb hs
    change a.1 ∈ coordinateSpace E ∧ a.2 ∈ coordinateSpace E at ha
    change b.1 ∈ coordinateSpace E ∧ b.2 ∈ coordinateSpace E at hb
    change a.1 - b.1 ∈ boundaries P ∧ a.2 - b.2 ∈ boundaries D
    refine ⟨hx ⟨?_, (coordinateSpace (F := F) E).sub_mem ha.1 hb.1⟩,
      hz ⟨?_, (coordinateSpace (F := F) E).sub_mem ha.2 hb.2⟩⟩
    · exact (LinearMap.sub_mem_ker_iff).mpr (congrArg Prod.fst hs)
    · exact (LinearMap.sub_mem_ker_iff).mpr (congrArg Prod.snd hs)

/-- The nontrivial pure logical vectors of the matrix CSS model. -/
def matrixLogical (P : Matrix R Q F) (D : Matrix S Q F) (v : Q → F) : Prop :=
  (v ∈ cycles D ∧ v ∉ boundaries P) ∨
    (v ∈ cycles P ∧ v ∉ boundaries D)

/-- Failure supplies a supported nontrivial representative, and conversely. -/
theorem erasureFails_iff (P : Matrix R Q F) (D : Matrix S Q F) (E : Set Q) :
    erasureFails P D E ↔
      ∃ v : Q → F, v ∈ coordinateSpace E ∧ matrixLogical P D v := by
  classical
  rw [erasureFails, erasureSucceeds_iff, xDim, zDim, zDim,
    supportedDim_eq_zero_iff, supportedDim_eq_zero_iff]
  constructor
  · intro h
    by_contra hn
    apply h
    constructor
    · intro v hv
      by_contra hvb
      exact hn ⟨v, hv.2, Or.inl ⟨hv.1, hvb⟩⟩
    · intro v hv
      by_contra hvb
      exact hn ⟨v, hv.2, Or.inr ⟨hv.1, hvb⟩⟩
  · rintro ⟨v, hv, (hx | hz)⟩ ⟨h1, h2⟩
    · exact hx.2 (h1 ⟨hx.1, hv⟩)
    · exact hz.2 (h2 ⟨hz.1, hv⟩)

variable [Fintype F] [DecidableEq F] [DecidableEq Q]

/-- CSS distance with infinity for an empty set of nontrivial logical vectors. -/
def matrixCSSDistance (P : Matrix R Q F) (D : Matrix S Q F) : WithTop Nat := by
  classical
  exact finitePredicateMinimum (matrixLogical P D) HammingWeight

/-- Least cardinality of an ambiguous erasure; infinity if none exists. -/
def erasureDistance (P : Matrix R Q F) (D : Matrix S Q F) : WithTop Nat := by
  classical
  exact finitePredicateMinimum (fun E : Finset Q => erasureFails P D (E : Set Q))
    Finset.card

theorem word_supported_on_support (v : Q → F) :
    v ∈ coordinateSpace (hammingSupport v : Set Q) := by
  classical
  intro q hq
  by_contra h
  exact hq (by simp [hammingSupport, h])

theorem weight_le_of_supported {E : Finset Q} {v : Q → F}
    (hv : v ∈ coordinateSpace (E : Set Q)) : HammingWeight v ≤ E.card := by
  apply Finset.card_le_card
  intro q hq
  by_contra hn
  have := hv q hn
  exact (Finset.mem_filter.mp hq).2 this

/-- Distance is exactly the smallest erasure causing an equivalence ambiguity. -/
theorem erasureDistance_eq_cssDistance (P : Matrix R Q F) (D : Matrix S Q F) :
    erasureDistance P D = matrixCSSDistance P D := by
  classical
  apply le_antisymm
  · apply le_finitePredicateMinimum
    intro v hv
    have hf : erasureFails P D (hammingSupport v : Set Q) :=
      (erasureFails_iff P D _).mpr ⟨v, word_supported_on_support v, hv⟩
    exact finitePredicateMinimum_le_of (weight := Finset.card) hf
  · apply le_finitePredicateMinimum
    intro E hE
    obtain ⟨v, hv, hl⟩ := (erasureFails_iff P D _).mp hE
    exact (finitePredicateMinimum_le_of (weight := HammingWeight) hl).trans
      (WithTop.coe_le_coe.mpr (weight_le_of_supported hv))

theorem erasureDistance_eq_top_iff (P : Matrix R Q F) (D : Matrix S Q F) :
    erasureDistance P D = ⊤ ↔ ∀ E : Finset Q, ¬ erasureFails P D (E : Set Q) := by
  classical
  exact finitePredicateMinimum_eq_top_iff

end HGPExperiment
