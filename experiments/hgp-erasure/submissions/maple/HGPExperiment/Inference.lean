import HGPExperiment.Erasure
import QEC.Coding.HypergraphProduct.Distance
import QEC.Coding.HypergraphProduct.Dimension.Formula

noncomputable section
namespace HGPExperiment
open QEC.Coding QEC.Coding.HypergraphProduct

variable {Q RX RZ : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype RX] [DecidableEq RX] [Fintype RZ] [DecidableEq RZ]

/-- An X error and a Z error, in that order. -/
abbrev ErrorPair (Q : Type*) := (Q → F₂) × (Q → F₂)

/-- Both components vanish outside the erased coordinates. -/
def SupportedError (E : Set Q) (e : ErrorPair Q) : Prop :=
  e.1 ∈ supportSpace E ∧ e.2 ∈ supportSpace E

/-- The measured Z-check and X-check syndromes. -/
def syndrome (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) (e : ErrorPair Q) :=
  (Matrix.toLin' D e.1, Matrix.toLin' P e.2)

/-- Equality up to X and Z stabilizers. -/
def ErrorEquivalent (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (e f : ErrorPair Q) : Prop :=
  e.1 - f.1 ∈ boundaries P ∧ e.2 - f.2 ∈ boundaries D

/-- Erasure inference succeeds exactly when a syndrome specifies one error class. -/
def ErasureCorrectable (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) (E : Set Q) : Prop :=
  ∀ e f, SupportedError E e → SupportedError E f →
    syndrome P D e = syndrome P D f → ErrorEquivalent P D e f

/-- Failure means ambiguity between inequivalent errors of the same syndrome. -/
def ErasureFails (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) (E : Set Q) : Prop :=
  ∃ e f, SupportedError E e ∧ SupportedError E f ∧
    syndrome P D e = syndrome P D f ∧ ¬ ErrorEquivalent P D e f

theorem erasureFails_iff_not_correctable (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (E : Set Q) : ErasureFails P D E ↔ ¬ ErasureCorrectable P D E := by
  classical
  simp only [ErasureFails, ErasureCorrectable, not_forall, not_imp]

theorem correctable_iff_cycles_trivial (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (E : Set Q) :
    ErasureCorrectable P D E ↔
      (∀ v, v ∈ cycles D → v ∈ supportSpace E → v ∈ boundaries P) ∧
      (∀ v, v ∈ cycles P → v ∈ supportSpace E → v ∈ boundaries D) := by
  constructor
  · intro h
    constructor
    · intro v hv hs
      have he := h (v, 0) (0, 0) ⟨hs, (supportSpace E).zero_mem⟩
        ⟨(supportSpace E).zero_mem, (supportSpace E).zero_mem⟩
        (by simpa [syndrome, cycles, LinearMap.mem_ker] using hv)
      simpa [ErrorEquivalent] using he.1
    · intro v hv hs
      have he := h (0, v) (0, 0) ⟨(supportSpace E).zero_mem, hs⟩
        ⟨(supportSpace E).zero_mem, (supportSpace E).zero_mem⟩
        (by simpa [syndrome, cycles, LinearMap.mem_ker] using hv)
      simpa [ErrorEquivalent] using he.2
  · rintro ⟨hx, hz⟩ e f he hf hsyn
    constructor
    · apply hx (e.1 - f.1)
      · change Matrix.toLin' D (e.1 - f.1) = 0
        rw [map_sub, sub_eq_zero]
        exact congrArg Prod.fst hsyn
      · exact (supportSpace E).sub_mem he.1 hf.1
    · apply hz (e.2 - f.2)
      · change Matrix.toLin' P (e.2 - f.2) = 0
        rw [map_sub, sub_eq_zero]
        exact congrArg Prod.snd hsyn
      · exact (supportSpace E).sub_mem he.2 hf.2

theorem erasureCorrectable_iff_dimensions_zero
    (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) (E : Set Q) :
    ErasureCorrectable P D E ↔
      logicalDimension D P E = 0 ∧ logicalDimension P D E = 0 := by
  rw [correctable_iff_cycles_trivial, logicalDimension_eq_zero_iff,
    logicalDimension_eq_zero_iff]

/-- A nontrivial pure logical representative, in either sector. -/
def IsLogicalWord (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) (v : Q → F₂) : Prop :=
  (v ∈ cycles D ∧ v ∉ boundaries P) ∨ (v ∈ cycles P ∧ v ∉ boundaries D)

theorem erasureFails_iff_logical_supported
    (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) (E : Set Q) :
    ErasureFails P D E ↔ ∃ v, IsLogicalWord P D v ∧ v ∈ supportSpace E := by
  classical
  rw [erasureFails_iff_not_correctable, correctable_iff_cycles_trivial]
  simp only [not_and_or, not_forall, not_imp, IsLogicalWord]
  aesop

/-- The CSS distance, minimized over the actual nonzero pure logical words. -/
def cssDistance (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) : WithTop Nat := by
  classical
  exact finitePredicateMinimum (IsLogicalWord P D) HammingWeight

theorem rowCode_carrier_eq_boundaries (P : Matrix RX Q F₂) :
    (parityCheckRowCode (Matrix.toLin' P)).carrier = boundaries P := by
  unfold parityCheckRowCode boundaries
  rw [wordLinearMapTranspose_toLin'_eq]

theorem isLogicalWord_iff_isCSSLogical (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    (v : Q → F₂) :
    IsLogicalWord P D v ↔
      IsCSSLogical (parityCheckRowCode (Matrix.toLin' P))
        (parityCheckRowCode (Matrix.toLin' D)) v := by
  simp only [IsLogicalWord, IsCSSLogical, parityCheckRowCode_dual_eq_kernelCode,
    rowCode_carrier_eq_boundaries, parityCheckKernelCode, cycles]

theorem cssDistance_eq_extendedAlgebraicCSSMinimumDistance
    (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) :
    cssDistance P D = extendedAlgebraicCSSMinimumDistance
      (parityCheckRowCode (Matrix.toLin' P)) (parityCheckRowCode (Matrix.toLin' D)) := by
  classical
  unfold cssDistance extendedAlgebraicCSSMinimumDistance
  congr 1
  funext v
  exact propext (isLogicalWord_iff_isCSSLogical P D v)

/-- The minimum erasure size causing ambiguity; the empty minimum is infinity. -/
def erasureDistance (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) : WithTop Nat := by
  classical
  exact finitePredicateMinimum (fun E : Finset Q => ErasureFails P D (E : Set Q))
    Finset.card

theorem logical_supported_on_own_support (v : Q → F₂) :
    v ∈ supportSpace (hammingSupport v : Set Q) := by
  intro q hq
  simpa [hammingSupport] using hq

theorem weight_le_erasure_size {E : Finset Q} {v : Q → F₂}
    (hv : v ∈ supportSpace (E : Set Q)) : HammingWeight v ≤ E.card := by
  apply Finset.card_le_card
  intro q hq
  by_contra hnot
  have hz := hv q hnot
  simpa [hammingSupport, hz] using hq

theorem erasureDistance_eq_cssDistance (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) :
    erasureDistance P D = cssDistance P D := by
  classical
  apply le_antisymm
  · unfold cssDistance
    apply le_finitePredicateMinimum
    intro v hv
    have hf : ErasureFails P D (hammingSupport v : Set Q) :=
      (erasureFails_iff_logical_supported P D _).2
        ⟨v, hv, logical_supported_on_own_support v⟩
    exact finitePredicateMinimum_le_of (weight := Finset.card) hf
  · unfold erasureDistance
    apply le_finitePredicateMinimum
    intro E hE
    obtain ⟨v, hv, hs⟩ := (erasureFails_iff_logical_supported P D _).1 hE
    exact (finitePredicateMinimum_le_of (weight := HammingWeight) hv).trans
      (WithTop.coe_le_coe.mpr (weight_le_erasure_size hs))

theorem erasureDistance_eq_top_iff (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) :
    erasureDistance P D = ⊤ ↔ ∀ E : Set Q, ¬ ErasureFails P D E := by
  classical
  rw [erasureDistance, finitePredicateMinimum_eq_top_iff]
  constructor
  · intro h E hE
    exact h E.toFinset (by simpa using hE)
  · intro h E
    exact h E

theorem cssDistance_le_weight (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂)
    {v : Q → F₂} (hv : IsLogicalWord P D v) :
    cssDistance P D ≤ (HammingWeight v : WithTop ℕ) := by
  classical
  exact finitePredicateMinimum_le_of hv

theorem erasureCorrectable_of_card_lt_distance
    (P : Matrix RX Q F₂) (D : Matrix RZ Q F₂) (E : Finset Q)
    (h : (E.card : WithTop ℕ) < cssDistance P D) :
    ErasureCorrectable P D (E : Set Q) := by
  classical
  by_contra hf
  obtain ⟨v, hv, hs⟩ := (erasureFails_iff_logical_supported P D _).1
    ((erasureFails_iff_not_correctable P D _).2 hf)
  have hw := (cssDistance_le_weight P D hv).trans
    (WithTop.coe_le_coe.mpr (weight_le_erasure_size hs))
  exact (not_lt_of_ge hw) h

end HGPExperiment
