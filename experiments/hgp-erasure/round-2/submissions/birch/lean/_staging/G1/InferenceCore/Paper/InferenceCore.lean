import Paper.Support

/-! Algebraic erasure inference and finite minimum distance, source.md C. -/
noncomputable section
namespace Paper
open QEC QEC.Coding QEC.Coding.HypergraphProduct Module
universe u
variable {Q R T : Type u} [Fintype Q] [DecidableEq Q] [Fintype R] [Fintype T]

/-- A quotient image has dimension zero exactly when all supported cycles are boundaries. -/
theorem supportedDim_zero_iff (C B : Submodule (ZMod 2) (Q → ZMod 2)) (E : Finset Q) :
    supportedDim C B E = 0 ↔ C ⊓ supportSpace E ≤ B := by
  rw [supportedDim, Submodule.finrank_eq_zero]
  constructor
  · intro h v hv
    have hm : B.mkQ v ∈ supportedLogical C B E := ⟨v, hv, rfl⟩
    rw [h] at hm
    exact Submodule.Quotient.eq_zero_iff_mem.mp hm
  · intro h
    apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      exact Submodule.Quotient.eq_zero_iff_mem.mpr (h hw)
    · exact bot_le

/-- Source C syndrome of a pair of pure X and pure Z errors. -/
def errorSyndrome (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2))
    (e : (Q → ZMod 2) × (Q → ZMod 2)) : (T → ZMod 2) × (R → ZMod 2) :=
  (Matrix.toLin' D e.1, Matrix.toLin' P e.2)

/-- Source C equivalence: component differences are actual stabilizer rows. -/
def errorEquivalent (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2))
    (e f : (Q → ZMod 2) × (Q → ZMod 2)) : Prop :=
  e.1 - f.1 ∈ LinearMap.range (Matrix.toLin' P.transpose) ∧
    e.2 - f.2 ∈ LinearMap.range (Matrix.toLin' D.transpose)

/-- Both components of an error are supported on the erased coordinates. -/
def errorSupported (E : Finset Q) (e : (Q → ZMod 2) × (Q → ZMod 2)) : Prop :=
  e.1 ∈ supportSpace E ∧ e.2 ∈ supportSpace E

/-- Erasure inference succeeds when equal syndromes imply error equivalence. -/
def erasureSucceeds (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2))
    (E : Finset Q) : Prop :=
  ∀ e f, errorSupported E e → errorSupported E f →
    errorSyndrome P D e = errorSyndrome P D f → errorEquivalent P D e f

/-- Failure is precisely ambiguity of supported errors with equal syndromes. -/
def erasureFails (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2))
    (E : Finset Q) : Prop := ¬ erasureSucceeds P D E

/-- A nontrivial representative in either pure CSS sector. -/
def cssLogical (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2))
    (v : Q → ZMod 2) : Prop :=
  (v ∈ LinearMap.ker (Matrix.toLin' P) ∧
    v ∉ LinearMap.range (Matrix.toLin' D.transpose)) ∨
  (v ∈ LinearMap.ker (Matrix.toLin' D) ∧
    v ∉ LinearMap.range (Matrix.toLin' P.transpose))

/-- Actual CSS distance: least weight of a nontrivial representative, or infinity. -/
def cssDistance (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2)) : WithTop ℕ := by
  classical
  exact finitePredicateMinimum (cssLogical P D) HammingWeight

/-- Least erased cardinality admitting ambiguity; infinity if all erasures succeed. -/
def erasureDistance (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2)) : WithTop ℕ := by
  classical
  exact finitePredicateMinimum (erasureFails P D) Finset.card

/-- Equal syndromes make supported differences into cycles, and each cycle can be
compared with zero. This is exactly vanishing of both quotient images (source C). -/
theorem erasureSucceeds_iff (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2))
    (E : Finset Q) :
    erasureSucceeds P D E ↔
      supportedDim (LinearMap.ker (Matrix.toLin' D))
          (LinearMap.range (Matrix.toLin' P.transpose)) E = 0 ∧
      supportedDim (LinearMap.ker (Matrix.toLin' P))
          (LinearMap.range (Matrix.toLin' D.transpose)) E = 0 := by
  rw [supportedDim_zero_iff, supportedDim_zero_iff]
  constructor
  · intro h
    constructor
    · intro v hv
      have he := h (v, 0) (0, 0) ⟨hv.2, (supportSpace E).zero_mem⟩
        ⟨(supportSpace E).zero_mem, (supportSpace E).zero_mem⟩ (by
          apply Prod.ext
          · exact hv.1
          · exact map_zero _)
      simpa [errorEquivalent] using he.1
    · intro v hv
      have he := h (0, v) (0, 0) ⟨(supportSpace E).zero_mem, hv.2⟩
        ⟨(supportSpace E).zero_mem, (supportSpace E).zero_mem⟩ (by
          apply Prod.ext
          · exact map_zero _
          · exact hv.1)
      simpa [errorEquivalent] using he.2
  · rintro ⟨hx, hz⟩ e f he hf hs
    have hxs : Matrix.toLin' D (e.1 - f.1) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Prod.fst hs
    have hzs : Matrix.toLin' P (e.2 - f.2) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Prod.snd hs
    exact ⟨hx ⟨hxs, (supportSpace E).sub_mem he.1 hf.1⟩,
      hz ⟨hzs, (supportSpace E).sub_mem he.2 hf.2⟩⟩

/-- Failure supplies precisely a supported nontrivial logical representative. -/
theorem erasureFails_iff (P : Matrix R Q (ZMod 2)) (D : Matrix T Q (ZMod 2))
    (E : Finset Q) :
    erasureFails P D E ↔ ∃ v, v ∈ supportSpace E ∧ cssLogical P D v := by
  classical
  rw [erasureFails, erasureSucceeds_iff, supportedDim_zero_iff, supportedDim_zero_iff]
  constructor
  · intro h
    by_cases hx : LinearMap.ker (Matrix.toLin' D) ⊓ supportSpace E ≤
        LinearMap.range (Matrix.toLin' P.transpose)
    · have hz := h ∘ And.intro hx
      simp only [Submodule.le_def, Submodule.mem_inf, not_forall, not_imp] at hz
      obtain ⟨v, hv, hn⟩ := hz
      exact ⟨v, hv.2, Or.inl ⟨hv.1, hn⟩⟩
    · simp only [Submodule.le_def, Submodule.mem_inf, not_forall, not_imp] at hx
      obtain ⟨v, hv, hn⟩ := hx
      exact ⟨v, hv.2, Or.inr ⟨hv.1, hn⟩⟩
  · rintro ⟨v, hv, hc | hc⟩ ⟨hx, hz⟩
    · exact hc.2 (hz ⟨hc.1, hv⟩)
    · exact hc.2 (hx ⟨hc.1, hv⟩)

/-- Supports realize logical weights, while every failing erasure contains such a support.
The two finite-infimum inequalities also cover empty witness families (source C). -/
theorem erasureDistance_eq_cssDistance (P : Matrix R Q (ZMod 2))
    (D : Matrix T Q (ZMod 2)) : erasureDistance P D = cssDistance P D := by
  classical
  apply le_antisymm
  · apply le_finitePredicateMinimum
    intro v hv
    have hs : v ∈ supportSpace (hammingSupport v) := by
      rw [mem_supportSpace]
      intro q hq
      simpa [hammingSupport] using hq
    have hf := (erasureFails_iff P D (hammingSupport v)).2 ⟨v, hs, hv⟩
    exact (finitePredicateMinimum_le_of (weight := Finset.card) hf).trans_eq
      (by rw [HammingWeight_eq_card_hammingSupport])
  · apply le_finitePredicateMinimum
    intro E hE
    obtain ⟨v, hv, hc⟩ := (erasureFails_iff P D E).1 hE
    have hw : HammingWeight v ≤ E.card := by
      rw [HammingWeight_eq_card_hammingSupport]
      apply Finset.card_le_card
      intro q hq
      by_contra hn
      have hz := (mem_supportSpace E v).1 hv q hn
      simpa [hammingSupport, hz] using hq
    exact (finitePredicateMinimum_le_of (weight := HammingWeight) hc).trans
      (WithTop.coe_le_coe.mpr hw)

end Paper
