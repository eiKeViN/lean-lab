import LeanQEC.Stabilizer.Interface

/-! # Construction from certificates natural to downstream tasks -/

namespace PauliGroup

/-- All Pauli operators fixing a chosen vector form a subgroup. -/
def vectorStabilizer {n : ℕ} (ψ : PState n) : Subgroup (PauliGroup_group n) where
  carrier s := stabilizes (s : 𝐔ₙ[n]) ψ
  one_mem' := one_stab_all ψ
  mul_mem' ha hb := mul_stab ha hb
  inv_mem' ha := inv_stab ha

/-- To certify a common fixed vector, it suffices to check the chosen generators. -/
theorem closure_stabilizes_of_generators {n : ℕ} {ι : Type*}
    (g : ι → PauliGroup_group n) (ψ : PState n)
    (hg : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) :
    ∀ s ∈ Subgroup.closure (Set.range g), stabilizes (s : 𝐔ₙ[n]) ψ := by
  have hle : Subgroup.closure (Set.range g) ≤ vectorStabilizer ψ := by
    apply (Subgroup.closure_le (vectorStabilizer ψ)).mpr
    rintro s ⟨i, rfl⟩
    exact hg i
  exact hle

/-- A nonzero jointly stabilized vector certifies exclusion of minus the identity. -/
theorem negId_not_mem_of_stabilizes {n : ℕ} (S : Subgroup (PauliGroup_group n))
    (ψ : PState n) (hψ : ψ ≠ 0)
    (hstab : ∀ s ∈ S, stabilizes (s : 𝐔ₙ[n]) ψ) : negIdPauli n ∉ S := by
  intro hmem
  have h := stabilizes_apply' (hstab _ hmem)
  rw [negIdPauli_coe] at h
  have hneg : -ψ = ψ := by
    simpa only [Matrix.neg_unitary_val, OneMemClass.coe_one, Matrix.neg_mulVec,
      Matrix.one_mulVec] using h
  have htwo : (2 : ℂ) • ψ = 0 := by
    rw [two_smul]
    calc
      ψ + ψ = -ψ + ψ := congrArg (fun v => v + ψ) hneg.symm
      _ = 0 := neg_add_cancel _
  exact hψ ((smul_eq_zero.mp htwo).resolve_left (by norm_num))

end PauliGroup

namespace StabCode

variable {n : ℕ}

/-- Build a code from a nonzero stabilized vector, deriving its validity certificate. -/
def ofStabilizedVector (S : Subgroup (PauliGroup_group n)) (ψ : PState n)
    (hψ : ψ ≠ 0) (hstab : ∀ s ∈ S, stabilizes (s : 𝐔ₙ[n]) ψ) : StabCode n :=
  ofSubgroup S (PauliGroup.negId_not_mem_of_stabilizes S ψ hψ hstab)

@[simp]
theorem ofStabilizedVector_stabs (S : Subgroup (PauliGroup_group n)) (ψ : PState n)
    (hψ : ψ ≠ 0) (hstab : ∀ s ∈ S, stabilizes (s : 𝐔ₙ[n]) ψ) :
    (ofStabilizedVector S ψ hψ hstab).stabs = S := rfl

theorem mem_space_ofStabilizedVector (S : Subgroup (PauliGroup_group n)) (ψ : PState n)
    (hψ : ψ ≠ 0) (hstab : ∀ s ∈ S, stabilizes (s : 𝐔ₙ[n]) ψ) :
    ψ ∈ (ofStabilizedVector S ψ hψ hstab).space :=
  ((ofStabilizedVector S ψ hψ hstab).mem_space ψ).mpr hstab

end StabCode

namespace BinSympMatrix

/-- Independent commuting binary rows generate a valid stabilizer subgroup. -/
theorem negId_not_mem_of_linearIndependent {k n : ℕ} (B : BinSympMatrix k n)
    (hc : B.isCommuting) (hi : LinearIndependent (ZMod 2) B.row) :
    negIdPauli n ∉ B.pauliSubgroup := by
  intro hmem
  obtain ⟨c, he⟩ := (B.mem_pauliSubgroup_iff_rowProduct hc _).mp hmem
  have hsum : ∑ i, c i • B.row i = 0 := by
    have hselected : (∑ i, if c i = 1 then B.row i else 0) = 0 := by
      rw [B.selectedRows_sum_eq_mulVec, ← B.rowProduct_binaryImage hc c, he]
      have hI : Z2Z2_Pauli_equiv.symm Pauli_I = (0, 0) :=
        (Equiv.symm_apply_eq _).mpr rfl
      ext i <;>
        simp [Pauli_toBinSympPauli, negIdPauli, scalarPauli, PauliGroup.map, hI]
    convert hselected using 1
    apply Finset.sum_congr rfl
    intro i _
    rcases zmod2_eq_zero_or_one (c i) with h | h <;> simp [h]
  have hc0 : c = fun _ => 0 := funext ((Fintype.linearIndependent_iff.mp hi) c hsum)
  have hone : negIdPauli n = 1 := by
    rw [← he, hc0, B.rowProduct_zero]
  have hunitary : (-1 : 𝐔ₙ[n]) = 1 := by
    simpa only [negIdPauli_coe] using
      congrArg (fun s : PauliGroup_group n => (s : 𝐔ₙ[n])) hone
  exact Matrix.unitaryGroup.neg_ne hunitary

end BinSympMatrix

namespace StabCode

/-- Construct from the usual independent commuting check rows, deriving exclusion of `-I`. -/
def ofIndependentRows {k n : ℕ} (B : BinSympMatrix k n)
    (hc : B.isCommuting) (hi : LinearIndependent (ZMod 2) B.row) : StabCode n :=
  ofBinSympMatrix B (B.negId_not_mem_of_linearIndependent hc hi)

@[simp]
theorem ofIndependentRows_stabs {k n : ℕ} (B : BinSympMatrix k n)
    (hc : B.isCommuting) (hi : LinearIndependent (ZMod 2) B.row) :
    (ofIndependentRows B hc hi).stabs = B.pauliSubgroup := rfl

end StabCode
