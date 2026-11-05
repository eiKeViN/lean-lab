import LeanQEC.Stabilizer.CSS

/-! User-provided Pauli permutation infrastructure; not present in the original API. -/

noncomputable section

local instance : CommGroup pgroup_phases :=
  { PauliPhases with mul_comm := mul_comm_pgroup_phases }

private theorem fold_pgroup_phases_eq_prod {n : ℕ} (f : Fin n → pgroup_phases) :
    fold_pgroup_phases f = ∏ i, f i := by
  induction n with
  | zero => simp [fold_pgroup_phases]
  | succ n ih =>
    rw [fold_pgroup_phases, Fin.prod_univ_succ, ih]
    rfl

namespace PauliGroup

variable {n : ℕ}

private def reindexFactored (σ : Equiv.Perm (Fin n)) : factored_Pauli n ≃ factored_Pauli n where
  toFun p := (p.1, fun i => p.2 (σ.symm i))
  invFun p := (p.1, fun i => p.2 (σ i))
  left_inv p := by simp
  right_inv p := by simp

private theorem reindexFactored_mul (σ : Equiv.Perm (Fin n)) (p q : factored_Pauli n) :
    reindexFactored σ (mul_factored_Paulis p q) =
      mul_factored_Paulis (reindexFactored σ p) (reindexFactored σ q) := by
  apply Prod.ext
  · change p.1 * q.1 * fold_pgroup_phases (fun i => (mul_Pauli1 (p.2 i) (q.2 i)).1) =
      p.1 * q.1 * fold_pgroup_phases (fun i =>
        (mul_Pauli1 (p.2 (σ.symm i)) (q.2 (σ.symm i))).1)
    simp only [fold_pgroup_phases_eq_prod]
    apply congrArg (fun z => p.1 * q.1 * z)
    exact (σ.symm.prod_comp (fun i => (mul_Pauli1 (p.2 i) (q.2 i)).1)).symm
  · rfl

private theorem unfold_mul (p q : PauliGroup_group n) :
    foldPauli.symm (p * q) = mul_factored_Paulis (foldPauli.symm p) (foldPauli.symm q) := by
  apply foldPauli.injective
  apply Subtype.ext
  simpa using (mul_factored_Paulis_correct (foldPauli.symm p) (foldPauli.symm q)).symm

/-- Relabel qubits: the factor formerly at `i` moves to `σ i`. -/
def reindex (σ : Equiv.Perm (Fin n)) : PauliGroup_group n ≃* PauliGroup_group n where
  toEquiv := foldPauli.symm.trans ((reindexFactored σ).trans foldPauli)
  map_mul' p q := by
    apply foldPauli.symm.injective
    change foldPauli.symm
        (foldPauli (reindexFactored σ (foldPauli.symm (p * q)))) =
      foldPauli.symm (@Mul.mul (PauliGroup_group n) inferInstance
        (foldPauli (reindexFactored σ (foldPauli.symm p)))
        (foldPauli (reindexFactored σ (foldPauli.symm q))))
    rw [Equiv.symm_apply_apply, unfold_mul]
    have hr := unfold_mul
      (foldPauli (reindexFactored σ (foldPauli.symm p)))
      (foldPauli (reindexFactored σ (foldPauli.symm q)))
    simp only [Equiv.symm_apply_apply] at hr
    exact (reindexFactored_mul σ _ _).trans hr.symm

@[simp]
theorem reindex_foldPauli (σ : Equiv.Perm (Fin n)) (p : factored_Pauli n) :
    reindex σ (foldPauli p) = foldPauli (p.1, fun i => p.2 (σ.symm i)) := by
  change foldPauli (reindexFactored σ (foldPauli.symm (foldPauli p))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
theorem reindex_negId (σ : Equiv.Perm (Fin n)) :
    reindex σ (negIdPauli n) = negIdPauli n := by
  simp [negIdPauli, scalarPauli]

@[simp]
theorem reindex_scalar (σ : Equiv.Perm (Fin n)) (z : pgroup_phases) :
    reindex σ (scalarPauli z) = scalarPauli z := by
  simp [scalarPauli]

@[simp]
theorem reindex_phase (σ : Equiv.Perm (Fin n)) (p : PauliGroup_group n) :
    PauliGroup.phase (reindex σ p) = PauliGroup.phase p := by
  change (foldPauli.symm (foldPauli (reindexFactored σ (foldPauli.symm p)))).1 =
    (foldPauli.symm p).1
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
theorem reindex_normalized (σ : Equiv.Perm (Fin n)) (p : PauliGroup_group n) :
    normalized (reindex σ p) ↔ normalized p := by
  simp [normalized]

theorem reindex_phaseSubgroup (σ : Equiv.Perm (Fin n)) :
    (phaseSubgroup n).map (reindex σ).toMonoidHom = phaseSubgroup n := by
  ext p
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_phaseSubgroup_iff_scalar q).mp hq
    exact (mem_phaseSubgroup_iff_scalar _).mpr ⟨z, reindex_scalar σ z⟩
  · intro hp
    obtain ⟨z, rfl⟩ := (mem_phaseSubgroup_iff_scalar p).mp hp
    exact ⟨scalarPauli z, (mem_phaseSubgroup_iff_scalar _).mpr ⟨z, rfl⟩,
      reindex_scalar σ z⟩

@[simp]
theorem reindex_map (σ : Equiv.Perm (Fin n)) (p : PauliGroup_group n) (i : Fin n) :
    PauliGroup.map (reindex σ p) i = PauliGroup.map p (σ.symm i) := by
  change (foldPauli.symm (reindex σ p)).2 i = (foldPauli.symm p).2 (σ.symm i)
  change (foldPauli.symm (foldPauli (reindexFactored σ (foldPauli.symm p)))).2 i = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
theorem reindex_weight (σ : Equiv.Perm (Fin n)) (p : PauliGroup_group n) :
    pauli_weight (reindex σ p) = pauli_weight p := by
  unfold pauli_weight
  apply Finset.card_equiv σ.symm
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, reindex_map]

end PauliGroup

