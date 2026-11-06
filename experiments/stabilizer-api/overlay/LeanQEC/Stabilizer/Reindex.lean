import LeanQEC.Stabilizer.Transport

/-! # Qubit permutations with automatic transport of stabilizers and presentations -/

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
theorem reindex_refl (p : PauliGroup_group n) : reindex (Equiv.refl _) p = p := by
  obtain ⟨⟨z, a⟩, rfl⟩ := foldPauli.surjective p
  simp only [reindex_foldPauli, Equiv.refl_symm, Equiv.refl_apply]

@[simp]
theorem reindex_reindex (σ τ : Equiv.Perm (Fin n)) (p : PauliGroup_group n) :
    reindex τ (reindex σ p) = reindex (σ.trans τ) p := by
  obtain ⟨⟨z, a⟩, rfl⟩ := foldPauli.surjective p
  simp only [reindex_foldPauli]
  all_goals rfl

@[simp]
theorem reindex_symm (σ : Equiv.Perm (Fin n)) (p : PauliGroup_group n) :
    reindex σ.symm (reindex σ p) = p := by simp

@[simp]
theorem reindex_equiv_refl : reindex (Equiv.refl (Fin n)) = MulEquiv.refl _ := by
  apply MulEquiv.ext
  intro p
  exact reindex_refl p

@[simp]
theorem reindex_equiv_trans (σ τ : Equiv.Perm (Fin n)) :
    (reindex σ).trans (reindex τ) = reindex (σ.trans τ) := by
  apply MulEquiv.ext
  intro p
  simp

@[simp]
theorem reindex_equiv_symm (σ : Equiv.Perm (Fin n)) :
    (reindex σ).symm = reindex σ.symm := by
  apply MulEquiv.ext
  intro p
  apply (reindex σ).injective
  simp

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

namespace StabCode

variable {n : ℕ}

/-- Relabel qubits in a code, deriving the new validity certificate. -/
def reindex (C : StabCode n) (σ : Equiv.Perm (Fin n)) : StabCode n :=
  C.map (PauliGroup.reindex σ) (PauliGroup.reindex_negId σ)

@[simp]
theorem reindex_refl (C : StabCode n) : C.reindex (Equiv.refl _) = C := by
  simp [reindex]

@[simp]
theorem reindex_reindex (C : StabCode n) (σ τ : Equiv.Perm (Fin n)) :
    (C.reindex σ).reindex τ = C.reindex (σ.trans τ) := by
  simp only [reindex, map_map, PauliGroup.reindex_equiv_trans]

@[simp]
theorem reindex_symm (C : StabCode n) (σ : Equiv.Perm (Fin n)) :
    (C.reindex σ).reindex σ.symm = C := by simp

/-- Relabel a stabilizer without rebuilding its membership proof. -/
def reindexStabilizer (C : StabCode n) (σ : Equiv.Perm (Fin n)) :
    C.Stabilizer ≃* (C.reindex σ).Stabilizer :=
  C.mapStabilizer (PauliGroup.reindex σ) (PauliGroup.reindex_negId σ)

@[simp]
theorem toPauli_reindexStabilizer (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (s : C.Stabilizer) :
    (C.reindex σ).toPauli (C.reindexStabilizer σ s) =
      PauliGroup.reindex σ (C.toPauli s) := rfl

@[simp]
theorem reindexStabilizer_refl (C : StabCode n) (s : C.Stabilizer) :
    stabilizerCongr C.reindex_refl (C.reindexStabilizer (Equiv.refl _) s) = s := by
  apply C.toPauli_injective
  simp

@[simp]
theorem reindexStabilizer_trans (C : StabCode n) (σ τ : Equiv.Perm (Fin n))
    (s : C.Stabilizer) :
    stabilizerCongr (C.reindex_reindex σ τ)
      ((C.reindex σ).reindexStabilizer τ (C.reindexStabilizer σ s)) =
      C.reindexStabilizer (σ.trans τ) s := by
  apply (C.reindex (σ.trans τ)).toPauli_injective
  simp

@[simp]
theorem reindexStabilizer_symm (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (s : C.Stabilizer) :
    stabilizerCongr (C.reindex_symm σ)
      ((C.reindex σ).reindexStabilizer σ.symm (C.reindexStabilizer σ s)) = s := by
  apply C.toPauli_injective
  simp

@[simp]
theorem reindex_numGenerators (C : StabCode n) (σ : Equiv.Perm (Fin n)) :
    (C.reindex σ).numGenerators = C.numGenerators :=
  C.map_numGenerators _ _

@[simp]
theorem reindex_normalizer_iff (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (E : PauliGroup_group n) :
    PauliGroup.reindex σ E ∈ (C.reindex σ).normalizerGroup ↔ E ∈ C.normalizerGroup :=
  C.mem_map_normalizer_iff _ _ E

@[simp]
theorem reindex_trivialLogicals_iff (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (E : PauliGroup_group n) :
    PauliGroup.reindex σ E ∈ (C.reindex σ).trivialLogicals ↔ E ∈ C.trivialLogicals := by
  change PauliGroup.reindex σ E ∈
    (C.map (PauliGroup.reindex σ) (PauliGroup.reindex_negId σ)).trivialLogicals ↔ _
  rw [C.map_trivialLogicals _ _ (PauliGroup.reindex_phaseSubgroup σ)]
  exact Subgroup.mem_map_iff_mem (PauliGroup.reindex σ).injective

@[simp]
theorem reindex_undetectable_iff (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (E : PauliGroup_group n) :
    (C.reindex σ).undetectable (PauliGroup.reindex σ E) ↔ C.undetectable E := by
  unfold undetectable
  rw [C.reindex_normalizer_iff σ E, C.reindex_trivialLogicals_iff σ E,
    PauliGroup.reindex_normalized σ E]

@[simp]
theorem reindex_distance (C : StabCode n) (σ : Equiv.Perm (Fin n)) :
    (C.reindex σ).distance = C.distance := by
  have hweights : (C.reindex σ).undetectable_set.image pauli_weight =
      C.undetectable_set.image pauli_weight := by
    ext w
    simp only [Finset.mem_image, undetectable_set, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, hw⟩
      obtain ⟨q, rfl⟩ := (PauliGroup.reindex σ).surjective p
      exact ⟨q, (C.reindex_undetectable_iff σ q).mp hp,
        (PauliGroup.reindex_weight σ q).symm.trans hw⟩
    · rintro ⟨p, hp, hw⟩
      exact ⟨PauliGroup.reindex σ p, (C.reindex_undetectable_iff σ p).mpr hp,
        (PauliGroup.reindex_weight σ p).trans hw⟩
  unfold distance
  rw [hweights]

namespace Presentation

variable {C : StabCode n} {ι : Type*}

/-- Relabel qubits in every generator while retaining the generation theorem. -/
def reindexQubits (P : C.Presentation ι) (σ : Equiv.Perm (Fin n)) :
    (C.reindex σ).Presentation ι :=
  P.map (PauliGroup.reindex σ) (PauliGroup.reindex_negId σ)

@[simp]
theorem reindexQubits_generator (P : C.Presentation ι) (σ : Equiv.Perm (Fin n)) (i : ι) :
    (P.reindexQubits σ).generator i = C.reindexStabilizer σ (P.generator i) := rfl

@[simp]
theorem reindexQubits_refl (P : C.Presentation ι) :
    (P.reindexQubits (Equiv.refl _)).congrCode C.reindex_refl = P := by
  ext i
  apply C.toPauli_injective
  simp

@[simp]
theorem reindexQubits_reindexQubits (P : C.Presentation ι) (σ τ : Equiv.Perm (Fin n)) :
    ((P.reindexQubits σ).reindexQubits τ).congrCode (C.reindex_reindex σ τ) =
      P.reindexQubits (σ.trans τ) := by
  ext i
  apply (C.reindex (σ.trans τ)).toPauli_injective
  simp

@[simp]
theorem reindexQubits_symm (P : C.Presentation ι) (σ : Equiv.Perm (Fin n)) :
    ((P.reindexQubits σ).reindexQubits σ.symm).congrCode (C.reindex_symm σ) = P := by
  ext i
  apply C.toPauli_injective
  simp

theorem reindexQubits_combination [Fintype ι] (P : C.Presentation ι)
    (σ : Equiv.Perm (Fin n)) (c : ι → ZMod 2) :
    (P.reindexQubits σ).combination c = C.reindexStabilizer σ (P.combination c) :=
  P.map_combination _ _ c

/-- Relabeling generators and relabeling qubits commute. -/
theorem reindexQubits_reindex {κ : Type*} (P : C.Presentation ι)
    (e : ι ≃ κ) (σ : Equiv.Perm (Fin n)) :
    (P.reindex e).reindexQubits σ = (P.reindexQubits σ).reindex e := by ext i; rfl

end Presentation
end StabCode
