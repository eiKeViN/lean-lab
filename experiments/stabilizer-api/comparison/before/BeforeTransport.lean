import Before
import UserReindex

/-! User-side code transport and distance proof on the original API. -/

noncomputable section

namespace BeforeTransport

variable {n : ℕ}

def reindexCode (C : StabCode n) (σ : Equiv.Perm (Fin n)) : StabCode n :=
  Before.mapCode C (PauliGroup.reindex σ) (PauliGroup.reindex_negId σ)

theorem reindex_normalizer (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (E : PauliGroup_group n) :
    PauliGroup.reindex σ E ∈ (reindexCode C σ).normalizerGroup ↔ E ∈ C.normalizerGroup := by
  change PauliGroup.reindex σ E ∈ Subgroup.centralizer
    ((C.stabs.map (PauliGroup.reindex σ).toMonoidHom : Subgroup (PauliGroup_group n)) : Set _) ↔ _
  simp only [StabCode.normalizerGroup, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · intro h s hs
    apply (PauliGroup.reindex σ).injective
    simpa only [map_mul] using h (PauliGroup.reindex σ s) ⟨s, hs, rfl⟩
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := ht
    simpa only [map_mul] using congrArg (PauliGroup.reindex σ) (h s hs)

theorem reindex_trivialLogicals (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (E : PauliGroup_group n) :
    PauliGroup.reindex σ E ∈ (reindexCode C σ).trivialLogicals ↔ E ∈ C.trivialLogicals := by
  have ht : (reindexCode C σ).trivialLogicals =
      C.trivialLogicals.map (PauliGroup.reindex σ).toMonoidHom := by
    change C.stabs.map (PauliGroup.reindex σ).toMonoidHom ⊔ PauliGroup.phaseSubgroup n =
      (C.stabs ⊔ PauliGroup.phaseSubgroup n).map (PauliGroup.reindex σ).toMonoidHom
    rw [Subgroup.map_sup, PauliGroup.reindex_phaseSubgroup]
  rw [ht]
  exact Subgroup.mem_map_iff_mem (PauliGroup.reindex σ).injective

theorem reindex_undetectable (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (E : PauliGroup_group n) :
    (reindexCode C σ).undetectable (PauliGroup.reindex σ E) ↔ C.undetectable E := by
  unfold StabCode.undetectable
  rw [reindex_normalizer, reindex_trivialLogicals, PauliGroup.reindex_normalized]

theorem reindex_distance (C : StabCode n) (σ : Equiv.Perm (Fin n)) :
    (reindexCode C σ).distance = C.distance := by
  have hweights : (reindexCode C σ).undetectable_set.image pauli_weight =
      C.undetectable_set.image pauli_weight := by
    ext w
    simp only [Finset.mem_image, StabCode.undetectable_set, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, hw⟩
      obtain ⟨q, rfl⟩ := (PauliGroup.reindex σ).surjective p
      exact ⟨q, (reindex_undetectable C σ q).mp hp,
        (PauliGroup.reindex_weight σ q).symm.trans hw⟩
    · rintro ⟨p, hp, hw⟩
      exact ⟨PauliGroup.reindex σ p, (reindex_undetectable C σ p).mpr hp,
        (PauliGroup.reindex_weight σ p).trans hw⟩
  unfold StabCode.distance
  rw [hweights]

theorem reindex_distance_bound (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (d : ℕ) (hd : d ≤ C.distance) : d ≤ (reindexCode C σ).distance := by
  rw [reindex_distance]
  exact hd

end BeforeTransport
