import LeanQEC.Stabilizer.BinaryBridge

/-!
# Transporting codes, their elements, and their generating presentations

One ambient Pauli equivalence induces all three transports. Downstream callers
reuse the resulting maps instead of reconstructing membership certificates.
-/

namespace StabCode

variable {n m : ℕ}

/-- The canonical algebraic identification associated with an equality of codes. -/
def stabilizerCongr {C D : StabCode n} (h : C = D) : C.Stabilizer ≃* D.Stabilizer :=
  MulEquiv.cast h

@[simp]
theorem toPauli_stabilizerCongr {C D : StabCode n} (h : C = D) (s : C.Stabilizer) :
    D.toPauli (stabilizerCongr h s) = C.toPauli s := by cases h; rfl

/-- Transport a stabilizer code along a Pauli equivalence preserving minus identity. -/
def map (C : StabCode n) (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) : StabCode m :=
  ofSubgroup (C.stabs.map e.toMonoidHom) (by
    rintro ⟨s, hs, he⟩
    apply C.h_minus
    have : s = negIdPauli n := e.injective (he.trans hneg.symm)
    simpa [this] using hs)

@[simp]
theorem map_stabs (C : StabCode n) (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) :
    (C.map e hneg).stabs = C.stabs.map e.toMonoidHom := rfl

@[simp]
theorem map_refl (C : StabCode n) : C.map (MulEquiv.refl _) rfl = C := by
  apply StabCode.ext
  simp

/-- Consecutive maps normalize to one map along the composite equivalence. -/
@[simp]
theorem map_map {l : ℕ} (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (f : PauliGroup_group m ≃* PauliGroup_group l)
    (he : e (negIdPauli n) = negIdPauli m) (hf : f (negIdPauli m) = negIdPauli l) :
    (C.map e he).map f hf = C.map (e.trans f) (by simp [he, hf]) := by
  apply StabCode.ext
  simp only [map_stabs, Subgroup.map_map]
  rfl

@[simp]
theorem map_symm (C : StabCode n) (e : PauliGroup_group n ≃* PauliGroup_group m)
    (he : e (negIdPauli n) = negIdPauli m) :
    (C.map e he).map e.symm (by rw [← he]; simp) = C := by simp

/-- Transport a typed stabilizer, retaining all its algebraic operations. -/
def mapStabilizer (C : StabCode n) (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) :
    C.Stabilizer ≃* (C.map e hneg).Stabilizer :=
  C.stabilizerEquiv.trans ((e.subgroupMap C.stabs).trans
    (C.map e hneg).stabilizerEquiv.symm)

@[simp]
theorem toPauli_mapStabilizer (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) (s : C.Stabilizer) :
    (C.map e hneg).toPauli (C.mapStabilizer e hneg s) = e (C.toPauli s) := rfl

@[simp]
theorem mapStabilizer_refl (C : StabCode n) (s : C.Stabilizer) :
    stabilizerCongr C.map_refl (C.mapStabilizer (MulEquiv.refl _) rfl s) = s := by
  apply C.toPauli_injective
  simp

@[simp]
theorem mapStabilizer_trans {l : ℕ} (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (f : PauliGroup_group m ≃* PauliGroup_group l)
    (he : e (negIdPauli n) = negIdPauli m) (hf : f (negIdPauli m) = negIdPauli l)
    (s : C.Stabilizer) :
    stabilizerCongr (C.map_map e f he hf)
      ((C.map e he).mapStabilizer f hf (C.mapStabilizer e he s)) =
      C.mapStabilizer (e.trans f) (by simp [he, hf]) s := by
  apply (C.map (e.trans f) _).toPauli_injective
  simp

@[simp]
theorem mapStabilizer_symm (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (he : e (negIdPauli n) = negIdPauli m) (s : C.Stabilizer) :
    stabilizerCongr (C.map_symm e he)
      ((C.map e he).mapStabilizer e.symm (by rw [← he]; simp)
        (C.mapStabilizer e he s)) = s := by
  apply C.toPauli_injective
  simp

/-- The same transport is linear in the binary scalar structure. -/
noncomputable def mapStabilizerLinearEquiv (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) :
    Additive C.Stabilizer ≃ₗ[ZMod 2] Additive (C.map e hneg).Stabilizer :=
  let a := MulEquiv.toAdditive (C.mapStabilizer e hneg)
  { a with map_smul' := (a.toAddMonoidHom.toZModLinearMap 2).map_smul' }

@[simp]
theorem mapStabilizerLinearEquiv_ofMul (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) (s : C.Stabilizer) :
    C.mapStabilizerLinearEquiv e hneg (Additive.ofMul s) =
      Additive.ofMul (C.mapStabilizer e hneg s) := rfl

theorem map_numGenerators (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) :
    (C.map e hneg).numGenerators = C.numGenerators := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  change (2 : ℕ) ^ (C.map e hneg).numGenerators = 2 ^ C.numGenerators
  rw [← StabCode.card_stabs, ← StabCode.card_stabs]
  exact (Nat.card_congr (C.mapStabilizer e hneg).toEquiv).symm

/-- Normalizer membership follows the same ambient equivalence. -/
theorem mem_map_normalizer_iff (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) (E : PauliGroup_group n) :
    e E ∈ (C.map e hneg).normalizerGroup ↔ E ∈ C.normalizerGroup := by
  simp only [normalizerGroup, map_stabs, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · intro h s hs
    apply e.injective
    simpa only [map_mul] using h (e s) ⟨s, hs, rfl⟩
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := ht
    simpa only [map_mul] using congrArg e (h s hs)

/-- Trivial logicals transport when the equivalence preserves the phase subgroup. -/
theorem map_trivialLogicals (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m)
    (hphase : (PauliGroup.phaseSubgroup n).map e.toMonoidHom = PauliGroup.phaseSubgroup m) :
    (C.map e hneg).trivialLogicals = C.trivialLogicals.map e.toMonoidHom := by
  simp only [trivialLogicals, map_stabs, Subgroup.map_sup, hphase]

namespace Presentation

variable {C : StabCode n} {ι κ : Type*}

@[ext]
theorem ext (P Q : C.Presentation ι) (h : ∀ i, P.generator i = Q.generator i) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      have : p = q := funext h
      cases this
      rfl

/-- Identify presentation types using an equality of their codes. -/
def congrCode {D : StabCode n} (h : C = D) (P : C.Presentation ι) : D.Presentation ι :=
  h ▸ P

@[simp]
theorem congrCode_generator {D : StabCode n} (h : C = D) (P : C.Presentation ι) (i : ι) :
    (P.congrCode h).generator i = stabilizerCongr h (P.generator i) := by cases h; rfl

/-- A relabeling of generators changes the presentation while preserving the code. -/
def reindex (P : C.Presentation ι) (e : ι ≃ κ) : C.Presentation κ where
  generator j := P.generator (e.symm j)
  generates := by
    rw [← P.generates]
    congr 1
    ext s
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp⟩

@[simp]
theorem reindex_generator (P : C.Presentation ι) (e : ι ≃ κ) (j : κ) :
    (P.reindex e).generator j = P.generator (e.symm j) := rfl

@[simp]
theorem reindex_refl (P : C.Presentation ι) : P.reindex (Equiv.refl _) = P := by ext i; rfl

@[simp]
theorem reindex_reindex {υ : Type*} (P : C.Presentation ι) (e : ι ≃ κ) (f : κ ≃ υ) :
    (P.reindex e).reindex f = P.reindex (e.trans f) := by ext i; rfl

@[simp]
theorem reindex_symm (P : C.Presentation ι) (e : ι ≃ κ) :
    (P.reindex e).reindex e.symm = P := by ext i; simp

theorem reindex_combination [Fintype ι] [Fintype κ] (P : C.Presentation ι)
    (e : ι ≃ κ) (c : ι → ZMod 2) :
    (P.reindex e).combination (fun j => c (e.symm j)) = P.combination c := by
  exact e.symm.prod_comp (fun i => if c i = 1 then P.generator i else 1)

/-- Transport the complete presentation along the ambient equivalence. -/
def map (P : C.Presentation ι) (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) : (C.map e hneg).Presentation ι where
  generator i := C.mapStabilizer e hneg (P.generator i)
  generates := by
    change Subgroup.closure (Set.range (fun i => e (C.toPauli (P.generator i)))) =
      C.stabs.map e.toMonoidHom
    rw [← P.generates, MonoidHom.map_closure]
    congr 1
    ext s
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨C.toPauli (P.generator i), ⟨i, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩

@[simp]
theorem map_generator (P : C.Presentation ι)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) (i : ι) :
    (P.map e hneg).generator i = C.mapStabilizer e hneg (P.generator i) := rfl

@[simp]
theorem map_refl (P : C.Presentation ι) :
    (P.map (MulEquiv.refl _) rfl).congrCode C.map_refl = P := by
  ext i
  apply C.toPauli_injective
  simp

@[simp]
theorem map_map {l : ℕ} (P : C.Presentation ι)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (f : PauliGroup_group m ≃* PauliGroup_group l)
    (he : e (negIdPauli n) = negIdPauli m) (hf : f (negIdPauli m) = negIdPauli l) :
    ((P.map e he).map f hf).congrCode (C.map_map e f he hf) =
      P.map (e.trans f) (by simp [he, hf]) := by
  ext i
  apply (C.map (e.trans f) _).toPauli_injective
  simp

@[simp]
theorem map_symm (P : C.Presentation ι)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (he : e (negIdPauli n) = negIdPauli m) :
    ((P.map e he).map e.symm (by rw [← he]; simp)).congrCode (C.map_symm e he) = P := by
  ext i
  apply C.toPauli_injective
  simp

theorem map_combination [Fintype ι] (P : C.Presentation ι)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) (c : ι → ZMod 2) :
    (P.map e hneg).combination c = C.mapStabilizer e hneg (P.combination c) := by
  simp only [combination, map_prod, apply_ite, map_one, map_generator]

/-- Coefficients commute with transport, as an equality of linear maps. -/
theorem coefficientLinearMap_map [Fintype ι] (P : C.Presentation ι)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) :
    (P.map e hneg).coefficientLinearMap =
      (C.mapStabilizerLinearEquiv e hneg).toLinearMap.comp P.coefficientLinearMap := by
  ext c
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, coefficientLinearMap_apply,
    map_combination, mapStabilizerLinearEquiv_ofMul]

end Presentation
end StabCode
