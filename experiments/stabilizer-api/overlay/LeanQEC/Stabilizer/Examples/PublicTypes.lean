import LeanQEC.Stabilizer.API

/-! Public signature contracts for the experiment's intended downstream entrypoints. -/

noncomputable section

variable {n : ℕ} {ι : Type*}

example (C : StabCode n) : CommGroup C.Stabilizer := inferInstance
example (C : StabCode n) : Fintype C.Stabilizer := inferInstance
example (C : StabCode n) : Module (ZMod 2) (Additive C.Stabilizer) := inferInstance

example (C : StabCode n) (s : Finset ι) (f : ι → C.Stabilizer) : C.Stabilizer := C.prod s f
example (C : StabCode n) (s : Finset ι) (f : ι → C.Stabilizer) : PauliGroup_group n :=
  C.prodPauli s f

example [Fintype ι] (C : StabCode n) (P : C.Presentation ι) :
    (ι → ZMod 2) →ₗ[ZMod 2] Additive C.Stabilizer := P.coefficientLinearMap

example [Fintype ι] (C : StabCode n) (P : C.Presentation ι) :
    Function.Surjective P.coefficientLinearMap := P.coefficientLinearMap_surjective

example [Fintype ι] (C : StabCode n) (P : C.Presentation ι) (c d : ι → ZMod 2) :
    P.coefficientLinearMap (c + d) = P.coefficientLinearMap c + P.coefficientLinearMap d := by
  simp

example [Fintype ι] (C : StabCode n) (P : C.Presentation ι) (c d : ι → ZMod 2) :
    P.combination (c + d) = P.combination c * P.combination d := by
  simp

example (C : StabCode n) : Additive C.Stabilizer ≃ₗ[ZMod 2] C.stabSymplecticSpace :=
  C.binaryLinearEquiv

example (C : StabCode n) (σ : Equiv.Perm (Fin n)) :
    C.Stabilizer ≃* (C.reindex σ).Stabilizer := C.reindexStabilizer σ

example (C : StabCode n) (P : C.Presentation ι) (σ : Equiv.Perm (Fin n)) :
    (C.reindex σ).Presentation ι := P.reindexQubits σ

#check StabCode.ofSubgroup
#check StabCode.ofStabilizedGenerators
#check StabCode.Presentation.coefficientLinearMap
#check StabCode.mapStabilizerLinearEquiv
#check StabCode.Presentation.coefficientLinearMap_map
#check StabCode.reindex_reindex
#check StabCode.stabilizerCongr
