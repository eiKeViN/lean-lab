import LeanQEC.Stabilizer.CSS

/-! User-side bridge assembled only from declarations available before the change. -/

noncomputable section

namespace BeforeLinear

variable {n : ℕ}

local instance (C : StabCode n) : IsMulCommutative C.stabs := C.h_comm
local instance (C : StabCode n) : CommGroup C.stabs := subgroupCarrierCommGroup C.stabs

def binaryHom (C : StabCode n) : C.stabs →* Multiplicative C.stabSymplecticSpace where
  toFun s := Multiplicative.ofAdd ⟨Pauli_toBinSympPauli s.val,
    (C.mem_stabilizerSpace_iff _).mpr ⟨s.val, s.property, rfl⟩⟩
  map_one' := congrArg Multiplicative.ofAdd (Subtype.ext Pauli_toBinSympPauli_one)
  map_mul' s t := congrArg Multiplicative.ofAdd
    (Subtype.ext (Pauli_to_BinSymp_correct s.val t.val))

theorem binaryHom_injective (C : StabCode n) : Function.Injective (binaryHom C) := by
  intro s t h
  apply Subtype.ext
  apply phi_injOn C s.property t.property
  exact congrArg (fun x : Multiplicative C.stabSymplecticSpace =>
    (Multiplicative.toAdd x).val) h

theorem binaryHom_surjective (C : StabCode n) : Function.Surjective (binaryHom C) := by
  intro x
  obtain ⟨s, hs, he⟩ := (C.mem_stabilizerSpace_iff _).mp (Multiplicative.toAdd x).property
  exact ⟨⟨s, hs⟩, congrArg Multiplicative.ofAdd (Subtype.ext he)⟩

def binaryEquiv (C : StabCode n) : C.stabs ≃* Multiplicative C.stabSymplecticSpace :=
  MulEquiv.ofBijective (binaryHom C) ⟨binaryHom_injective C, binaryHom_surjective C⟩

def binaryAddEquiv (C : StabCode n) : Additive C.stabs ≃+ C.stabSymplecticSpace :=
  MulEquiv.toAdditiveLeft (binaryEquiv C)

local instance (C : StabCode n) : Module (ZMod 2) (Additive C.stabs) :=
  (binaryAddEquiv C).module (ZMod 2)

def binaryLinearEquiv (C : StabCode n) : Additive C.stabs ≃ₗ[ZMod 2]
    C.stabSymplecticSpace := (binaryAddEquiv C).linearEquiv (ZMod 2)

theorem stabilizer_finrank (C : StabCode n) :
    Module.finrank (ZMod 2) (Additive C.stabs) = C.numGenerators :=
  (binaryLinearEquiv C).finrank_eq

end BeforeLinear
