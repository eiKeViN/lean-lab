import LeanQEC.Stabilizer.Basic

/-!
# Stable interfaces for stabilizer elements

`C.Stabilizer` keeps the code in the instance-search target while retaining the
original subgroup operations. `C.toPauli` and `C.toUnitary` expose structured
embeddings, with simplification lemmas for the usual algebraic operations.
-/

namespace StabCode

variable {n : ℕ}

/-- The standard carrier for algebra on a code's stabilizers. Intentionally a `def`. -/
def Stabilizer (C : StabCode n) : Type := C.stabs

instance instStabilizerCommGroup (C : StabCode n) : CommGroup C.Stabilizer :=
  C.instCommGroup

instance instStabilizerFinite (C : StabCode n) : Finite C.Stabilizer :=
  inferInstanceAs (Finite C.stabs)

noncomputable instance instStabilizerFintype (C : StabCode n) : Fintype C.Stabilizer :=
  inferInstanceAs (Fintype C.stabs)

noncomputable instance instStabilizerDecidableEq (C : StabCode n) :
    DecidableEq C.Stabilizer := Classical.decEq _

/-- The stable carrier uses precisely the existing subgroup data. -/
def stabilizerEquiv (C : StabCode n) : C.Stabilizer ≃* C.stabs :=
  MulEquiv.refl _

/-- The inclusion into the ambient Pauli group. -/
def toPauli (C : StabCode n) : C.Stabilizer →* PauliGroup_group n where
  toFun s := (s : C.stabs).val
  map_one' := rfl
  map_mul' _ _ := rfl

instance instStabilizerCoe (C : StabCode n) :
    CoeOut C.Stabilizer (PauliGroup_group n) := ⟨C.toPauli⟩

theorem toPauli_injective (C : StabCode n) : Function.Injective C.toPauli :=
  Subtype.val_injective

@[simp]
theorem stabilizer_mem (C : StabCode n) (s : C.Stabilizer) :
    (s : PauliGroup_group n) ∈ C.stabs := (s : C.stabs).property

/-- Regard an ambient member as a stabilizer, without exposing subtype construction. -/
def ofMem (C : StabCode n) (s : PauliGroup_group n) (hs : s ∈ C.stabs) :
    C.Stabilizer := ⟨s, hs⟩

@[simp]
theorem toPauli_ofMem (C : StabCode n) (s : PauliGroup_group n) (hs : s ∈ C.stabs) :
    C.toPauli (C.ofMem s hs) = s := rfl

@[simp]
theorem ofMem_toPauli (C : StabCode n) (s : C.Stabilizer) :
    C.ofMem (C.toPauli s) (C.stabilizer_mem s) = s := rfl

@[simp]
theorem coe_stabilizer_one (C : StabCode n) :
    ((1 : C.Stabilizer) : PauliGroup_group n) = 1 := rfl

@[simp]
theorem coe_stabilizer_mul (C : StabCode n) (s t : C.Stabilizer) :
    ((s * t : C.Stabilizer) : PauliGroup_group n) =
      (s : PauliGroup_group n) * (t : PauliGroup_group n) := rfl

@[simp]
theorem coe_stabilizer_inv (C : StabCode n) (s : C.Stabilizer) :
    ((s⁻¹ : C.Stabilizer) : PauliGroup_group n) = (s : PauliGroup_group n)⁻¹ := rfl

@[simp]
theorem coe_stabilizer_pow (C : StabCode n) (s : C.Stabilizer) (k : ℕ) :
    ((s ^ k : C.Stabilizer) : PauliGroup_group n) = (s : PauliGroup_group n) ^ k := rfl

@[simp]
theorem coe_stabilizer_list_prod (C : StabCode n) (l : List C.Stabilizer) :
    ((l.prod : C.Stabilizer) : PauliGroup_group n) =
      (l.map C.toPauli).prod :=
  map_list_prod C.toPauli l

/-- A finite unordered product, retaining stabilizer membership and algebraic structure. -/
def prod {ι : Type*} (C : StabCode n) (s : Finset ι) (f : ι → C.Stabilizer) :
    C.Stabilizer := ∏ i ∈ s, f i

/-- The ambient image of a finite stabilizer product. -/
def prodPauli {ι : Type*} (C : StabCode n) (s : Finset ι) (f : ι → C.Stabilizer) :
    PauliGroup_group n := C.toPauli (C.prod s f)

@[simp]
theorem toPauli_prod {ι : Type*} (C : StabCode n) (s : Finset ι)
    (f : ι → C.Stabilizer) : C.toPauli (C.prod s f) = C.prodPauli s f := rfl

@[simp]
theorem prod_mem {ι : Type*} (C : StabCode n) (s : Finset ι)
    (f : ι → C.Stabilizer) : C.toPauli (C.prod s f) ∈ C.stabs :=
  C.stabilizer_mem _

@[simp]
theorem prodPauli_mem {ι : Type*} (C : StabCode n) (s : Finset ι)
    (f : ι → C.Stabilizer) : C.prodPauli s f ∈ C.stabs := C.stabilizer_mem _

/-- The inclusion into unitary operators; matrix users need not traverse nested subtypes. -/
def toUnitary (C : StabCode n) : C.Stabilizer →* 𝐔ₙ[n] where
  toFun s := (C.toPauli s : 𝐔ₙ[n])
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem toUnitary_ofMem (C : StabCode n) (s : PauliGroup_group n) (hs : s ∈ C.stabs) :
    C.toUnitary (C.ofMem s hs) = (s : 𝐔ₙ[n]) := rfl

theorem stabilizes_of_mem_space (C : StabCode n) (s : C.Stabilizer)
    {ψ : PState n} (hψ : ψ ∈ C.space) : stabilizes (C.toUnitary s) ψ :=
  (C.mem_space ψ).mp hψ _ (C.stabilizer_mem s)

@[simp]
theorem card_stabilizer (C : StabCode n) :
    Fintype.card C.Stabilizer = 2 ^ C.numGenerators := by
  rw [← Nat.card_eq_fintype_card]
  exact C.card_stabs

end StabCode
