import LeanQEC.Stabilizer.CSS

noncomputable section

namespace Before

variable {n m k : ℕ} {ι : Type*}

-- 1. Construction: the old record asks the caller for both proofs.
def fromSubgroup (S : Subgroup (PauliGroup_group n))
    (hc : IsMulCommutative S) (hm : negIdPauli n ∉ S) : StabCode n :=
  ⟨S, hc, hm⟩

-- 2. Use the shortest existing generic member API.
theorem ambient_commute (C : StabCode n) (a b : PauliGroup_group n)
    (ha : a ∈ C.stabs) (hb : b ∈ C.stabs) : a * b = b * a := by
  letI : IsMulCommutative C.stabs := C.h_comm
  exact setLike_mul_comm ha hb

theorem subgroup_commute (C : StabCode n) (a b : C.stabs) : a * b = b * a := by
  letI : IsMulCommutative C.stabs := C.h_comm
  exact mul_comm' a b

-- 3. Configure a section once, then use generic finite-product algebra.
section Products

variable (C : StabCode n)
local instance : IsMulCommutative C.stabs := C.h_comm
local instance : CommGroup C.stabs := subgroupCarrierCommGroup C.stabs

theorem product_distrib (s : Finset ι) (f g : ι → C.stabs) :
    (∏ i ∈ s, f i * g i) = (∏ i ∈ s, f i) * ∏ i ∈ s, g i :=
  Finset.prod_mul_distrib

end Products

-- 4. Caller-defined generator combination, valid even for a redundant family.
def combination [Fintype ι] (C : StabCode n) (g : ι → C.stabs) (c : ι → ZMod 2) :
    C.stabs := by
  letI : IsMulCommutative C.stabs := C.h_comm
  letI : CommGroup C.stabs := subgroupCarrierCommGroup C.stabs
  exact ∏ i, if c i = 1 then g i else 1

theorem combination_stabilizes [Fintype ι] (C : StabCode n) (g : ι → C.stabs)
    (c : ι → ZMod 2) (ψ : PState n) (hψ : ψ ∈ C.space) :
    stabilizes ((combination C g c).val : 𝐔ₙ[n]) ψ :=
  (C.mem_space ψ).mp hψ _ (combination C g c).property

-- 5. Check a generating family, using the old closure theorem directly.
theorem mem_space (C : StabCode n) (g : ι → PauliGroup_group n)
    (hgen : Subgroup.closure (Set.range g) = C.stabs)
    (ψ : PState n) (hfix : ∀ i, stabilizes (g i : 𝐔ₙ[n]) ψ) : ψ ∈ C.space := by
  apply (C.mem_space_of_closure hgen ψ).mpr
  rintro s ⟨i, rfl⟩
  exact hfix i

-- 6. Convert the user's standard Commute facts to the old domain predicate.
theorem mem_normalizer (C : StabCode n) (g : ι → PauliGroup_group n)
    (hgen : Subgroup.closure (Set.range g) = C.stabs)
    (E : PauliGroup_group n) (hcomm : ∀ i, Commute E (g i)) :
    E ∈ C.normalizerGroup := by
  apply (C.mem_normalizerGroup_of_closure hgen E).mpr
  rintro s ⟨i, rfl⟩
  exact (commute_iff_commute E (g i)).mpr (hcomm i)

-- 7. Matrix multiplication was already directly supported by the old API.
theorem matrix_binary_image (B : BinSympMatrix k n) (hc : B.isCommuting)
    (c : Fin k → ZMod 2) :
    Pauli_toBinSympPauli (B.rowProduct hc c) =
      (B.X.transpose.mulVec c, B.Z.transpose.mulVec c) :=
  B.rowProduct_binaryImage hc c

-- 8. Turn the existing existence theorem into a chosen, reusable stabilizer.
def binaryLift (C : StabCode n) (v : C.stabSymplecticSpace) : C.stabs := by
  let h := (C.mem_stabilizerSpace_iff v.val).mp v.property
  exact ⟨h.choose, h.choose_spec.1⟩

theorem binaryLift_spec (C : StabCode n) (v : C.stabSymplecticSpace) :
    Pauli_toBinSympPauli (binaryLift C v).val = v.val :=
  ((C.mem_stabilizerSpace_iff v.val).mp v.property).choose_spec.2

theorem binaryLift_roundtrip (C : StabCode n) (s : C.stabs) :
    binaryLift C ⟨Pauli_toBinSympPauli s.val,
      (C.mem_stabilizerSpace_iff _).mpr ⟨s.val, s.property, rfl⟩⟩ = s := by
  apply Subtype.ext
  apply phi_injOn C (binaryLift C _).property s.property
  exact binaryLift_spec C _

-- 9. An ambient group equivalence must be packaged into a valid code.
def mapCode (C : StabCode n) (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) : StabCode m where
  stabs := C.stabs.map e.toMonoidHom
  h_comm := by
    letI : IsMulCommutative C.stabs := C.h_comm
    infer_instance
  h_minus := by
    rintro ⟨s, hs, he⟩
    apply C.h_minus
    have heq : s = negIdPauli n := e.injective (he.trans hneg.symm)
    simpa [heq] using hs

end Before
