import LeanQEC.Stabilizer.API

noncomputable section

namespace After

variable {n m k : ℕ} {ι : Type*}

-- 1. Construction from the independent validity condition.
def fromSubgroup (S : Subgroup (PauliGroup_group n))
    (hm : negIdPauli n ∉ S) : StabCode n :=
  StabCode.ofSubgroup S hm

-- 2. Direct ambient and typed-carrier entry points.
theorem ambient_commute (C : StabCode n) (a b : PauliGroup_group n)
    (ha : a ∈ C.stabs) (hb : b ∈ C.stabs) : a * b = b * a :=
  C.mul_comm ha hb

theorem subgroup_commute (C : StabCode n) (a b : C.Stabilizer) : a * b = b * a :=
  mul_comm a b

-- 3. No user-local instances are needed for finite-product algebra.
theorem product_distrib (C : StabCode n) (s : Finset ι) (f g : ι → C.Stabilizer) :
    (∏ i ∈ s, f i * g i) = (∏ i ∈ s, f i) * ∏ i ∈ s, g i :=
  Finset.prod_mul_distrib

-- 4. Any family already has the required algebraic structure.
def combination [Fintype ι] (C : StabCode n) (g : ι → C.Stabilizer)
    (c : ι → ZMod 2) : C.Stabilizer :=
  ∏ i, if c i = 1 then g i else 1

theorem combination_stabilizes [Fintype ι] (C : StabCode n) (P : C.Presentation ι)
    (c : ι → ZMod 2) (ψ : PState n) (hψ : ψ ∈ C.space) :
    stabilizes (C.toUnitary (P.combination c)) ψ :=
  P.combination_stabilizes c hψ

-- 5. A presentation retains the generation theorem.
theorem mem_space (C : StabCode n) (P : C.Presentation ι)
    (ψ : PState n) (hfix : ∀ i, stabilizes (C.toUnitary (P.generator i)) ψ) :
    ψ ∈ C.space :=
  (P.mem_space_iff ψ).mpr hfix

-- 6. It also exposes the standard mathlib Commute predicate.
theorem mem_normalizer (C : StabCode n) (P : C.Presentation ι)
    (E : PauliGroup_group n) (hcomm : ∀ i, Commute E (C.toPauli (P.generator i))) :
    E ∈ C.normalizerGroup :=
  (P.mem_normalizer_iff E).mpr hcomm

-- 7. The same one-line matrix result, accessed through the chosen presentation.
theorem matrix_binary_image (B : BinSympMatrix k n)
    (hm : negIdPauli n ∉ B.pauliSubgroup) (c : Fin k → ZMod 2) :
    Pauli_toBinSympPauli
      ((StabCode.ofBinSympMatrix B hm).toPauli ((B.presentation hm).combination c)) =
      (B.X.transpose.mulVec c, B.Z.transpose.mulVec c) :=
  B.presentation_combination_binaryImage hm c

-- 8. Choose a signed stabilizer and simplify the round trip.
def binaryLift (C : StabCode n) (v : C.stabSymplecticSpace) : C.Stabilizer :=
  C.ofBinary v

theorem binaryLift_spec (C : StabCode n) (v : C.stabSymplecticSpace) :
    C.toBinary (binaryLift C v) = v := by
  simp [binaryLift]

theorem binaryLift_roundtrip (C : StabCode n) (s : C.Stabilizer) :
    C.ofBinary (C.toBinary s) = s := by simp

-- 9. The mathematical map data is sufficient at the call site.
def mapCode (C : StabCode n) (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) : StabCode m :=
  C.map e hneg

theorem map_stabilizer_mul (C : StabCode n)
    (e : PauliGroup_group n ≃* PauliGroup_group m)
    (hneg : e (negIdPauli n) = negIdPauli m) (s t : C.Stabilizer) :
    C.mapStabilizer e hneg (s * t) =
      C.mapStabilizer e hneg s * C.mapStabilizer e hneg t :=
  map_mul _ _ _

-- 10. Reuse linear algebra and a distance bound through the supplied equivalences.
theorem stabilizer_finrank (C : StabCode n) :
    Module.finrank (ZMod 2) (Additive C.Stabilizer) = C.numGenerators :=
  C.binaryLinearEquiv.finrank_eq

theorem reindex_distance_bound (C : StabCode n) (σ : Equiv.Perm (Fin n))
    (d : ℕ) (hd : d ≤ C.distance) : d ≤ (C.reindex σ).distance := by
  simpa using hd

end After
