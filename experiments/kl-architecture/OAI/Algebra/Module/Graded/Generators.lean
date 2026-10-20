import Mathlib
import OAI.Algebra.Module.Graded.Components

/-! Semantic home: OAI.Algebra.Module.Graded.Generators. Source spans: GradedModules:4, GradedModules:1, GradedModules:3, GradedModules:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]

 theorem internal_of_components
    (𝓜 : ℤ → Submodule k M) (p : ℤ → M →ₗ[k] M)
    (hmem : ∀ i m, p i m ∈ 𝓜 i)
    (hsame : ∀ i m, m ∈ 𝓜 i → p i m = m)
    (hne : ∀ i j m, i ≠ j → m ∈ 𝓜 j → p i m = 0)
    (hsum : ∀ m, ∃ s : Finset ℤ, ∑ i ∈ s, p i m = m) :
    DirectSum.IsInternal 𝓜 := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
    intro s v hv hz i hi
    have hp := congrArg (p i) hz
    rw [map_sum, map_zero, Finset.sum_eq_single_of_mem i hi] at hp
    · simpa only [hsame i _ (hv i hi)] using hp
    · intro j hj hji
      exact hne i j _ (Ne.symm hji) (hv j hj)
  · apply top_unique
    intro m _
    obtain ⟨s,hs⟩ := hsum m
    rw [← hs]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup 𝓜 i) (hmem i m)

 theorem image_isInternal
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    (f : M →ₗ[k] N) (hf : Function.Surjective f)
    (hker : ∀ i m, f m = 0 → f (component 𝓜 i m) = 0) :
    DirectSum.IsInternal (fun i => (𝓜 i).map f) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
    intro s v hv hz i hi
    choose w hw hfw using fun j : s => (Submodule.mem_map.mp (hv j.val j.property))
    let w' : ℤ → M := fun j => if hj : j ∈ s then w ⟨j,hj⟩ else 0
    have hw' (j) : w' j ∈ 𝓜 j := by
      dsimp [w']; split_ifs with hj
      · exact hw ⟨j,hj⟩
      · exact Submodule.zero_mem _
    have hfw' (j) (hj : j ∈ s) : f (w' j) = v j := by simpa [w',hj] using hfw ⟨j,hj⟩
    have hsum : f (∑ j ∈ s, w' j) = 0 := by
      rw [map_sum]
      exact (Finset.sum_congr rfl hfw').trans hz
    have hc := hker i _ hsum
    rw [map_sum, Finset.sum_eq_single_of_mem i hi] at hc
    · change f (DirectSum.decompose 𝓜 (w' i) i : M) = 0 at hc
      rw [DirectSum.decompose_of_mem_same 𝓜 (hw' i), hfw' i hi] at hc
      exact hc
    · intro j _ hji
      exact DirectSum.decompose_of_mem_ne 𝓜 (hw' j) hji
  · apply top_unique
    intro n _
    obtain ⟨m,rfl⟩ := hf n
    rw [← DirectSum.sum_support_decompose 𝓜 m, map_sum]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun i => (𝓜 i).map f) i)
      (Submodule.mem_map.mpr ⟨_,(DirectSum.decompose 𝓜 m i).property,rfl⟩)

variable {A : Type ua} [CommRing A] [Algebra k A]
  [Module A M] [IsScalarTower k A M]

 def subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) : ℤ → Submodule k S :=
  fun i => (𝓜 i).comap (S.subtype.restrictScalars k)

 theorem sub_isInternal
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    (S : Submodule A M)
    (hS : ∀ i m, m ∈ S → component 𝓜 i m ∈ S) :
    DirectSum.IsInternal (subPiece 𝓜 S) := by
  classical
  let p : ℤ → S →ₗ[k] S := fun i =>
    LinearMap.codRestrict (S.restrictScalars k)
      ((component 𝓜 i).comp (S.subtype.restrictScalars k)) (fun m => hS i m m.property)
  apply internal_of_components (subPiece 𝓜 S) p
  · intro i m
    exact (DirectSum.decompose 𝓜 (m : M) i).property
  · intro i m hm
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_same 𝓜 hm
  · intro i j m hij hm
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_ne 𝓜 hm hij.symm
  · intro m
    refine ⟨(DirectSum.decompose 𝓜 (m : M)).support, ?_⟩
    apply Subtype.ext
    change (∑ i ∈ (DirectSum.decompose 𝓜 (m : M)).support, p i m : S).val = (m : M)
    rw [Submodule.coe_sum]
    exact DirectSum.sum_support_decompose 𝓜 (m : M)

 def quotientPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) :
    ℤ → Submodule k (M ⧸ S) := fun i => (𝓜 i).map (S.mkQ.restrictScalars k)

 theorem quotient_isInternal
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    (S : Submodule A M)
    (hS : ∀ i m, m ∈ S → component 𝓜 i m ∈ S) :
    DirectSum.IsInternal (quotientPiece 𝓜 S) := by
  apply image_isInternal 𝓜 (S.mkQ.restrictScalars k) S.mkQ_surjective
  intro i m hm
  apply (Submodule.Quotient.mk_eq_zero S).mpr
  exact hS i m ((Submodule.Quotient.mk_eq_zero S).mp hm)

 instance sub_gradedSMul
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [SetLike.GradedSMul 𝓐 𝓜] (S : Submodule A M) :
    SetLike.GradedSMul 𝓐 (subPiece 𝓜 S) where
  smul_mem := by
    intro i j a m ha hm
    change a • (m : M) ∈ 𝓜 (i+j)
    exact SetLike.GradedSMul.smul_mem ha (show (m : M) ∈ 𝓜 j from hm)

 instance quotient_gradedSMul
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [SetLike.GradedSMul 𝓐 𝓜] (S : Submodule A M) :
    SetLike.GradedSMul 𝓐 (quotientPiece 𝓜 S) where
  smul_mem := by
    intro i j a m ha hm
    obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
    exact Submodule.mem_map.mpr ⟨a • v,SetLike.GradedSMul.smul_mem ha hv,map_smul S.mkQ a v⟩

 theorem subPiece_eq_bot (𝓜 : ℤ → Submodule k M) (S : Submodule A M)
    (i : ℤ) (h : 𝓜 i = ⊥) : subPiece 𝓜 S i = ⊥ := by
  apply le_antisymm _ bot_le
  intro m hm
  apply Subtype.ext
  exact (Submodule.mem_bot k).mp (h ▸ hm)

 theorem quotientPiece_eq_bot (𝓜 : ℤ → Submodule k M) (S : Submodule A M)
    (i : ℤ) (h : 𝓜 i = ⊥) : quotientPiece 𝓜 S i = ⊥ := by
  simp [quotientPiece,h]

 def shiftedPiece {ι : Type*} (𝓐 : ℤ → Submodule k A) (d : ι → ℤ) :
    ℤ → Submodule k (ι → A) := fun n =>
  { carrier := {v | ∀ i, v i ∈ 𝓐 (n-d i)}
    zero_mem' := fun _ => Submodule.zero_mem _
    add_mem' := fun hx hy i => Submodule.add_mem _ (hx i) (hy i)
    smul_mem' := fun c _ hx i => Submodule.smul_mem _ c (hx i) }

 theorem shifted_isInternal {ι : Type*} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐] (d : ι → ℤ) :
    DirectSum.IsInternal (shiftedPiece 𝓐 d) := by
  classical
  let p : ℤ → (ι → A) →ₗ[k] (ι → A) := fun n =>
    LinearMap.pi fun i => (component 𝓐 (n-d i)).comp (LinearMap.proj i)
  apply internal_of_components (shiftedPiece 𝓐 d) p
  · intro n v i
    exact (DirectSum.decompose 𝓐 (v i) (n-d i)).property
  · intro n v hv
    funext i
    exact DirectSum.decompose_of_mem_same 𝓐 (hv i)
  · intro n j v hnj hv
    funext i
    apply DirectSum.decompose_of_mem_ne 𝓐 (hv i)
    omega
  · intro v
    let s : ι → Finset ℤ := fun i =>
      (DirectSum.decompose 𝓐 (v i)).support.image (fun n => n+d i)
    refine ⟨Finset.univ.biUnion s, ?_⟩
    funext i
    change (∑ n ∈ Finset.univ.biUnion s, p n v) i = v i
    rw [Finset.sum_apply]
    have hsub : s i ⊆ Finset.univ.biUnion s :=
      Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hout (n : ℤ) (_ : n ∈ Finset.univ.biUnion s) (hn : n ∉ s i) :
        p n v i = 0 := by
      have hni : n-d i ∉ (DirectSum.decompose 𝓐 (v i)).support := by
        intro hni
        exact hn (Finset.mem_image.mpr ⟨n-d i,hni,by omega⟩)
      have hz := DFinsupp.notMem_support_iff.mp hni
      exact congrArg Subtype.val hz
    rw [← Finset.sum_subset hsub hout]
    change ∑ n ∈ (DirectSum.decompose 𝓐 (v i)).support.image (fun n => n+d i),
      component 𝓐 (n-d i) (v i) = v i
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    simp only [add_sub_cancel_right]
    exact DirectSum.sum_support_decompose 𝓐 (v i)

 instance shifted_gradedSMul {ι : Type*}
    (𝓐 : ℤ → Submodule k A) [SetLike.GradedMonoid 𝓐] (d : ι → ℤ) :
    SetLike.GradedSMul 𝓐 (shiftedPiece 𝓐 d) where
  smul_mem := by
    intro i j a m ha hm t
    have h := SetLike.GradedMul.mul_mem ha (hm t)
    simpa [sub_eq_add_neg,add_assoc] using h

 theorem shiftedPiece_eq_bot {ι : Type*}
    (𝓐 : ℤ → Submodule k A) (hneg : ∀ i < 0, 𝓐 i = ⊥) (d : ι → ℤ)
    (n : ℤ) (h : ∀ i, n < d i) : shiftedPiece 𝓐 d n = ⊥ := by
  apply le_antisymm _ bot_le
  intro m hm
  funext i
  have hi := hm i
  rw [hneg _ (by have := h i; omega)] at hi
  exact hi

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
open scoped Pointwise
universe uk ua um
variable {k : Type uk} {A : Type ua} {M : Type um} [Field k] [CommRing A] [klPreservedInstance9 : Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [klPreservedInstance8 : IsScalarTower k A M]

include klPreservedInstance8 in
/-- Graded Nakayama in its generation form. The submodule is closed under
actual homogeneous components, rather than assumed to be the whole module. -/
theorem eq_top_of_positive_smul_sup
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (N : Submodule A M) (hN : ∀ n m, m ∈ N → (DirectSum.decompose 𝓜 m n : M) ∈ N)
    (hgen : N ⊔ positiveIdeal 𝓐 • (⊤ : Submodule A M) = ⊤) : N = ⊤ := by
  have _ := klPreservedInstance8
  classical
  have hlow : ∀ j < d₀, ∀ m ∈ 𝓜 j, m ∈ N := by
    intro j hj m hm
    have hm0 : m = 0 := by simpa [hbound j hj] using hm
    simp [hm0]
  have hind : ∀ n : ℕ, ∀ m ∈ 𝓜 (d₀+n), m ∈ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      let p := component 𝓜 (d₀+n)
      have hsmul (i : ℤ) (hi : 0 < i) (a : A) (ha : a ∈ 𝓐 i) :
          ∀ m : M, p (a • m) ∈ N := by
        intro m
        refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ m
        · simp
        · intro j m
          by_cases hj : j < d₀+n
          · have hm : (m : M) ∈ N := by
              by_cases hj₀ : j < d₀
              · exact hlow j hj₀ m m.property
              · have heq : d₀ + (j-d₀).toNat = j := by omega
                exact ih (j-d₀).toNat (by omega) m (heq.symm ▸ m.property)
            exact hN _ _ (N.smul_mem a hm)
          · have hdeg : i+j ≠ d₀+n := by omega
            have ham : a • (m : M) ∈ 𝓜 (i+j) :=
              SetLike.GradedSMul.smul_mem ha m.property
            have heq : p (a • (m : M)) = 0 :=
              DirectSum.decompose_of_mem_ne 𝓜 ham hdeg
            simp [heq]
        · intro x y hx hy
          simpa only [smul_add, map_add] using N.add_mem hx hy
      let J : Ideal A :=
        { carrier := {a | ∀ m : M, p (a • m) ∈ N}
          zero_mem' := by simp [N.zero_mem]
          add_mem' := by
            intro a b ha hb m
            simpa only [add_smul, map_add] using N.add_mem (ha m) (hb m)
          smul_mem' := by
            intro r a ha m
            change p ((r*a) • m) ∈ N
            rw [mul_comm r a, mul_smul]
            exact ha (r • m) }
      have hIJ : positiveIdeal 𝓐 ≤ J := by
        apply Ideal.span_le.mpr
        rintro a ⟨i,hi,ha⟩
        exact hsmul i hi a ha
      have hp : ∀ m : M, p m ∈ N := by
        intro m
        have hm : m ∈ N ⊔ positiveIdeal 𝓐 • (⊤ : Submodule A M) := by
          rw [hgen]; trivial
        obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hm
        rw [map_add]
        apply N.add_mem (hN _ _ hx)
        refine Submodule.smul_induction_on hy ?_ ?_
        · intro a ha z _; exact hIJ ha z
        · intro z w hz hw; simpa only [map_add] using N.add_mem hz hw
      intro m hm
      have hcomp : p m=m := DirectSum.decompose_of_mem_same 𝓜 hm
      exact hcomp ▸ hp m
  have homogeneous_mem (j : ℤ) (m : M) (hm : m ∈ 𝓜 j) : m ∈ N := by
    by_cases hj : j < d₀
    · exact hlow j hj m hm
    · have heq : d₀ + (j-d₀).toNat = j := by omega
      exact hind (j-d₀).toNat m (heq.symm ▸ hm)
  apply top_unique
  intro m _
  exact DirectSum.Decomposition.inductionOn 𝓜 N.zero_mem
    (fun m => homogeneous_mem _ m m.property)
    (fun _ _ hx hy => N.add_mem hx hy) m

include klPreservedInstance8 in
/-- Projection of a scalar multiple of a homogeneous vector. -/
theorem component_smul_homogeneous
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] (a : A) (m : M) (d n : ℤ) (hm : m ∈ 𝓜 d) :
    component 𝓜 n (a • m) = component 𝓐 (n-d) a • m := by
  have _ := klPreservedInstance8
  classical
  refine DirectSum.Decomposition.inductionOn 𝓐 ?_ ?_ ?_ a
  · simp
  · intro i a
    by_cases hi : i = n-d
    · have hsum : i+d = n := by omega
      have ham : (a : A) • m ∈ 𝓜 n := hsum ▸
        SetLike.GradedSMul.smul_mem a.property hm
      rw [show component 𝓜 n ((a : A) • m) = (a : A) • m from
        DirectSum.decompose_of_mem_same 𝓜 ham]
      rw [show component 𝓐 (n-d) (a : A) = (a : A) from
        DirectSum.decompose_of_mem_same 𝓐 (hi ▸ a.property)]
    · have hsum : i+d ≠ n := by omega
      rw [show component 𝓜 n ((a : A) • m) = 0 from
        DirectSum.decompose_of_mem_ne 𝓜
          (SetLike.GradedSMul.smul_mem a.property hm) hsum,
        show component 𝓐 (n-d) (a : A) = 0 from
        DirectSum.decompose_of_mem_ne 𝓐 a.property hi, zero_smul]
  · intro a b ha hb
    simp only [add_smul, map_add, ha, hb]

include klPreservedInstance9 klPreservedInstance8 in
/-- Finite generation can be made homogeneous using the actual finite
support decomposition of each generator. -/
theorem exists_finite_homogeneous_generators
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜] [Module.Finite A M] :
    ∃ t : Finset M, Submodule.span A (t : Set M) = ⊤ ∧
      ∀ m ∈ t, ∃ d : ℤ, m ∈ 𝓜 d := by
  have _ := klPreservedInstance9
  have _ := klPreservedInstance8
  classical
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let t : Finset M := s.biUnion fun m =>
    (DirectSum.decompose 𝓜 m).support.image fun j => (DirectSum.decompose 𝓜 m j : M)
  refine ⟨t, ?_, ?_⟩
  · apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro m hm
    rw [← DirectSum.sum_support_decompose 𝓜 m]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨m,hm,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩
  · intro m hm
    obtain ⟨a,ha,hma⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hma
    exact ⟨j,(DirectSum.decompose 𝓜 a j).property⟩

/-- The span of finitely many homogeneous vectors is closed under each
component, as required for graded Nakayama. -/
theorem homogeneous_span_components {ι : Type*} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] (v : ι → M) (d : ι → ℤ)
    (hv : ∀ i, v i ∈ 𝓜 (d i)) (n : ℤ) (m : M)
    (hm : m ∈ Submodule.span A (Set.range v)) :
    component 𝓜 n m ∈ Submodule.span A (Set.range v) := by
  classical
  obtain ⟨c,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hm
  rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [component_smul_homogeneous 𝓐 𝓜 _ _ (d i) n (hv i)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- Reduction of a scalar modulo the augmentation ideal gives precisely
its scalar-field action on the reduced module. -/
theorem quotient_smul_of_scalar_mod (I : Ideal A) (a : A) (c : k)
    (hac : a-algebraMap k A c ∈ I) (m : M) :
    (I • (⊤ : Submodule A M)).mkQ (a • m) =
      c • (I • (⊤ : Submodule A M)).mkQ m := by
  let J := I • (⊤ : Submodule A M)
  have hz : J.mkQ ((a-algebraMap k A c) • m) = 0 :=
    (Submodule.Quotient.mk_eq_zero J).mpr
      (Submodule.smul_mem_smul hac (Submodule.mem_top : m ∈ (⊤ : Submodule A M)))
  rw [sub_smul, map_sub] at hz
  have heq := sub_eq_zero.mp hz
  calc
    _ = J.mkQ (algebraMap k A c • m) := heq
    _ = algebraMap k A c • J.mkQ m := map_smul J.mkQ _ _
    _ = c • J.mkQ m := IsScalarTower.algebraMap_smul A c (J.mkQ m)

/-- A finite free cover of a projective module, minimal at any proper
augmentation ideal of a noetherian domain, is injective. The determinant
form of Nakayama removes the complementary torsion-free kernel. -/
theorem linearIndependent_of_projective_cover {ι : Type*} [Fintype ι]
    [IsDomain A] [IsNoetherianRing A] [Module.Projective A M]
    (I : Ideal A) (hI : I ≠ ⊤)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ I)
    (v : ι → M) (hspan : Submodule.span A (Set.range v) = ⊤)
    (hind : LinearIndependent k
      (fun i => (I • (⊤ : Submodule A M)).mkQ (v i))) :
    LinearIndependent A v := by
  classical
  let J := I • (⊤ : Submodule A M)
  let f := Fintype.linearCombination A v
  have hsurj : Function.Surjective f := by
    intro m
    exact (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : M →ₗ[A] M) hsurj
  have hmin : LinearMap.ker f ≤ I • (⊤ : Submodule A (ι → A)) := by
    intro a ha
    choose c hc using fun i => hscalar (a i)
    have heq : ∑ i, c i • J.mkQ (v i) = 0 := by
      calc
        _ = J.mkQ (∑ i, a i • v i) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact (quotient_smul_of_scalar_mod I (a i) (c i) (hc i) (v i)).symm
        _ = 0 := congrArg J.mkQ (LinearMap.mem_ker.mp ha) |>.trans (map_zero _)
    have hc0 : ∀ i, c i=0 := (Fintype.linearIndependent_iff.mp hind) c heq
    have hai (i : ι) : a i ∈ I := by simpa [hc0 i] using hc i
    have hrebuild : a = ∑ i, a i • Pi.single i (1 : A) := by
      ext j
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [hrebuild]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem_smul (hai i) Submodule.mem_top
  have htop := positive_smul_kernel_of_minimal_split I f s hs hmin
  have hfg : (⊤ : Submodule A (LinearMap.ker f)).FG := IsNoetherian.noetherian _
  obtain ⟨r,hr,hkill⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    I (⊤ : Submodule A (LinearMap.ker f)) hfg (by rw [htop])
  have hr0 : r ≠ 0 := by
    intro heq
    have hone : (1 : A) ∈ I := by simpa [heq] using I.neg_mem hr
    exact hI (Ideal.eq_top_of_isUnit_mem I hone isUnit_one)
  have hker : LinearMap.ker f = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    have hz : r • (⟨a,ha⟩ : LinearMap.ker f) = 0 := hkill _ Submodule.mem_top
    have ha0 : (⟨a,ha⟩ : LinearMap.ker f) = 0 := (smul_eq_zero.mp hz).resolve_left hr0
    exact congrArg Subtype.val ha0
  exact linearIndependent_iff_injective_fintypeLinearCombination.mpr
    (LinearMap.ker_eq_bot.mp hker)

/-- Images of any finite generating family span the augmentation quotient
as a vector space over the degree-zero field. -/
theorem quotient_span_of_scalar_mod {ι : Type*} [Fintype ι]
    (I : Ideal A) (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ I)
    (v : ι → M) (hv : Submodule.span A (Set.range v) = ⊤) :
    Submodule.span k (Set.range (fun i => (I • (⊤ : Submodule A M)).mkQ (v i))) = ⊤ := by
  classical
  let J := I • (⊤ : Submodule A M)
  apply top_unique
  intro z _
  obtain ⟨m,rfl⟩ := J.mkQ_surjective z
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (hv ▸ Submodule.mem_top :
    m ∈ Submodule.span A (Set.range v))
  choose c hc using fun i => hscalar (a i)
  apply (Submodule.mem_span_range_iff_exists_fun k).mpr
  refine ⟨c, ?_⟩
  calc
    _ = J.mkQ (∑ i, a i • v i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (quotient_smul_of_scalar_mod I (a i) (c i) (hc i) (v i)).symm
    _ = J.mkQ m := congrArg J.mkQ ha


theorem exists_homogeneous_basis_of_scalar_mod
    [IsDomain A] [IsNoetherianRing A] [Module.Projective A M] [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (hproper : positiveIdeal 𝓐 ≠ ⊤)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐) :
    ∃ (ι : Type um), Finite ι ∧ ∃ b : Module.Basis ι A M,
      ∀ i, ∃ d : ℤ, b i ∈ 𝓜 d := by
  classical
  obtain ⟨t,ht,hth⟩ := exists_finite_homogeneous_generators (A := A) 𝓜
  let v : t → M := Subtype.val
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    simpa [v] using ht
  let I := positiveIdeal 𝓐
  let J := I • (⊤ : Submodule A M)
  have hq := quotient_span_of_scalar_mod I hscalar v hv
  obtain ⟨ι,a,ha,hsp,hli⟩ := exists_linearIndependent' k (fun i => J.mkQ (v i))
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let w : ι → M := v ∘ a
  have hw : ∀ i, ∃ d : ℤ, w i ∈ 𝓜 d := fun i => hth _ (a i).property
  choose d hd using hw
  have hqw : Submodule.span k (Set.range (fun i => J.mkQ (w i))) = ⊤ := hsp.trans hq
  let N := Submodule.span A (Set.range w)
  have hN : ∀ n m, m ∈ N → (DirectSum.decompose 𝓜 m n : M) ∈ N :=
    homogeneous_span_components 𝓐 𝓜 w d hd
  have hgen : N ⊔ I • (⊤ : Submodule A M) = ⊤ := by
    apply top_unique
    intro m _
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp
      (hqw ▸ Submodule.mem_top : J.mkQ m ∈
        Submodule.span k (Set.range (fun i => J.mkQ (w i))))
    let z : M := ∑ i, algebraMap k A (c i) • w i
    have hz : z ∈ N := by
      apply Submodule.sum_mem
      intro i _
      exact N.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have hqz : J.mkQ z = J.mkQ m := by
      change J.mkQ (∑ i, algebraMap k A (c i) • w i) = J.mkQ m
      rw [map_sum]
      convert hc using 1
      apply Finset.sum_congr rfl
      intro i _
      exact (map_smul J.mkQ _ _).trans (IsScalarTower.algebraMap_smul A (c i) _)
    have hdiff : m-z ∈ J := by
      apply (Submodule.Quotient.mk_eq_zero J).mp
      change J.mkQ (m-z)=0
      rw [map_sub,hqz,sub_self]
    exact Submodule.mem_sup.mpr ⟨z,hz,m-z,hdiff,by abel⟩
  have hspan : N=⊤ := eq_top_of_positive_smul_sup 𝓐 𝓜 d₀ hbound N hN hgen
  have hliA : LinearIndependent A w :=
    linearIndependent_of_projective_cover I hproper hscalar w hspan hli
  refine ⟨ι,inferInstance,Module.Basis.mk hliA hspan.ge,?_⟩
  intro i
  exact ⟨d i, by simpa only [Module.Basis.mk_apply] using hd i⟩

/-- The augmentation for a nonnegatively supported integer grading is
actual degree-zero projection. -/
noncomputable def nonnegativeAugmentation
    (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
    [SetLike.GradedMonoid 𝓐] (hneg : ∀ j < 0, 𝓐 j = ⊥) : A →+* A where
  toFun := component 𝓐 0
  map_zero' := map_zero _
  map_one' := DirectSum.decompose_of_mem_same 𝓐 SetLike.GradedOne.one_mem
  map_add' := map_add _
  map_mul' := by
    intro a b
    refine DirectSum.Decomposition.inductionOn 𝓐 ?_ ?_ ?_ a
    · simp
    · intro i a
      refine DirectSum.Decomposition.inductionOn 𝓐 ?_ ?_ ?_ b
      · simp
      · intro j b
        by_cases hi : i < 0
        · have ha : (a : A) = 0 := by simpa [hneg i hi] using a.property
          simp [ha]
        by_cases hj : j < 0
        · have hb : (b : A) = 0 := by simpa [hneg j hj] using b.property
          simp [hb]
        by_cases hij : i+j=0
        · have hi0 : i=0 := by omega
          have hj0 : j=0 := by omega
          have hab := SetLike.GradedMul.mul_mem a.property b.property
          change component 𝓐 0 ((a:A)*(b:A)) = component 𝓐 0 (a:A) * component 𝓐 0 (b:A)
          rw [show component 𝓐 0 ((a:A)*(b:A)) = (a:A)*(b:A) from
            DirectSum.decompose_of_mem_same 𝓐 (hij ▸ hab),
            show component 𝓐 0 (a:A) = a from
              DirectSum.decompose_of_mem_same 𝓐 (hi0 ▸ a.property),
            show component 𝓐 0 (b:A) = b from
              DirectSum.decompose_of_mem_same 𝓐 (hj0 ▸ b.property)]
        · change component 𝓐 0 ((a:A)*(b:A)) = component 𝓐 0 (a:A) * component 𝓐 0 (b:A)
          rw [show component 𝓐 0 ((a:A)*(b:A))=0 from
            DirectSum.decompose_of_mem_ne 𝓐
              (SetLike.GradedMul.mul_mem a.property b.property) hij]
          by_cases hi0 : i=0
          · have hj0 : j≠0 := by omega
            rw [show component 𝓐 0 (b:A)=0 from
              DirectSum.decompose_of_mem_ne 𝓐 b.property hj0,mul_zero]
          · rw [show component 𝓐 0 (a:A)=0 from
              DirectSum.decompose_of_mem_ne 𝓐 a.property hi0,zero_mul]
      · intro b c hb hc
        simp only [mul_add,map_add,hb,hc]
    · intro a c ha hc
      simp only [add_mul,map_add,ha,hc]

/-- The positive ideal is exactly the augmentation kernel. -/
theorem positiveIdeal_eq_augmentation_ker
    (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
    [SetLike.GradedMonoid 𝓐] (hneg : ∀ j < 0, 𝓐 j = ⊥) :
    positiveIdeal 𝓐 = RingHom.ker (nonnegativeAugmentation 𝓐 hneg) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨i,hi,ha⟩
    exact DirectSum.decompose_of_mem_ne 𝓐 ha (by omega)
  · intro a ha
    rw [← DirectSum.sum_support_decompose 𝓐 a]
    apply Ideal.sum_mem
    intro j hj
    by_cases hjpos : 0 < j
    · exact Ideal.subset_span ⟨j,hjpos,(DirectSum.decompose 𝓐 a j).property⟩
    have hz : (DirectSum.decompose 𝓐 a j : A)=0 := by
      by_cases hjzero : j=0
      · subst j; exact ha
      · have hjneg : j<0 := by omega
        simpa [hneg j hjneg] using (DirectSum.decompose 𝓐 a j).property
    rw [hz]
    exact Ideal.zero_mem _


theorem exists_homogeneous_basis_connected
    [IsDomain A] [IsNoetherianRing A] [Module.Projective A M] [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]
    (hneg : ∀ j < 0, 𝓐 j = ⊥)
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥) :
    ∃ (ι : Type um), Finite ι ∧ ∃ b : Module.Basis ι A M,
      ∀ i, ∃ d : ℤ, b i ∈ 𝓜 d := by
  apply exists_homogeneous_basis_of_scalar_mod 𝓐 𝓜 d₀ hbound
  · rw [positiveIdeal_eq_augmentation_ker 𝓐 hneg]
    exact RingHom.ker_ne_top _
  · intro a
    obtain ⟨c,hc⟩ := hzero _ (DirectSum.decompose 𝓐 a 0).property
    refine ⟨c,?_⟩
    rw [positiveIdeal_eq_augmentation_ker 𝓐 hneg]
    change component 𝓐 0 (a-algebraMap k A c)=0
    rw [map_sub,hc]
    rw [show component 𝓐 0 (DirectSum.decompose 𝓐 a 0 : A) =
      (DirectSum.decompose 𝓐 a 0 : A) from
      DirectSum.decompose_of_mem_same 𝓐 (DirectSum.decompose 𝓐 a 0).property]
    exact sub_self _

/-- The actual polynomial grading, with each variable in degree one, on
integer degrees as used for shifted stalks. -/
abbrev polynomialGrading (k : Type*) [Field k] (σ : Type*) :=
  MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => (1 : ℤ))

noncomputable instance polynomialGrading_decomposition (k : Type*) [Field k] (σ : Type*) :
    DirectSum.Decomposition (polynomialGrading k σ) :=
  MvPolynomial.weightedDecomposition k (fun _ : σ => (1 : ℤ))

instance polynomialGrading_monoid (k : Type*) [Field k] (σ : Type*) :
    SetLike.GradedMonoid (polynomialGrading k σ) :=
  MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

theorem polynomialGrading_negative (k : Type*) [Field k] (σ : Type*)
    (j : ℤ) (hj : j < 0) : polynomialGrading k σ j = ⊥ := by
  classical
  apply eq_bot_iff.mpr
  intro p hp
  change p=0
  apply MvPolynomial.ext
  intro d
  by_contra hd
  have heq := hp (show p.coeff d≠0 by simpa using hd)
  have hn : 0 ≤ Finsupp.weight (fun _ : σ => (1 : ℤ)) d := by
    simp only [Finsupp.weight_apply,Finsupp.sum]
    exact Finset.sum_nonneg fun i _ => nsmul_nonneg (by norm_num) _
  omega

theorem polynomialGrading_zero (k : Type*) [Field k] (σ : Type*)
    (p : MvPolynomial σ k) (hp : p ∈ polynomialGrading k σ 0) :
    ∃ c : k, algebraMap k (MvPolynomial σ k) c=p := by
  classical
  refine ⟨p.coeff 0,?_⟩
  apply MvPolynomial.ext
  intro d
  by_cases hd : d=0
  · subst d; simp
  · have hc : p.coeff d=0 := by
      by_contra hc
      have heq := hp hc
      obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hd
      have hb := Finsupp.le_weight_of_ne_zero (M := ℤ)
        (w := fun _ : σ => (1 : ℤ)) (fun _ => by norm_num)
        (show d i≠0 by simpa using hi)
      omega
    simp [MvPolynomial.coeff_C,Ne.symm hd,hc]


theorem exists_homogeneous_basis_polynomial {σ : Type*} [Finite σ]
    [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]
    [Module.Projective (MvPolynomial σ k) M] [Module.Finite (MvPolynomial σ k) M]
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥) :
    ∃ (ι : Type um), Finite ι ∧ ∃ b : Module.Basis ι (MvPolynomial σ k) M,
      ∀ i, ∃ d : ℤ, b i ∈ 𝓜 d := by
  exact exists_homogeneous_basis_connected (polynomialGrading k σ) 𝓜
    (polynomialGrading_negative k σ) (polynomialGrading_zero k σ) d₀ hbound

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

theorem exists_homogeneous_minimal_generators
    [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐) :
    ∃ (ι : Type um), Finite ι ∧ ∃ (v : ι → M) (d : ι → ℤ),
      (∀ i, v i ∈ 𝓜 (d i)) ∧ Submodule.span A (Set.range v) = ⊤ ∧
      LinearIndependent k (fun i => (positiveIdeal 𝓐 • (⊤ : Submodule A M)).mkQ (v i)) := by
  classical
  obtain ⟨t,ht,hth⟩ := exists_finite_homogeneous_generators (A := A) 𝓜
  let v : t → M := Subtype.val
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    simpa [v] using ht
  let I := positiveIdeal 𝓐
  let J := I • (⊤ : Submodule A M)
  have hq := quotient_span_of_scalar_mod I hscalar v hv
  obtain ⟨ι,a,ha,hsp,hli⟩ := exists_linearIndependent' k (fun i => J.mkQ (v i))
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let w : ι → M := v ∘ a
  have hw : ∀ i, ∃ d : ℤ, w i ∈ 𝓜 d := fun i => hth _ (a i).property
  choose d hd using hw
  have hqw : Submodule.span k (Set.range (fun i => J.mkQ (w i))) = ⊤ := hsp.trans hq
  let N := Submodule.span A (Set.range w)
  have hN : ∀ n m, m ∈ N → (DirectSum.decompose 𝓜 m n : M) ∈ N :=
    homogeneous_span_components 𝓐 𝓜 w d hd
  have hgen : N ⊔ I • (⊤ : Submodule A M) = ⊤ := by
    apply top_unique
    intro m _
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp
      (hqw ▸ Submodule.mem_top : J.mkQ m ∈
        Submodule.span k (Set.range (fun i => J.mkQ (w i))))
    let z : M := ∑ i, algebraMap k A (c i) • w i
    have hz : z ∈ N := by
      apply Submodule.sum_mem
      intro i _
      exact N.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have hqz : J.mkQ z = J.mkQ m := by
      change J.mkQ (∑ i, algebraMap k A (c i) • w i) = J.mkQ m
      rw [map_sum]
      convert hc using 1
      apply Finset.sum_congr rfl
      intro i _
      exact (map_smul J.mkQ _ _).trans (IsScalarTower.algebraMap_smul A (c i) _)
    have hdiff : m-z ∈ J := by
      apply (Submodule.Quotient.mk_eq_zero J).mp
      change J.mkQ (m-z)=0
      rw [map_sub,hqz,sub_self]
    exact Submodule.mem_sup.mpr ⟨z,hz,m-z,hdiff,by abel⟩
  have hspan : N=⊤ := eq_top_of_positive_smul_sup 𝓐 𝓜 d₀ hbound N hN hgen
  exact ⟨ι,inferInstance,w,d,hd,hspan,hli⟩

 theorem kernel_minimal_cover (I : Ideal A)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ I)
    {ι : Type*} [Fintype ι] (v : ι → M)
    (hind : LinearIndependent k (fun i => (I • (⊤ : Submodule A M)).mkQ (v i))) :
    LinearMap.ker (Fintype.linearCombination A v) ≤ I • (⊤ : Submodule A (ι → A)) := by
  classical
  intro f hf
  let J := I • (⊤ : Submodule A M)
  choose c hc using fun i => hscalar (f i)
  have hz : ∑ i, c i • J.mkQ (v i) = 0 := by
    have hm : ∑ i, f i • v i = 0 := LinearMap.mem_ker.mp hf
    have hq := congrArg J.mkQ hm
    rw [map_sum,map_zero] at hq
    convert hq using 1
    apply Finset.sum_congr rfl
    intro i _
    exact (quotient_smul_of_scalar_mod I (f i) (c i) (hc i) (v i)).symm
  have hc0 : ∀ i, c i = 0 := (Fintype.linearIndependent_iff.mp hind) c hz
  have hfi (i : ι) : f i ∈ I := by simpa [hc0 i] using hc i
  have he : f = ∑ i, f i • Pi.single i (1 : A) := by
    ext i
    simp [Pi.single_apply]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem_smul (hfi i) Submodule.mem_top

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk ua um un ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem map_component
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 (i+d)) (n : ℤ) (m : M) :
    component 𝓝 n (f m) = f (component 𝓜 (n-d) m) := by
  classical
  refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ m
  · simp
  · intro j v
    by_cases h : j+d=n
    · have h' : n-d=j := by omega
      change (DirectSum.decompose 𝓝 (f (v : M)) n : N) =
        f (DirectSum.decompose 𝓜 (v : M) (n-d) : M)
      rw [← h, DirectSum.decompose_of_mem_same 𝓝 (hf j v v.property),
        show j+d-d=j by omega, DirectSum.decompose_of_mem_same 𝓜 v.property]
    · have h' : j ≠ n-d := by omega
      change (DirectSum.decompose 𝓝 (f (v : M)) n : N) =
        f (DirectSum.decompose 𝓜 (v : M) (n-d) : M)
      rw [DirectSum.decompose_of_mem_ne 𝓝 (hf j v v.property) h,
        DirectSum.decompose_of_mem_ne 𝓜 v.property h', map_zero]
  · intro x y hx hy
    simp only [map_add,hx,hy]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem kernel_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 (i+d)) :
    ∀ n m, m ∈ LinearMap.ker f → component 𝓜 n m ∈ LinearMap.ker f := by
  intro n m hm
  change f (component 𝓜 n m)=0
  have h := map_component 𝓜 𝓝 f d hf (n+d) m
  simpa [LinearMap.mem_ker.mp hm] using h.symm

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem range_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 (i+d)) :
    ∀ n m, m ∈ LinearMap.range f → component 𝓝 n m ∈ LinearMap.range f := by
  rintro n _ ⟨m,rfl⟩
  exact ⟨component 𝓜 (n-d) m,(map_component 𝓜 𝓝 f d hf n m).symm⟩

omit [IsScalarTower k A M] in
 theorem component_homogeneous_smul
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d : ℤ) (a : A) (ha : a ∈ 𝓐 d) (n : ℤ) (m : M) :
    component 𝓜 n (a • m) = a • component 𝓜 (n-d) m := by
  apply map_component 𝓜 𝓜 (LinearMap.lsmul A M a) d
  intro i v hv
  simpa [add_comm] using SetLike.GradedSMul.smul_mem ha hv

omit [IsScalarTower k A M] in
 theorem scalar_range_homogeneous
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d : ℤ) (a : A) (ha : a ∈ 𝓐 d) :
    ∀ n m, m ∈ LinearMap.range (LinearMap.lsmul A M a) →
      component 𝓜 n m ∈ LinearMap.range (LinearMap.lsmul A M a) := by
  apply range_homogeneous 𝓜 𝓜 (LinearMap.lsmul A M a) d
  intro i v hv
  simpa [add_comm] using SetLike.GradedSMul.smul_mem ha hv

 theorem exists_graded_minimal_free_cover
    [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐) :
    ∃ (ι : Type um), Finite ι ∧ ∃ (d : ι → ℤ) (f : (ι → A) →ₗ[A] M),
      Function.Surjective f ∧
      (∀ n v, v ∈ shiftedPiece 𝓐 d n → f v ∈ 𝓜 n) ∧
      LinearMap.ker f ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (ι → A)) := by
  classical
  obtain ⟨ι,hι,v,d,hd,hspan,hind⟩ :=
    exists_homogeneous_minimal_generators 𝓐 𝓜 d₀ hbound hscalar
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨ι,hι,d,Fintype.linearCombination A v,?_,?_,?_⟩
  · intro m
    exact (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  · intro n c hc
    apply Submodule.sum_mem
    intro i _
    simpa using SetLike.GradedSMul.smul_mem (hc i) (hd i)
  · exact kernel_minimal_cover _ hscalar v hind

section Pi
variable {ι : Type ui} {P : ι → Type um}
  [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]

 def piPiece (𝓟 : ∀ i, ℤ → Submodule k (P i)) : ℤ → Submodule k (∀ i, P i) :=
  fun n => Submodule.pi Set.univ (fun i => 𝓟 i n)

 theorem pi_isInternal [Fintype ι]
    (𝓟 : ∀ i, ℤ → Submodule k (P i)) [∀ i, DirectSum.Decomposition (𝓟 i)] :
    DirectSum.IsInternal (piPiece 𝓟) := by
  classical
  let p : ℤ → (∀ i, P i) →ₗ[k] (∀ i, P i) := fun n =>
    LinearMap.pi fun i => (component (𝓟 i) n).comp (LinearMap.proj i)
  apply internal_of_components (piPiece 𝓟) p
  · intro n v i _
    exact (DirectSum.decompose (𝓟 i) (v i) n).property
  · intro n v hv
    funext i
    exact DirectSum.decompose_of_mem_same (𝓟 i) (hv i (Set.mem_univ i))
  · intro n j v hnj hv
    funext i
    exact DirectSum.decompose_of_mem_ne (𝓟 i) (hv i (Set.mem_univ i)) hnj.symm
  · intro v
    let s : ι → Finset ℤ := fun i => (DirectSum.decompose (𝓟 i) (v i)).support
    refine ⟨Finset.univ.biUnion s, ?_⟩
    funext i
    rw [Finset.sum_apply]
    have hsub : s i ⊆ Finset.univ.biUnion s :=
      Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hout (n : ℤ) (_ : n ∈ Finset.univ.biUnion s) (hn : n ∉ s i) :
        p n v i = 0 := by
      change n ∉ (DirectSum.decompose (𝓟 i) (v i)).support at hn
      have hz := DFinsupp.notMem_support_iff.mp hn
      exact congrArg Subtype.val hz
    rw [← Finset.sum_subset hsub hout]
    exact DirectSum.sum_support_decompose (𝓟 i) (v i)

 instance pi_gradedSMul [∀ i, Module A (P i)] [∀ i, IsScalarTower k A (P i)]
    (𝓐 : ℤ → Submodule k A) (𝓟 : ∀ i, ℤ → Submodule k (P i))
    [∀ i, SetLike.GradedSMul 𝓐 (𝓟 i)] : SetLike.GradedSMul 𝓐 (piPiece 𝓟) where
  smul_mem := by
    intro n j a v ha hv i hi
    exact SetLike.GradedSMul.smul_mem ha (hv i hi)

 theorem piPiece_eq_bot
    (𝓟 : ∀ i, ℤ → Submodule k (P i)) (n : ℤ) (h : ∀ i, 𝓟 i n = ⊥) :
    piPiece 𝓟 n = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  funext i
  have hi : v i ∈ 𝓟 i n := hv i (Set.mem_univ i)
  rw [h i] at hi
  exact hi

end Pi
end KLInvariance.Graded
end

end OAI
