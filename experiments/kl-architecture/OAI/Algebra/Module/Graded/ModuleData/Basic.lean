import Mathlib
import OAI.Algebra.Module.Graded.Generators

/-! Semantic home: OAI.Algebra.Module.Graded.ModuleData.Basic. Source spans: GradedModules:6, GradedModules:7, GradedModules:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

/-- Actual finite nonnegatively graded modules; no character or duality property
is folded into this data. -/
structure ModuleData (𝓐 : ℤ → Submodule k A) where
  obj : ModuleCat.{max ua um} A
  kModule : Module k obj
  tower : IsScalarTower k A obj
  piece : ℤ → Submodule k obj
  decomposition : DirectSum.Decomposition piece
  graded : SetLike.GradedSMul 𝓐 piece
  nonneg : ∀ n < 0, piece n = ⊥
  finite : Module.Finite A obj

attribute [instance] ModuleData.kModule ModuleData.tower ModuleData.decomposition
  ModuleData.graded ModuleData.finite

instance _root_.OAI.KLInvariance.Graded.instCoeSortModuleDataType {𝓐 : ℤ → Submodule k A} : CoeSort (ModuleData.{uk,ua,um} 𝓐) (Type (max ua um)) :=
  ⟨fun M => M.obj⟩

namespace ModuleData
variable {𝓐 : ℤ → Submodule k A}

instance _root_.OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj (M : ModuleData.{uk,ua,um} 𝓐) : AddCommGroup M := inferInstanceAs (AddCommGroup M.obj)
instance _root_.OAI.KLInvariance.Graded.ModuleData.instModuleCarrierObj (M : ModuleData.{uk,ua,um} 𝓐) : Module A M := inferInstanceAs (Module A M.obj)

structure Hom (M N : ModuleData.{uk,ua,um} 𝓐) where
  map : M →ₗ[A] N
  graded : ∀ n m, m ∈ M.piece n → map m ∈ N.piece n

noncomputable def sub [IsNoetherianRing A] (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A S
  kModule := inferInstance
  tower := inferInstance
  piece := subPiece M.piece S
  decomposition := (sub_isInternal M.piece S hS).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => subPiece_eq_bot M.piece S n (M.nonneg n hn)
  finite := inferInstance

noncomputable def quotient (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (M ⧸ S)
  kModule := inferInstance
  tower := inferInstance
  piece := quotientPiece M.piece S
  decomposition := (quotient_isInternal M.piece S hS).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => quotientPiece_eq_bot M.piece S n (M.nonneg n hn)
  finite := inferInstance

noncomputable def pi {ι : Type um} [Fintype ι] (M : ι → ModuleData.{uk,ua,um} 𝓐) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (∀ i, M i)
  kModule := inferInstance
  tower := inferInstance
  piece := piPiece fun i => (M i).piece
  decomposition := (pi_isInternal (fun i => (M i).piece)).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => piPiece_eq_bot (fun i => (M i).piece) n (fun i => (M i).nonneg n hn)
  finite := inferInstance

noncomputable def kernel [IsNoetherianRing A] {M N : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M N) : ModuleData.{uk,ua,um} 𝓐 :=
  sub M f.map.ker (kernel_homogeneous M.piece N.piece f.map 0
    (by simpa using f.graded))

noncomputable def range [IsNoetherianRing A] {M N : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M N) : ModuleData.{uk,ua,um} 𝓐 :=
  sub N f.map.range (range_homogeneous M.piece N.piece f.map 0
    (by simpa using f.graded))

noncomputable def scalarQuotient (M : ModuleData.{uk,ua,um} 𝓐)
    (a : A) (d : ℤ) (ha : a ∈ 𝓐 d) : ModuleData.{uk,ua,um} 𝓐 :=
  quotient M (LinearMap.range (LinearMap.lsmul A M a))
    (scalar_range_homogeneous 𝓐 M.piece d a ha)

 def projection {ι : Type um} [Fintype ι] (M : ι → ModuleData.{uk,ua,um} 𝓐) (i : ι) :
    Hom (pi M) (M i) where
  map := LinearMap.proj i
  graded := fun _ _ hm => hm i (Set.mem_univ i)

 def quotientMap (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    Hom M (quotient M S hS) where
  map := S.mkQ
  graded := by
    intro n m hm
    change S.mkQ m ∈ quotientPiece M.piece S n
    exact Submodule.mem_map.mpr ⟨m,hm,rfl⟩

 def subtype [IsNoetherianRing A] (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    Hom (sub M S hS) M where
  map := S.subtype
  graded := fun _ _ hm => hm


 def Hom.comp {M N P : ModuleData.{uk,ua,um} 𝓐} (g : Hom N P) (f : Hom M N) :
    Hom M P where
  map := g.map.comp f.map
  graded := fun n m hm => g.graded n _ (f.graded n m hm)

 def Hom.id (M : ModuleData.{uk,ua,um} 𝓐) : Hom M M where
  map := LinearMap.id
  graded := fun _ _ h => h

 theorem Hom.component {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) (n : ℤ) (m : M) :
    component N.piece n (f.map m) = f.map (component M.piece n m) := by
  simpa using map_component M.piece N.piece f.map 0 (by simpa using f.graded) n m

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]

noncomputable def free {ι : Type (max ua um)} [Fintype ι]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) (d : ι → ℤ) (hd : ∀ i, 0 ≤ d i) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (ι → A)
  kModule := inferInstance
  tower := inferInstance
  piece := shiftedPiece 𝓐 d
  decomposition := (shifted_isInternal 𝓐 d).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => shiftedPiece_eq_bot 𝓐 hneg d n (fun i => lt_of_lt_of_le hn (hd i))
  finite := inferInstance

 structure MinimalCover (M : ModuleData.{uk,ua,um} 𝓐) where
  source : ModuleData.{uk,ua,um} 𝓐
  free : Module.Free A source
  hom : Hom source M
  surjective : Function.Surjective hom.map
  minimal : LinearMap.ker hom.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A source)

 theorem exists_minimalCover
    (hneg : ∀ n < 0, 𝓐 n = ⊥)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)
    (M : ModuleData.{uk,ua,um} 𝓐) : Nonempty (MinimalCover M) := by
  classical
  obtain ⟨ι,hι,v,d,hd,hspan,hind⟩ :=
    exists_homogeneous_minimal_generators 𝓐 M.piece 0 M.nonneg hscalar
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  have hd0 (i : ι) : 0 ≤ d i := by
    by_contra h
    have hbot := M.nonneg (d i) (lt_of_not_ge h)
    have hv0 : v i = 0 := by simpa only [hbot, Submodule.mem_bot] using hd i
    have hz := hind.ne_zero i
    exact hz (by rw [hv0,map_zero])
  let F := free hneg d hd0
  let f : Hom F M :=
    { map := Fintype.linearCombination A v
      graded := by
        intro n c hc
        apply Submodule.sum_mem
        intro i _
        simpa using SetLike.GradedSMul.smul_mem (hc i) (hd i) }
  have hfree : Module.Free A F := inferInstanceAs (Module.Free A (ι → A))
  refine ⟨⟨F,hfree,f,?_,?_⟩⟩
  · intro m
    exact (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  · exact kernel_minimal_cover _ hscalar v hind

end ModuleData
end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section

 theorem shift_isInternal (M : ModuleData.{uk,ua,um} 𝓐) (d : ℤ) :
    DirectSum.IsInternal (fun n => M.piece (n-d)) := by
  classical
  apply internal_of_components _ (fun n => component M.piece (n-d))
  · intro n m
    exact (DirectSum.decompose M.piece m (n-d)).property
  · intro n m hm
    exact DirectSum.decompose_of_mem_same M.piece hm
  · intro n j m hnj hm
    apply DirectSum.decompose_of_mem_ne M.piece hm
    omega
  · intro m
    refine ⟨(DirectSum.decompose M.piece m).support.image (fun n => n+d),?_⟩
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    simp only [add_sub_cancel_right]
    exact DirectSum.sum_support_decompose M.piece m

namespace ModuleData
 def shift (M : ModuleData.{uk,ua,um} 𝓐) (d : ℕ) : ModuleData.{uk,ua,um} 𝓐 where
  obj := M.obj
  kModule := M.kModule
  tower := M.tower
  piece n := M.piece (n-d)
  decomposition := (shift_isInternal M d).chooseDecomposition
  graded := ⟨by
    intro i j a m ha hm
    change a • m ∈ M.piece (i+j-d)
    have hh : a • m ∈ M.piece (i+(j-(d:ℤ))) := SetLike.GradedSMul.smul_mem ha hm
    convert hh using 1
    congr 1
    omega⟩
  nonneg n hn := M.nonneg (n-d) (by omega)
  finite := M.finite

 def Hom.shift {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) (d : ℕ) :
    Hom (M.shift d) (N.shift d) where
  map := f.map
  graded n m hm := f.graded (n-d) m hm

 def prod (M N : ModuleData.{uk,ua,um} 𝓐) : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (M × N)
  kModule := inferInstance
  tower := inferInstance
  piece n := (M.piece n).prod (N.piece n)
  decomposition := (show DirectSum.IsInternal (fun n => (M.piece n).prod (N.piece n)) from by
    apply internal_of_components _ (fun n =>
      (component M.piece n).prodMap (component N.piece n))
    · intro n m
      exact ⟨(DirectSum.decompose M.piece m.1 n).property,
        (DirectSum.decompose N.piece m.2 n).property⟩
    · intro n m hm
      exact Prod.ext (DirectSum.decompose_of_mem_same M.piece hm.1)
        (DirectSum.decompose_of_mem_same N.piece hm.2)
    · intro i j m hij hm
      exact Prod.ext (DirectSum.decompose_of_mem_ne M.piece hm.1 (Ne.symm hij))
        (DirectSum.decompose_of_mem_ne N.piece hm.2 (Ne.symm hij))
    · intro m
      classical
      refine ⟨(DirectSum.decompose M.piece m.1).support ∪ (DirectSum.decompose N.piece m.2).support,?_⟩
      apply Prod.ext
      · change (∑ n ∈ _, (component M.piece n).prodMap (component N.piece n) m).1=m.1
        rw [Prod.fst_sum]
        rw [← Finset.sum_subset Finset.subset_union_left]
        · exact DirectSum.sum_support_decompose M.piece m.1
        · intro n _ hn
          have hh : (DirectSum.decompose M.piece m.1) n=0 := DFinsupp.notMem_support_iff.mp hn
          exact congrArg (fun z : M.piece n => (z : M)) hh
      · change (∑ n ∈ _, (component M.piece n).prodMap (component N.piece n) m).2=m.2
        rw [Prod.snd_sum]
        rw [← Finset.sum_subset Finset.subset_union_right]
        · exact DirectSum.sum_support_decompose N.piece m.2
        · intro n _ hn
          have hh : (DirectSum.decompose N.piece m.2) n=0 := DFinsupp.notMem_support_iff.mp hn
          exact congrArg (fun z : N.piece n => (z : N)) hh).chooseDecomposition
  graded := ⟨by
    intro i j a m ha hm
    exact ⟨SetLike.GradedSMul.smul_mem ha hm.1,SetLike.GradedSMul.smul_mem ha hm.2⟩⟩
  nonneg n hn := by simp [M.nonneg n hn,N.nonneg n hn]
  finite := inferInstance

 def Hom.prodMap {M N P Q : ModuleData.{uk,ua,um} 𝓐} (f : Hom M P) (g : Hom N Q) :
    Hom (M.prod N) (P.prod Q) where
  map := f.map.prodMap g.map
  graded n _ hm := ⟨f.graded n _ hm.1,g.graded n _ hm.2⟩

end ModuleData
end
end KLInvariance.Graded
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

 theorem Hom.mem_of_map_mem {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N)
    (hi : Function.Injective f.map) (n : ℤ) (m : M) (hm : f.map m ∈ N.piece n) :
    m ∈ M.piece n := by
  have h : f.map (Graded.component M.piece n m) = f.map m := by
    rw [← f.component]
    exact DirectSum.decompose_of_mem_same N.piece hm
  rw [← hi h]
  exact (DirectSum.decompose M.piece m n).property

 theorem Hom.homogeneous_preimage {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N)
    (hs : Function.Surjective f.map) (n : ℤ) (v : N) (hv : v ∈ N.piece n) :
    ∃ m : M, m ∈ M.piece n ∧ f.map m = v := by
  obtain ⟨m,rfl⟩ := hs v
  refine ⟨Graded.component M.piece n m,(DirectSum.decompose M.piece m n).property,?_⟩
  rw [← f.component]
  exact DirectSum.decompose_of_mem_same N.piece hv

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

include hneg in
 theorem exists_hom_lift_of_basis [Nontrivial A] {F N P : ModuleData.{uk,ua,um} 𝓐}
    {ι : Type (max ua um)} [Fintype ι] (b : Module.Basis ι A F)
    (d : ι → ℤ) (hd : ∀ i, b i ∈ F.piece (d i))
    (f : Hom N P) (hs : Function.Surjective f.map) (g : Hom F P) :
    ∃ l : Hom F N, f.map.comp l.map = g.map := by
  classical
  have hd0 (i : ι) : 0 ≤ d i := by
    by_contra h
    have hz : b i = 0 := by simpa [F.nonneg (d i) (lt_of_not_ge h)] using hd i
    exact b.ne_zero i hz
  let H := free.{uk,ua,um} hneg d hd0
  let e : Hom H F :=
    { map := b.equivFun.symm.toLinearMap
      graded := by
        intro n v hv
        change ι → A at v
        change v ∈ shiftedPiece 𝓐 d n at hv
        change b.equivFun.symm v ∈ F.piece n
        rw [b.equivFun_symm_apply]
        apply Submodule.sum_mem
        intro i _
        simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i) }
  have he : Function.Injective e.map := b.equivFun.symm.injective
  have hcoeff (n : ℤ) (v : F) (hv : v ∈ F.piece n) :
      b.equivFun v ∈ shiftedPiece 𝓐 d n := by
    apply e.mem_of_map_mem he n
    change b.equivFun.symm (b.equivFun v) ∈ F.piece n
    simpa only [LinearEquiv.symm_apply_apply] using hv
  have hlifts (i : ι) : ∃ v : N, v ∈ N.piece (d i) ∧ f.map v = g.map (b i) :=
    f.homogeneous_preimage hs (d i) _ (g.graded (d i) _ (hd i))
  choose v hvg hvf using hlifts
  let l : Hom F N :=
    { map := b.constr A v
      graded := by
        intro n m hm
        rw [b.constr_apply]
        apply Submodule.sum_mem
        intro i _
        simpa using SetLike.GradedSMul.smul_mem (hcoeff n m hm i) (hvg i) }
  refine ⟨l,?_⟩
  apply b.ext
  intro i
  change f.map ((b.constr A v) (b i)) = g.map (b i)
  rw [b.constr_basis,hvf]

variable [IsDomain A] [IsNoetherianRing A]
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)

include hneg hzero in
 theorem exists_hom_lift {F N P : ModuleData.{uk,ua,um} 𝓐}
    [Module.Free A F] (f : Hom N P) (hs : Function.Surjective f.map) (g : Hom F P) :
    ∃ l : Hom F N, f.map.comp l.map = g.map := by
  classical
  obtain ⟨ι,hι,b,hd⟩ := exists_homogeneous_basis_connected 𝓐 F.piece hneg hzero 0 F.nonneg
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  choose d hd using hd
  exact exists_hom_lift_of_basis hneg b d hd f hs g

omit [IsDomain A] [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] hneg hzero in
 theorem Hom.bijective_of_mod_positive {M : ModuleData.{uk,ua,um} 𝓐} (f : Hom M M)
    (hm : ∀ m, m-f.map m ∈ positiveIdeal 𝓐 • (⊤ : Submodule A M)) :
    Function.Bijective f.map := by
  have hr : LinearMap.range f.map = ⊤ :=
    eq_top_of_positive_smul_sup 𝓐 M.piece 0 M.nonneg (LinearMap.range f.map)
      (range_homogeneous M.piece M.piece f.map 0 (by simpa using f.graded))
      (by
        apply top_unique
        intro m _
        exact Submodule.mem_sup.mpr ⟨f.map m,⟨m,rfl⟩,m-f.map m,hm m,add_sub_cancel _ _⟩)
  have hs := LinearMap.range_eq_top.mp hr
  exact ⟨IsNoetherian.injective_of_surjective_endomorphism f.map hs,hs⟩

include hneg hzero in
 theorem MinimalCover.equiv {M : ModuleData.{uk,ua,um} 𝓐} (C D : MinimalCover M) :
    ∃ e : C.source ≃ₗ[A] D.source,
      (∀ n v, v ∈ C.source.piece n → e v ∈ D.source.piece n) ∧
      D.hom.map.comp e.toLinearMap = C.hom.map := by
  let := C.free
  let := D.free
  obtain ⟨f,hf⟩ := exists_hom_lift hneg hzero D.hom D.surjective C.hom
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective D.hom
  have hfa (v : C.source) : D.hom.map (f.map v)=C.hom.map v := LinearMap.congr_fun hf v
  have hga (v : D.source) : C.hom.map (g.map v)=D.hom.map v := LinearMap.congr_fun hg v
  have hgc : Function.Bijective (g.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply C.minimal
    change C.hom.map (m-g.map (f.map m))=0
    rw [map_sub,hga,hfa,sub_self]
  have hfd : Function.Bijective (f.comp g).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply D.minimal
    change D.hom.map (m-f.map (g.map m))=0
    rw [map_sub,hfa,hga,sub_self]
  have hfb : Function.Bijective f.map :=
    ⟨Function.Injective.of_comp hgc.1,Function.Surjective.of_comp hfd.2⟩
  exact ⟨LinearEquiv.ofBijective f.map hfb,f.graded,hf⟩

end KLInvariance.Graded.ModuleData
end

end OAI
