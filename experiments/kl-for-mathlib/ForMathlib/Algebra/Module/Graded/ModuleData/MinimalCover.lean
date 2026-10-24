module
public import Mathlib
public import ForMathlib.Algebra.Module.Cover.Local
public import ForMathlib.Algebra.Module.Graded.ModuleData.Equality
public import ForMathlib.Algebra.Module.Graded.NonnegativeBasis

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover. Source spans: SheafMorphisms:15, SheafMorphisms:19, SheafMorphisms:22, SheafMorphisms:25, SheafMorphisms:8, SheafMorphisms:17.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} (M : ModuleData.{uk,ua,um} 𝓐)

 theorem idempotent_eq_zero (f : Hom M M)
    (hi : ∀ v, f.map (f.map v) = f.map v)
    (hm : LinearMap.range f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A M)) :
    f.map = 0 := by
  have hker : LinearMap.ker f.map = ⊤ :=
    eq_top_of_positive_smul_sup 𝓐 M.piece 0 M.nonneg (LinearMap.ker f.map)
      (by
        intro n m h
        change f.map (component M.piece n m) = 0
        rw [← f.component, LinearMap.mem_ker.mp h, map_zero])
      (by
        apply top_unique
        intro m _
        apply Submodule.mem_sup.mpr
        refine ⟨m-f.map m,?_,f.map m,hm ⟨m,rfl⟩,sub_add_cancel _ _⟩
        change f.map (m-f.map m) = 0
        rw [map_sub,hi,sub_self])
  exact LinearMap.ker_eq_top.mp hker

end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem MinimalCover.bijective_of_boundaryIso {M : ModuleData.{uk,ua,um} 𝓐}
    (C : MinimalCover M) (f : Hom C.source C.source) (g : M ≃ₗ[A] M)
    (hg : ∀ n v, v ∈ M.piece n → g v ∈ M.piece n)
    (hcomm : ∀ v, C.hom.map (f.map v) = g (C.hom.map v)) :
    Function.Bijective f.map := by
  let gh : Hom M M := ⟨g.toLinearMap,hg⟩
  let gi : Hom M M :=
    { map := g.symm.toLinearMap
      graded := by
        intro n v hv
        apply gh.mem_of_map_mem g.injective n
        change g (g.symm v) ∈ M.piece n
        simpa only [LinearEquiv.apply_symm_apply] using hv }
  let := C.free
  obtain ⟨l,hl⟩ := exists_hom_lift hneg hzero C.hom C.surjective (gi.comp C.hom)
  have hla (v : C.source) : C.hom.map (l.map v) = g.symm (C.hom.map v) :=
    LinearMap.congr_fun hl v
  have hfl : Function.Bijective (f.comp l).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-f.map (l.map v))=0
    rw [map_sub,hcomm,hla,LinearEquiv.apply_symm_apply,sub_self]
  have hlf : Function.Bijective (l.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-l.map (f.map v))=0
    rw [map_sub,hla,hcomm,LinearEquiv.symm_apply_apply,sub_self]
  exact ⟨Function.Injective.of_comp hlf.1,Function.Surjective.of_comp hfl.2⟩

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData.Hom
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M N : ModuleData.{uk,ua,um} 𝓐}
noncomputable section

 @[expose] def inverse (f : Hom M N) (hf : Function.Bijective f.map) : Hom N M where
  map := (LinearEquiv.ofBijective f.map hf).symm.toLinearMap
  graded := by
    intro n v hv
    apply f.mem_of_map_mem hf.1 n
    change (LinearEquiv.ofBijective f.map hf) ((LinearEquiv.ofBijective f.map hf).symm v) ∈ N.piece n
    simpa only [LinearEquiv.apply_symm_apply] using hv

 theorem map_inverse (f : Hom M N) (hf : Function.Bijective f.map) (v : N) :
    f.map ((f.inverse hf).map v)=v := (LinearEquiv.ofBijective f.map hf).apply_symm_apply v

 theorem inverse_map (f : Hom M N) (hf : Function.Bijective f.map) (v : M) :
    (f.inverse hf).map (f.map v)=v := (LinearEquiv.ofBijective f.map hf).symm_apply_apply v

end
end KLInvariance.Graded.ModuleData.Hom
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem exists_minimalCover_split {T F : ModuleData.{uk,ua,um} 𝓐}
    (C : MinimalCover T) [Module.Free A F]
    (f : Hom F T) (hf : Function.Surjective f.map) :
    ∃ (g : Hom F C.source) (h : Hom C.source F),
      C.hom.map.comp g.map = f.map ∧ g.map.comp h.map = LinearMap.id := by
  let : Module.Free A C.source := C.free
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective f
  obtain ⟨t,ht⟩ := exists_hom_lift hneg hzero f hf C.hom
  have hgt : Function.Bijective (g.comp t).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-g.map (t.map v))=0
    rw [map_sub,← LinearMap.comp_apply,hg,← LinearMap.comp_apply,ht,sub_self]
  refine ⟨g,t.comp ((g.comp t).inverse hgt),hg,?_⟩
  ext v
  exact (g.comp t).map_inverse hgt v

 @[expose] def Hom.splitEquiv {F C : ModuleData.{uk,ua,um} 𝓐}
    (g : Hom F C) (h : Hom C F) (hgh : g.map.comp h.map = LinearMap.id) :
    F ≃ₗ[A] C × kernel g := LocalCover.splitEquiv g.map h.map hgh

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] [IsDomain A] in
 theorem Hom.splitEquiv_graded {F C : ModuleData.{uk,ua,um} 𝓐}
    (g : Hom F C) (h : Hom C F) (hgh : g.map.comp h.map = LinearMap.id)
    (n : ℤ) (v : F) (hv : v ∈ F.piece n) :
    g.splitEquiv h hgh v ∈ (prod C (kernel g)).piece n := by
  constructor
  · change (LocalCover.splitEquiv g.map h.map hgh v).1 ∈ C.piece n
    exact (LocalCover.splitEquiv_apply_fst g.map h.map hgh v).symm ▸ g.graded n v hv
  · change ((LocalCover.splitEquiv g.map h.map hgh v).2 : F) ∈ F.piece n
    rw [LocalCover.splitEquiv_apply_snd_coe]
    exact Submodule.sub_mem _ hv (h.graded n _ (g.graded n v hv))

include hneg hzero in
 theorem Hom.kernel_free_of_split {F C : ModuleData.{uk,ua,um} 𝓐}
    [Module.Free A F] (g : Hom F C) (h : Hom C F)
    (hgh : g.map.comp h.map = LinearMap.id) : Module.Free A (kernel g) := by
  let e := g.splitEquiv h hgh
  let p : F →ₗ[A] kernel g := (LinearMap.snd A C (kernel g)).comp e.toLinearMap
  have hp : p.comp g.map.ker.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((LocalCover.splitEquiv g.map h.map hgh v).2 : F) = v
    simp only [LocalCover.splitEquiv_apply_snd_coe,
      LinearMap.mem_ker.mp v.property, map_zero, sub_zero]
  let : Module.Projective A (kernel g) := Module.Projective.of_split g.map.ker.subtype p hp
  obtain ⟨ι,hι,b,_⟩ := exists_homogeneous_basis_connected 𝓐 (kernel g).piece
    hneg hzero 0 (kernel g).nonneg
  exact Module.Free.of_basis b

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem exists_equiv_shiftedUnits (F : ModuleData.{uk,ua,um} 𝓐) [Module.Free A F] :
    ∃ (n : ℕ) (d : ULift.{um} (Fin n) → ℕ)
      (e : F ≃ₗ[A] pi (fun i : ULift.{um} (Fin n) => (unit hneg).shift (d i))),
      ∀ m v, v ∈ F.piece m → e v ∈
        (pi (fun i : ULift.{um} (Fin n) => (unit hneg).shift (d i))).piece m := by
  classical
  obtain ⟨ι,hι,b0,hd0⟩ := exists_homogeneous_basis_connected 𝓐 F.piece hneg hzero 0 F.nonneg
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let n := Fintype.card ι
  let J := ULift.{um} (Fin n)
  let re : ι ≃ J := (Fintype.equivFin ι).trans Equiv.ulift.symm
  let b := b0.reindex re
  choose dz hdz using hd0
  let d : J → ℕ := fun i => (dz (re.symm i)).toNat
  have hd (i : J) : b i ∈ F.piece (d i : ℤ) := by
    have hz : 0 ≤ dz (re.symm i) := by
      by_contra h
      have he : b0 (re.symm i)=0 := by
        simpa only [F.nonneg _ (lt_of_not_ge h),Submodule.mem_bot] using hdz (re.symm i)
      exact b0.ne_zero (re.symm i) he
    simpa only [b,Module.Basis.reindex_apply,d,Int.toNat_of_nonneg hz] using hdz (re.symm i)
  let e : F ≃ₗ[A] pi (fun i : J => (unit hneg).shift (d i)) :=
    { toFun v i _ := b.equivFun v i
      invFun v := b.equivFun.symm (fun i => v i PUnit.unit)
      left_inv v := b.equivFun.symm_apply_apply v
      right_inv v := by
        funext i j
        change b.equivFun (b.equivFun.symm (fun i => v i PUnit.unit)) i=v i j
        rw [LinearEquiv.apply_symm_apply]
      map_add' v w := by funext i j; exact congrFun (b.equivFun.map_add v w) i
      map_smul' a v := by funext i j; exact congrFun (b.equivFun.map_smul a v) i }
  refine ⟨n,d,e,?_⟩
  intro m v hv i _ j
  change b.equivFun v i ∈ 𝓐 (m-(d i : ℤ)-0)
  rw [sub_zero]
  exact basis_coordinates_graded F.piece b (fun i => (d i : ℤ)) hd m v hv i

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

 theorem unit_idempotent_trivial [IsDomain A]
    (f : Hom (unit.{uk,ua,um} hneg) (unit.{uk,ua,um} hneg))
    (hi : ∀ v, f.map (f.map v) = f.map v) :
    f.map = 0 ∨ f.map = LinearMap.id := by
  let e : unit.{uk,ua,um} hneg := fun _ => 1
  let c : A := f.map e PUnit.unit
  have expand (v : unit.{uk,ua,um} hneg) : v = v PUnit.unit • e := by
    funext i
    cases i
    exact (mul_one _).symm
  have hf (v : unit.{uk,ua,um} hneg) (i : PUnit.{max ua um + 1}) :
      f.map v i = v PUnit.unit * c := by
    calc
      f.map v i = f.map (v PUnit.unit • e) i := congrArg (fun v => f.map v i) (expand v)
      _ = v PUnit.unit * c := by rw [map_smul]; cases i; rfl
  have hc : c*c=c := by
    have h := congrFun (hi e) PUnit.unit
    rw [hf (f.map e) PUnit.unit] at h
    exact h
  have hz : c*(c-1)=0 := by rw [mul_sub,mul_one,hc,sub_self]
  rcases mul_eq_zero.mp hz with hc | hc
  · left
    apply LinearMap.ext
    intro v
    funext i
    rw [hf,hc,mul_zero]
    rfl
  · right
    have hc : c=1 := sub_eq_zero.mp hc
    apply LinearMap.ext
    intro v
    funext i
    rw [hf,hc,mul_one]
    cases i
    rfl

end KLInvariance.Graded.ModuleData
end

end OAI
