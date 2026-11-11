import QEC.Coding.HypergraphProduct.Dimension.BoundaryMaps
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import HGPExperiment.Erasure
import HGPExperiment.StripDuality

noncomputable section
namespace HGPExperiment
open QEC.Coding.HypergraphProduct TensorProduct
universe u
variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Arrays with all columns in `U` and all rows in `V`. -/
def gridSpace (U : Submodule (ZMod 2) (A → ZMod 2))
    (V : Submodule (ZMod 2) (B → ZMod 2)) :
    Submodule (ZMod 2) (A × B → ZMod 2) where
  carrier := {w | (∀ b, (fun a => w (a,b)) ∈ U) ∧ (∀ a, (fun b => w (a,b)) ∈ V)}
  zero_mem' := ⟨fun _ => U.zero_mem, fun _ => V.zero_mem⟩
  add_mem' hx hy := ⟨fun b => U.add_mem (hx.1 b) (hy.1 b), fun a => V.add_mem (hx.2 a) (hy.2 a)⟩
  smul_mem' c hx := ⟨fun b => U.smul_mem c (hx.1 b), fun a => V.smul_mem c (hx.2 a)⟩

private theorem tensor_columns {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
    (f : (A → ZMod 2) →ₗ[ZMod 2] M)
    (t : (A → ZMod 2) ⊗[ZMod 2] (B → ZMod 2)) (b : B) :
    piScalarRight (ZMod 2) (ZMod 2) M B (f.rTensor (B → ZMod 2) t) b =
      f (fun a => wordTensorEquiv (ZMod 2) A B t (a,b)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [LinearMap.rTensor_tmul, piScalarRight_apply, piScalarRightHom_tmul,
        wordTensorEquiv_tmul_apply]
      change y b • f x = f (fun a => x a * y b)
      rw [← map_smul]
      congr 1
      funext a
      simp [mul_comm]
  | add x y hx hy => simp_all [map_add]

private theorem tensor_rows {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
    (g : (B → ZMod 2) →ₗ[ZMod 2] M)
    (t : (A → ZMod 2) ⊗[ZMod 2] (B → ZMod 2)) (a : A) :
    piScalarRight (ZMod 2) (ZMod 2) M A
      ((TensorProduct.comm (ZMod 2) (A → ZMod 2) M)
        (g.lTensor (A → ZMod 2) t)) a =
      g (fun b => wordTensorEquiv (ZMod 2) A B t (a,b)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.comm_tmul, piScalarRight_apply,
        piScalarRightHom_tmul, wordTensorEquiv_tmul_apply]
      change x a • g y = g (fun b => x a * y b)
      rw [← map_smul]
      rfl
  | add x y hx hy => simp_all [map_add]

theorem finrank_gridSpace (U : Submodule (ZMod 2) (A → ZMod 2))
    (V : Submodule (ZMod 2) (B → ZMod 2)) :
    Module.finrank (ZMod 2) (gridSpace U V) =
      Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) V := by
  let e := wordTensorEquiv (ZMod 2) A B
  have h : (LinearMap.ker (jointTensorMap U.mkQ V.mkQ)).map e.toLinearMap = gridSpace U V := by
    ext w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      change (U.mkQ.rTensor (B → ZMod 2) t, V.mkQ.lTensor (A → ZMod 2) t) = 0 at ht
      refine ⟨fun b => ?_, fun a => ?_⟩
      · rw [← Submodule.Quotient.eq_zero_iff_mem]
        rw [← tensor_columns U.mkQ t b, (Prod.mk_eq_zero.mp ht).1]
        simp
      · rw [← Submodule.Quotient.eq_zero_iff_mem]
        rw [← tensor_rows V.mkQ t a, (Prod.mk_eq_zero.mp ht).2]
        simp
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      change (U.mkQ.rTensor (B → ZMod 2) (e.symm w), V.mkQ.lTensor (A → ZMod 2) (e.symm w)) = 0
      apply Prod.ext
      · apply (piScalarRight (ZMod 2) (ZMod 2) _ B).injective
        ext b
        rw [tensor_columns]
        simp only [e, LinearEquiv.apply_symm_apply]
        exact (Submodule.Quotient.eq_zero_iff_mem).mpr (hw.1 b)
      · apply (TensorProduct.comm (ZMod 2) (A → ZMod 2) _).injective
        apply (piScalarRight (ZMod 2) (ZMod 2) _ A).injective
        ext a
        rw [tensor_rows]
        simp only [e, LinearEquiv.apply_symm_apply]
        exact (Submodule.Quotient.eq_zero_iff_mem).mpr (hw.2 a)
  rw [← h, e.finrank_map_eq]
  simpa using finrank_ker_jointTensorMap U.mkQ V.mkQ


variable {C : Type u} [Fintype C] [DecidableEq C]

def rowMap (g : (B → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2)) :
    (A × B → ZMod 2) →ₗ[ZMod 2] (A × C → ZMod 2) where
  toFun w p := g (fun b => w (p.1,b)) p.2
  map_add' x y := by ext p; exact congrFun (g.map_add _ _) p.2
  map_smul' c x := by ext p; exact congrFun (g.map_smul c _) p.2

def colMap (f : (A → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2)) :
    (A × B → ZMod 2) →ₗ[ZMod 2] (C × B → ZMod 2) where
  toFun w p := f (fun a => w (a,p.2)) p.1
  map_add' x y := by ext p; exact congrFun (f.map_add _ _) p.1
  map_smul' c x := by ext p; exact congrFun (f.map_smul c _) p.1

@[simp] theorem rowMap_apply (g : (B → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2))
    (w : A × B → ZMod 2) (a : A) (c : C) :
    rowMap g w (a,c) = g (fun b => w (a,b)) c := rfl

@[simp] theorem colMap_apply (f : (A → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2))
    (w : A × B → ZMod 2) (c : C) (b : B) :
    colMap f w (c,b) = f (fun a => w (a,b)) c := rfl

variable {D : Type u} [Fintype D] [DecidableEq D]

theorem colMap_rowMap (f : (A → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2))
    (g : (B → ZMod 2) →ₗ[ZMod 2] (D → ZMod 2)) (w : A × B → ZMod 2) :
    colMap f (rowMap g w) = rowMap g (colMap f w) := by
  obtain ⟨t, rfl⟩ := (wordTensorEquiv (ZMod 2) A B).surjective w
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp_all only [map_add]
  | tmul x y =>
      ext ⟨c,d⟩
      change f (fun a => g (fun b => wordTensorEquiv (ZMod 2) A B (x ⊗ₜ[ZMod 2] y) (a,b)) d) c =
        g (fun b => f (fun a => wordTensorEquiv (ZMod 2) A B (x ⊗ₜ[ZMod 2] y) (a,b)) c) d
      simp only [wordTensorEquiv_tmul_apply]
      have h1 (a : A) : (fun b => x a * y b) = x a • y := rfl
      have h2 (b : B) : (fun a => x a * y b) = y b • x := by ext a; simp [mul_comm]
      simp only [h1, h2, map_smul, Pi.smul_apply, smul_eq_mul]
      change f (g y d • x) c = g (f x c • y) d
      simp [mul_comm]

/-- A linear lifting of a map's range, extended to its ambient codomain. -/
theorem exists_range_lift (g : (B → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2)) :
    ∃ l : (C → ZMod 2) →ₗ[ZMod 2] (B → ZMod 2),
      ∀ y ∈ LinearMap.range g, g (l y) = y := by
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨p, hp⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective (LinearMap.range g).ker_subtype
  refine ⟨s.comp p, ?_⟩
  intro y hy
  have hp' : p y = ⟨y,hy⟩ := by
    exact DFunLike.congr_fun hp ⟨y,hy⟩
  change g (s (p y)) = y
  rw [hp']
  exact congrArg Subtype.val (DFunLike.congr_fun hs ⟨y,hy⟩)

/-- Exactness for arrays: rowwise lifting can preserve a columnwise kernel. -/
theorem exists_rowMap_preimage_iff
    (f : (A → ZMod 2) →ₗ[ZMod 2] (C → ZMod 2))
    (g : (B → ZMod 2) →ₗ[ZMod 2] (D → ZMod 2)) (w : A × D → ZMod 2) :
    (∃ v : A × B → ZMod 2, colMap f v = 0 ∧ rowMap g v = w) ↔
      w ∈ gridSpace (LinearMap.ker f) (LinearMap.range g) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    constructor
    · intro d
      change f (fun a => rowMap g v (a,d)) = 0
      ext c
      have h := congrFun (colMap_rowMap f g v) (c,d)
      simpa [hv] using h
    · intro a
      exact ⟨fun b => v (a,b), rfl⟩
  · intro hw
    obtain ⟨l, hl⟩ := exists_range_lift g
    refine ⟨rowMap l w, ?_, ?_⟩
    · rw [colMap_rowMap]
      have hf : colMap f w = 0 := by
        ext ⟨c,d⟩
        exact congrFun (hw.1 d) c
      simp [hf]
    · ext ⟨a,d⟩
      exact congrFun (hl _ (hw.2 a)) d


/-- A word carried by the first physical block. -/
def inlWord {T : Type u} : (A × B → ZMod 2) →ₗ[ZMod 2] (Sum (A × B) T → ZMod 2) where
  toFun w := Sum.elim w 0
  map_add' x y := by ext q; cases q <;> rfl
  map_smul' c x := by ext q; cases q <;> rfl

theorem inlWord_injective {T : Type u} :
    Function.Injective (inlWord (A := A) (B := B) (T := T)) := by
  intro x y h
  funext p
  exact congrFun h (Sum.inl p)

/-- A whole strip in the variable-variable block, with the other block empty. -/
def stripSet (S : Set A) : Set (Sum (A × B) (C × D)) :=
  {q | match q with | Sum.inl p => p.1 ∈ S | Sum.inr _ => False}

@[simp] theorem inlWord_inl {T : Type u} (w : A × B → ZMod 2) (p : A × B) :
    inlWord (T := T) w (Sum.inl p) = w p := rfl
@[simp] theorem inlWord_inr {T : Type u} (w : A × B → ZMod 2) (p : T) :
    inlWord w (Sum.inr p) = 0 := rfl

/-- Intersecting an array space with a physical strip amounts to shortening
    its column space. -/
theorem strip_intersection (S : Set A)
    (T : Submodule (ZMod 2) (Sum (A × B) (C × D) → ZMod 2))
    (U : Submodule (ZMod 2) (A → ZMod 2)) (V : Submodule (ZMod 2) (B → ZMod 2))
    (h : ∀ w, inlWord w ∈ T ↔ w ∈ gridSpace U V) :
    T ⊓ supportSpace (stripSet S) =
      (gridSpace (U ⊓ supportSpace S) V).map inlWord := by
  ext v
  constructor
  · rintro ⟨hv, hs⟩
    let w : A × B → ZMod 2 := fun p => v (Sum.inl p)
    have heq : inlWord w = v := by
      funext q
      cases q with
      | inl p => rfl
      | inr p => exact (hs (Sum.inr p) (by simp [stripSet])).symm
    have hg := (h w).mp (heq.symm ▸ hv)
    refine ⟨w, ⟨fun b => ⟨hg.1 b, ?_⟩, hg.2⟩, heq⟩
    intro a ha
    exact hs (Sum.inl (a,b)) ha
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(h w).mpr ⟨fun b => (hw.1 b).1, hw.2⟩, ?_⟩
    intro q hq
    cases q with
    | inl p => exact (hw.1 p.2).2 p.1 hq
    | inr p => rfl

variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

theorem boundary1_inlWord (G : Data (ZMod 2) R₁ C₁ R₂ C₂) (w : C₁ × C₂ → ZMod 2) :
    Matrix.toLin' (boundary1Matrix G) (inlWord w) = colMap (Matrix.toLin' G.first) w := by
  ext ⟨r,c⟩
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, colMap, inlWord, boundary1Matrix]

theorem boundary2Transpose_inlWord (G : Data (ZMod 2) R₁ C₁ R₂ C₂) (w : C₁ × C₂ → ZMod 2) :
    Matrix.toLin' (boundary2Matrix G).transpose (inlWord w) = rowMap (Matrix.toLin' G.second) w := by
  ext ⟨c,r⟩
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_prod_type, rowMap, inlWord, boundary2Matrix, Matrix.transpose_apply]

theorem boundary2_eq_inlWord_iff (G : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : C₁ × R₂ → ZMod 2) (w : C₁ × C₂ → ZMod 2) :
    Matrix.toLin' (boundary2Matrix G) v = inlWord w ↔
      colMap (Matrix.toLin' G.first) v = 0 ∧ rowMap (Matrix.toLin' G.second.transpose) v = w := by
  have hi (c : C₁) (d : C₂) : Matrix.toLin' (boundary2Matrix G) v (Sum.inl (c,d)) =
      rowMap (Matrix.toLin' G.second.transpose) v (c,d) := by
    exact boundary2_inl_apply G v c d
  have hr (r : R₁) (s : R₂) : Matrix.toLin' (boundary2Matrix G) v (Sum.inr (r,s)) =
      colMap (Matrix.toLin' G.first) v (r,s) := by
    exact boundary2_inr_apply G v r s
  constructor
  · intro h
    constructor
    · ext ⟨r,s⟩
      simpa [hr] using congrFun h (Sum.inr (r,s))
    · ext ⟨c,d⟩
      simpa [hi] using congrFun h (Sum.inl (c,d))
  · rintro ⟨h1,h2⟩
    ext q
    cases q with
    | inl p => simpa [hi] using congrFun h2 p
    | inr p => simpa [hr] using congrFun h1 p

end HGPExperiment
