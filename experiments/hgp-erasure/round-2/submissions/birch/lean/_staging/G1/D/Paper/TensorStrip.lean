import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Linarith

/-!
# A mixed tensor kernel dimension

Source: source.md D, expanded by G1. First restrict to the kernel of the
first factor map; the remaining constraint is a tensor product map. Its rank
is the product of the ranks, by factorization through the actual ranges.
-/

noncomputable section
namespace Paper
open TensorProduct
universe u v

/-- Rank-nullity for a tensor word constrained by `f` and by a mixed `r ⊗ g`.
Flatness identifies `ker(f ⊗ id)` with `ker f ⊗ N`. Factor the remaining
map through its actual factor ranges to multiply its ranks, then apply
rank-nullity to both ordinary factor maps and to their tensor map. -/
theorem mixed_tensor_kernel_dimension
    {F : Type u} {M M' L N N' : Type v} [Field F]
    [AddCommGroup M] [Module F M] [Module.Finite F M]
    [AddCommGroup M'] [Module F M'] [Module.Finite F M']
    [AddCommGroup L] [Module F L] [Module.Finite F L]
    [AddCommGroup N] [Module F N] [Module.Finite F N]
    [AddCommGroup N'] [Module F N'] [Module.Finite F N']
    (f : M →ₗ[F] M') (r : M →ₗ[F] L) (g : N →ₗ[F] N') :
    Module.finrank F (LinearMap.ker ((f.rTensor N).prod (TensorProduct.map r g))) =
      Module.finrank F (LinearMap.ker f) * Module.finrank F (LinearMap.ker g) +
        Module.finrank F (LinearMap.ker (r.comp (LinearMap.ker f).subtype)) *
          Module.finrank F (LinearMap.range g) := by
  let K := LinearMap.ker f
  let t : K ⊗[F] N →ₗ[F] M ⊗[F] N := K.subtype.rTensor N
  let a : K →ₗ[F] L := r.comp K.subtype
  let b : K ⊗[F] N →ₗ[F] L ⊗[F] N' := TensorProduct.map a g
  have ht : Function.Injective t :=
    Module.Flat.rTensor_preserves_injective_linearMap K.subtype K.injective_subtype
  have htRange : LinearMap.range t = LinearMap.ker (f.rTensor N) :=
    ((Module.Flat.rTensor_exact N f.exact_subtype_ker_map).linearMap_ker_eq).symm
  have hb : b = (TensorProduct.map r g).comp t := by
    ext x y
    rfl
  have hker : (LinearMap.ker b).map t =
      LinearMap.ker ((f.rTensor N).prod (TensorProduct.map r g)) := by
    rw [hb, LinearMap.ker_comp, Submodule.map_comap_eq, htRange,
      LinearMap.ker_prod, inf_comm]
  have hdim : Module.finrank F (LinearMap.ker b) =
      Module.finrank F (LinearMap.ker ((f.rTensor N).prod (TensorProduct.map r g))) := by
    have h := LinearMap.finrank_range_of_inj
      (f := t.comp (LinearMap.ker b).subtype) (ht.comp (LinearMap.ker b).injective_subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype, hker] at h
    exact h.symm
  let ar := a.rangeRestrict
  let gr := g.rangeRestrict
  let inc := TensorProduct.map (LinearMap.range a).subtype (LinearMap.range g).subtype
  let onto := TensorProduct.map ar gr
  have hinc : Function.Injective inc :=
    TensorProduct.map_injective_of_flat_flat _ _
      (LinearMap.range a).injective_subtype (LinearMap.range g).injective_subtype
  have honto : Function.Surjective onto :=
    TensorProduct.map_surjective a.surjective_rangeRestrict g.surjective_rangeRestrict
  have hfactor : b = inc.comp onto := by
    rw [← TensorProduct.map_comp]
    rfl
  have hrank : Module.finrank F (LinearMap.range b) =
      Module.finrank F (LinearMap.range a) * Module.finrank F (LinearMap.range g) := by
    rw [hfactor, LinearMap.range_comp, LinearMap.range_eq_top.mpr honto,
      Submodule.map_top, LinearMap.finrank_range_of_inj hinc,
      Module.finrank_tensorProduct]
  have hbn := b.finrank_range_add_finrank_ker
  rw [hrank, Module.finrank_tensorProduct, hdim] at hbn
  have han := a.finrank_range_add_finrank_ker
  have hgn := g.finrank_range_add_finrank_ker
  change _ = Module.finrank F K * Module.finrank F (LinearMap.ker g) +
    Module.finrank F (LinearMap.ker a) * Module.finrank F (LinearMap.range g)
  nlinarith

end Paper
