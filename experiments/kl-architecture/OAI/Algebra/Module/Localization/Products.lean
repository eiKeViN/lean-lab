import Mathlib

/-! Semantic home: OAI.Algebra.Module.Localization.Products. Source spans: PlaneLocalization:26.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.LocalProducts
open scoped Pointwise
universe ur us um
variable {R : Type ur} [CommRing R] {S : Type us} [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

 theorem smul_top_le_of_map_dvd {p q : R} (h : algebraMap R S q ∣ algebraMap R S p) :
    p • (⊤ : Submodule R M) ≤ q • (⊤ : Submodule R M) := by
  intro z hz
  obtain ⟨w,_,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
  obtain ⟨t,ht⟩ := h
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨t • w,Submodule.mem_top,?_⟩
  rw [← IsScalarTower.algebraMap_smul S q,← IsScalarTower.algebraMap_smul S p,
    smul_smul,← ht]

 theorem smul_top_eq_of_map_associated {p q : R}
    (h : Associated (algebraMap R S p) (algebraMap R S q)) :
    p • (⊤ : Submodule R M) = q • (⊤ : Submodule R M) :=
  le_antisymm (smul_top_le_of_map_dvd h.symm.dvd) (smul_top_le_of_map_dvd h.dvd)

variable {ι κ : Type*}

 theorem associated_prod_power (s : Finset ι) (a : ι → S) (p : S)
    (h : ∀ i ∈ s, Associated (a i) p) : Associated (∏ i ∈ s, a i) (p^s.card) := by
  simpa only [Finset.prod_const] using Associated.prod s a (fun _ => p) h

 theorem associated_prod_scale (s : Finset ι) (t : Finset κ) (a : ι → S) (b : κ → S)
    (p f : S) (k : ℕ) (ha : ∀ i ∈ s, Associated (a i) p)
    (hb : ∀ j ∈ t, Associated (b j) p) (hf : Associated f (p^k))
    (hcount : s.card=t.card+k) :
    Associated (∏ i ∈ s, a i) (f*∏ j ∈ t, b j) := by
  have hs := associated_prod_power s a p ha
  have ht := associated_prod_power t b p hb
  apply hs.trans
  have hpow : p^s.card=p^k*p^t.card := by rw [hcount,add_comm,pow_add]
  rw [hpow]
  exact (hf.mul_mul ht).symm

/-- The local embedded product images agree whenever the reduced labels are
associated and the actual later-edge count has the required difference. -/
 theorem product_image_scale (s : Finset ι) (t : Finset κ) (a : ι → R) (b : κ → R)
    (p : S) (f : R) (k : ℕ)
    (ha : ∀ i ∈ s, Associated (algebraMap R S (a i)) p)
    (hb : ∀ j ∈ t, Associated (algebraMap R S (b j)) p)
    (hf : Associated (algebraMap R S f) (p^k)) (hcount : s.card=t.card+k) :
    (∏ i ∈ s, a i) • (⊤ : Submodule R M) =
      f • ((∏ j ∈ t, b j) • (⊤ : Submodule R M)) := by
  rw [← mul_smul]
  apply smul_top_eq_of_map_associated (S := S)
  simpa only [map_prod,map_mul] using associated_prod_scale s t
    (fun i => algebraMap R S (a i)) (fun j => algebraMap R S (b j)) p
    (algebraMap R S f) k ha hb hf hcount

end KLInvariance.LocalProducts
end

end OAI
