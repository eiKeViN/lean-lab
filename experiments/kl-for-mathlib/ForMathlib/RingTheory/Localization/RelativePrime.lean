import Mathlib

/-! Semantic home: ForMathlib.RingTheory.Localization.RelativePrime. Source spans: PlaneLocalization:16.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.LocalizationRelativePrime
variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

omit [IsDomain A] in
 theorem not_dvd_map {a b : A} (ha : Prime a) (hap : a ∈ p) (hab : ¬a ∣ b) :
    ¬ algebraMap A (Localization.AtPrime p) a ∣ algebraMap A (Localization.AtPrime p) b := by
  intro h
  obtain ⟨s,hs,hdiv⟩ := (IsLocalization.toLocalizationMap p.primeCompl (Localization.AtPrime p)).map_dvd_map.mp h
  rcases ha.dvd_mul.mp hdiv with has | hab'
  · exact hs (p.mem_of_dvd has hap)
  · exact hab hab'

 theorem map_prime {a : A} (ha : Prime a) (hap : a ∈ p) :
    Prime (algebraMap A (Localization.AtPrime p) a) := by
  apply (IsLocalization.toLocalizationMap p.primeCompl (Localization.AtPrime p)).map_prime ha
  · change algebraMap A (Localization.AtPrime p) a ≠ 0
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective A (Localization.AtPrime p)).ne ha.ne_zero
  · change ¬IsUnit (algebraMap A (Localization.AtPrime p) a)
    rw [IsLocalization.AtPrime.isUnit_to_map_iff _ p]
    exact not_not_intro hap

 theorem map_relPrime {a b : A} (ha : Prime a) (hab : ¬a ∣ b) :
    IsRelPrime (algebraMap A (Localization.AtPrime p) a)
      (algebraMap A (Localization.AtPrime p) b) := by
  by_cases hap : a ∈ p
  · exact ((map_prime p ha hap).irreducible.isRelPrime_iff_not_dvd).mpr (not_dvd_map p ha hap hab)
  · exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p a).mpr hap).isRelPrime_left

end KLInvariance.LocalizationRelativePrime
end

end OAI
