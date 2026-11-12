import HigherDegreeResiduePlace
import Mathlib.NumberTheory.KummerDedekind

noncomputable section
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Classical.propDecidable
open scoped NumberField
open UniqueFactorizationMonoid
namespace StrictEUnit

/-- A factor of the reduced minimal polynomial selects an actual nonzero
prime ideal, provided the conductor condition is checked. -/
theorem numberField_kummer_prime_from_factor
    {K : Type*} [Field K] [NumberField K]
    (a : 𝓞 K) (I : Ideal ℤ) [hI : I.IsMaximal] (hI0 : I ≠ ⊥)
    (hc : (conductor ℤ a).comap (algebraMap ℤ (𝓞 K)) ⊔ I = ⊤)
    (Q : Polynomial ℤ)
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors
      ((minpoly ℤ a).map (Ideal.Quotient.mk I))) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      w.asIdeal = Ideal.span ((I.map (algebraMap ℤ (𝓞 K)) : Set (𝓞 K)) ∪ {Q.aeval a}) ∧
      I.map (algebraMap ℤ (𝓞 K)) ≤ w.asIdeal ∧ Q.aeval a ∈ w.asIdeal := by
  classical
  let e := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    hI hI0 hc (NumberField.RingOfIntegers.isIntegral a)
  let J := e.symm ⟨Q.map (Ideal.Quotient.mk I), hQ⟩
  have hirr : Irreducible (J.val : Ideal (𝓞 K)) :=
    irreducible_of_normalized_factor _ J.property
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨J.val, Ideal.isPrime_of_prime (irreducible_iff_prime.mp hirr), hirr.ne_zero⟩
  have he : w.asIdeal = Ideal.span
      ((I.map (algebraMap ℤ (𝓞 K)) : Set (𝓞 K)) ∪ {Q.aeval a}) :=
    KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
      hI hQ hI0 hc (NumberField.RingOfIntegers.isIntegral a)
  refine ⟨w, he, ?_, ?_⟩
  · rw [he]
    intro x hx
    exact Ideal.subset_span (Or.inl hx)
  · rw [he]
    exact Ideal.subset_span (Or.inr (by simp))

end StrictEUnit
end
