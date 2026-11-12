import PolynomialValuationGauss
import IntegralNormDivisor
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# One coefficient norm clears a common integral polynomial product

The coefficient-product range lemma uses height-one valuations of a Dedekind
 domain. Its number-field specialization and the accepted non-Galois norm
 divisor use one chosen nonzero coefficient of the common polynomial for the
 entire family. No UFD, Galois, absolute-norm bound, or degree-dependent power
 is assumed or concluded.
-/

noncomputable section

open scoped NumberField

namespace StrictEUnit

/-- If every coefficient of a product lies in a Dedekind domain, then every
product of one coefficient from each factor lies in that domain as well. -/
theorem polynomial_coeff_mul_mem_range_of_product
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (P Q : Polynomial K)
    (hprod : ∀ n : ℕ, (P * Q).coeff n ∈ (algebraMap R K).range) (i j : ℕ) :
    P.coeff i * Q.coeff j ∈ (algebraMap R K).range := by
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K
  intro v
  rw [(v.valuation K).map_mul]
  apply polynomial_valuation_coeff_product_le (v.valuation K) P Q 1 ?_ i j
  intro n
  obtain ⟨x, hx⟩ := hprod n
  rw [← hx]
  exact v.valuation_le_one x

/-- Integral coefficients of a polynomial product force integrality of all
pairwise coefficient products, over any number field. -/
theorem polynomial_isIntegral_coeff_mul_of_product
    {K : Type*} [Field K] [NumberField K] (P Q : Polynomial K)
    (hprod : ∀ n : ℕ, IsIntegral ℤ ((P * Q).coeff n)) (i j : ℕ) :
    IsIntegral ℤ (P.coeff i * Q.coeff j) := by
  have hrange (n : ℕ) : (P * Q).coeff n ∈ (algebraMap (𝓞 K) K).range :=
    ⟨⟨(P * Q).coeff n, hprod n⟩, rfl⟩
  obtain ⟨b, hb⟩ := polynomial_coeff_mul_mem_range_of_product
    (R := 𝓞 K) P Q hrange i j
  rw [← hb]
  exact NumberField.RingOfIntegers.isIntegral_coe b

/-- The literal signed integer norm of one fixed nonzero coefficient of the
common integral polynomial clears every coefficient of every family member.
The family need not be finite, and the same norm is retained throughout. -/
theorem polynomial_common_coefficient_norm_clears_family
    {K I : Type*} [Field K] [NumberField K]
    (V : Polynomial (𝓞 K)) (k : ℕ) (hk : V.coeff k ≠ 0)
    (W : I → Polynomial K)
    (hprod : ∀ l : I, ∀ n : ℕ,
      IsIntegral ℤ ((V.map (algebraMap (𝓞 K) K) * W l).coeff n)) :
    Algebra.norm ℤ (V.coeff k) ≠ 0 ∧
      (Algebra.norm ℤ (V.coeff k) : ℚ) = Algebra.norm ℚ ((V.coeff k : 𝓞 K) : K) ∧
      ∀ l : I, ∀ j : ℕ,
        IsIntegral ℤ ((Algebra.norm ℤ (V.coeff k) : K) * (W l).coeff j) := by
  refine ⟨Algebra.norm_ne_zero_iff.mpr hk, Algebra.coe_norm_int (V.coeff k), ?_⟩
  obtain ⟨b, hb⟩ := ringOfIntegers_dvd_integer_norm (V.coeff k)
  have hnorm : (Algebra.norm ℤ (V.coeff k) : K) =
      algebraMap (𝓞 K) K (V.coeff k) * algebraMap (𝓞 K) K b := by
    simpa only [map_intCast, map_mul] using congrArg (algebraMap (𝓞 K) K) hb
  intro l j
  have hcoeff : IsIntegral ℤ (algebraMap (𝓞 K) K (V.coeff k) * (W l).coeff j) := by
    simpa only [Polynomial.coeff_map] using polynomial_isIntegral_coeff_mul_of_product
      (V.map (algebraMap (𝓞 K) K)) (W l) (hprod l) k j
  rw [hnorm, mul_right_comm (algebraMap (𝓞 K) K (V.coeff k))
    (algebraMap (𝓞 K) K b) ((W l).coeff j)]
  exact hcoeff.mul (NumberField.RingOfIntegers.isIntegral_coe b)

end StrictEUnit

end
