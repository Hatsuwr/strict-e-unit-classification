import PolynomialIntegralCommonNorm
import IntegralNormHouse

/-! The positive denominator is the absolute value of the SAME integer norm
of the SAME coefficient of the common polynomial. No size hypothesis on that
coefficient, or exponential-in-cutoff conclusion, is added. -/

noncomputable section

open scoped NumberField

namespace StrictEUnit

/-- One positive, house-bounded integer clears an arbitrary family of polynomial
quotients whose products with the same integral polynomial are integral. -/
theorem polynomial_common_coefficient_natAbs_norm_certificate
    {K I : Type*} [Field K] [NumberField K]
    (V : Polynomial (𝓞 K)) (k : ℕ) (hk : V.coeff k ≠ 0)
    (W : I → Polynomial K)
    (hprod : ∀ l : I, ∀ n : ℕ,
      IsIntegral ℤ ((V.map (algebraMap (𝓞 K) K) * W l).coeff n)) :
    0 < Int.natAbs (Algebra.norm ℤ (V.coeff k)) ∧
      (Int.natAbs (Algebra.norm ℤ (V.coeff k)) : ℝ) ≤
        NumberField.house ((V.coeff k : 𝓞 K) : K) ^ Module.finrank ℚ K ∧
      (Algebra.norm ℤ (V.coeff k) : ℚ) = Algebra.norm ℚ ((V.coeff k : 𝓞 K) : K) ∧
      ∀ l : I, ∀ j : ℕ,
        IsIntegral ℤ ((Int.natAbs (Algebra.norm ℤ (V.coeff k)) : K) * (W l).coeff j) := by
  obtain ⟨hq, hbound, b, hb⟩ := ringOfIntegers_natAbs_norm_certificate (V.coeff k) hk
  refine ⟨hq, hbound, Algebra.coe_norm_int (V.coeff k), ?_⟩
  have hnorm : (Int.natAbs (Algebra.norm ℤ (V.coeff k)) : K) =
      algebraMap (𝓞 K) K (V.coeff k) * algebraMap (𝓞 K) K b := by
    simpa only [map_natCast, map_mul] using congrArg (algebraMap (𝓞 K) K) hb
  intro l j
  have hcoeff : IsIntegral ℤ (algebraMap (𝓞 K) K (V.coeff k) * (W l).coeff j) := by
    simpa only [Polynomial.coeff_map] using polynomial_isIntegral_coeff_mul_of_product
      (V.map (algebraMap (𝓞 K) K)) (W l) (hprod l) k j
  rw [hnorm, mul_right_comm (algebraMap (𝓞 K) K (V.coeff k))
    (algebraMap (𝓞 K) K b) ((W l).coeff j)]
  exact hcoeff.mul (NumberField.RingOfIntegers.isIntegral_coe b)

end StrictEUnit

end
