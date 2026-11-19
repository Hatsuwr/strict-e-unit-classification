import PolynomialConnectionClearing
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! Same-denominator transfer to arbitrary expanded coefficient positions.
No support, recurrence, nonvanishing or arithmetic-growth premise is introduced. -/
noncomputable section
namespace StrictEUnit

/-- Expansion does not create new coefficient denominators. The nondivisible
index branch is explicitly zero, not the coefficient at a truncated quotient. -/
theorem isIntegral_expanded_coefficient_div
    {K : Type*} [Field K] (P : Polynomial K) (z d : K)
    (h : ℕ) (hh : 0 < h) (e : ℕ)
    (hint : ∀ l, IsIntegral ℤ (z * (Polynomial.C d⁻¹ * P).coeff l)) :
    IsIntegral ℤ (z * (Polynomial.expand K h P).coeff e / d) := by
  rw [Polynomial.coeff_expand hh]
  by_cases he : h ∣ e
  · rw [if_pos he]
    have hi := hint (e/h)
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_mul_C] at hi
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hi
  · rw [if_neg he, mul_zero, zero_div]
    exact isIntegral_zero

/-- The actual original W_m and H_m definitions discharge the normalization
identity. Every arbitrary extracted coefficient uses the SAME integer δ. -/
theorem polynomialConnectionSequence_expanded_integral
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (m δ h : ℕ) (hh : 0 < h) (row j : Fin r) (e : ℕ)
    (hint : ∀ l, IsIntegral ℤ
      ((δ:K)*(dividedPolynomialConnectionSequence T U m row j).coeff l)) :
    IsIntegral ℤ ((δ:K) *
      (Polynomial.expand K h (polynomialConnectionSequence T U m row j)).coeff e /
        (m.factorial:K)) := by
  exact isIntegral_expanded_coefficient_div (polynomialConnectionSequence T U m row j)
    (δ:K) (m.factorial:K) h hh e hint

end StrictEUnit
end
