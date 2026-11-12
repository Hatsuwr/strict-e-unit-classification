import WeightedClearedDerivative
import Mathlib.Algebra.Polynomial.Expand

/-! Exact expansion transport. Nondivisible indices vanish; no coefficient
at floor(k/h) is used without the divisibility branch. -/
noncomputable section
namespace StrictEUnit

/-- A shifted weighted coefficient bound transports to literal polynomial
expansion, including the case where the shifted lower bound is negative. -/
theorem polynomial_expand_shifted_lower_bound
    {R : Type*} [CommSemiring R] (P : Polynomial R) (h b d k : ℕ) (hh : 0<h)
    (hP : ∀ i, h*i+d<b → P.coeff i = 0)
    (hk : k+d<b) : (Polynomial.expand R h P).coeff k = 0 := by
  rw [Polynomial.coeff_expand hh]
  split_ifs with hd
  · apply hP
    rw [Nat.mul_div_cancel' hd]
    exact hk
  · rfl

/-- The differential part has zero coefficient at every expanded index on
or below the chosen irregular face. This uses only original polynomial
differentiation and the exact expansion coefficient formula. -/
theorem polynomial_expand_irregular_derivative_zero
    {R : Type*} [CommRing R] (T P : Polynomial R) (c : R)
    (h t e a k : ℕ) (hh : 0<h)
    (hT : ∀ i, i<t → T.coeff i = 0)
    (hP : ∀ i, i<e → (Polynomial.expand R h P).coeff i = 0)
    (hha : h<a) (ha : a≤h*t) (hk : k≤e+(h*t-a)) :
    (Polynomial.expand R h
      (T*P.derivative - Polynomial.C c*T.derivative*P)).coeff k = 0 := by
  rw [Polynomial.coeff_expand hh]
  split_ifs with hd
  · refine irregular_cleared_derivative_coeff_eq_zero T P c h t e a (k/h)
      hT ?_ hha ha ?_
    · intro i hi
      rw [← Polynomial.coeff_expand_mul' hh P i]
      exact hP (h*i) hi
    · rw [Nat.mul_div_cancel' hd]
      exact hk
  · rfl

end StrictEUnit
end
