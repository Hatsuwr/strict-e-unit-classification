import SignedInverseLaplace

/-!
# Exact kernel and polynomial errors of the signed inverse-Laplace transform

Only the positive Laurent coefficients are read by the transform. In
particular, polynomial expressions in z=w⁻¹ are killed. This is an additive
coefficient argument, not a claim that the transform is multiplicative.
-/
noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The exact kernel condition includes n=0, which reads exponent 1.
No restriction is imposed on coefficients at exponent 0 or below. -/
theorem signedInverseLaplace_eq_zero_iff (y : LaurentSeries K) :
    signedInverseLaplace y = 0 ↔ ∀ n : ℕ, y.coeff ((n : ℤ) + 1) = 0 := by
  constructor
  · intro hy n
    have hn := congrArg (PowerSeries.coeff K n) hy
    rw [signedInverseLaplace_coeff, map_zero] at hn
    have hf : (n.factorial : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hs : (-1 : K) ^ n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hn).resolve_right hf)).resolve_left hs
  · intro hy
    ext n
    rw [signedInverseLaplace_coeff, hy n, mul_zero, zero_div, map_zero]

/-- Every Laurent monomial at nonpositive exponent is killed, including a
nonzero constant at exponent zero. -/
theorem signedInverseLaplace_single_nonpos (d : ℤ) (c : K) (hd : d ≤ 0) :
    signedInverseLaplace (HahnSeries.single d c) = 0 := by
  apply (signedInverseLaplace_eq_zero_iff _).mpr
  intro n
  exact HahnSeries.coeff_single_of_ne (by omega : (n : ℤ) + 1 ≠ d)

/-- Literal evaluation of a polynomial in z=w⁻¹, with the usual constant
embedding. This is an actual polynomial evaluation, not a chosen error term. -/
def signedLaplacePolynomialInZ (P : Polynomial K) : LaurentSeries K :=
  P.eval₂ (HahnSeries.C : K →+* LaurentSeries K) (HahnSeries.single (-1 : ℤ) (1 : K))

/-- Polynomial initial-value errors disappear under the signed transform. -/
theorem signedInverseLaplace_polynomialInZ (P : Polynomial K) :
    signedInverseLaplace (signedLaplacePolynomialInZ P) = 0 := by
  change signedInverseLaplace
    (P.eval₂ (HahnSeries.C : K →+* LaurentSeries K)
      (HahnSeries.single (-1 : ℤ) (1 : K))) = 0
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.eval₂_add, signedInverseLaplace_add, hP, hQ, add_zero]
  | monomial n c =>
      rw [Polynomial.eval₂_monomial, HahnSeries.C_apply,
        HahnSeries.single_pow, HahnSeries.single_mul_single]
      simp only [one_pow, mul_one, zero_add]
      apply signedInverseLaplace_single_nonpos
      simp only [nsmul_eq_mul, mul_neg, mul_one]
      exact neg_nonpos.mpr (Nat.cast_nonneg n)

/-- Adding any literal polynomial in z does not alter the transformed series. -/
theorem signedInverseLaplace_add_polynomialInZ (y : LaurentSeries K) (P : Polynomial K) :
    signedInverseLaplace (y + signedLaplacePolynomialInZ P) = signedInverseLaplace y := by
  rw [signedInverseLaplace_add, signedInverseLaplace_polynomialInZ, add_zero]

end StrictEUnit
end
