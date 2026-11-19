import PolynomialDifferentialSubring

/-! Exact denominators in the full polynomial-log inverse. A bounded power of
the actual scalar indicial value clears the entire inverse, not just its
constant diagonal. No exponential bound for products of these divisors is claimed. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem polynomialDifferentialInverseAux_pivot_clearing
    (R : Subring K) (P : Polynomial K) (hP : ∀ j,P.coeff j∈R)
    (h0 : P.coeff 0≠0) (n : ℕ) (f : Polynomial K) (hf : ∀ j,f.coeff j∈R) :
    ∀ j,((P.coeff 0)^n • polynomialDifferentialOperatorInverseAux P n f).coeff j∈R := by
  induction n generalizing f with
  | zero => simpa [polynomialDifferentialOperatorInverseAux] using R.zero_mem
  | succ n ih =>
    have hder := polynomial_subring_derivative R f hf
    have hprev := ih f.derivative hder
    have hdiv : ∀ j,P.divX.coeff j∈R := by
      intro j
      simpa only [Polynomial.coeff_divX] using hP (j+1)
    have he : (P.coeff 0)^(n+1) • polynomialDifferentialOperatorInverseAux P (n+1) f =
        (P.coeff 0)^n • f - polynomialDifferentialOperator P.divX
          ((P.coeff 0)^n • polynomialDifferentialOperatorInverseAux P n f.derivative) := by
      rw [polynomialDifferentialOperatorInverseAux,smul_smul,pow_succ,mul_assoc,
        mul_inv_cancel₀ h0,mul_one,smul_sub,LinearMap.map_smul]
    rw [he]
    exact polynomial_subring_sub R _ _
      (polynomial_subring_smul R _ _ (R.pow_mem (hP 0) n) hf)
      (polynomial_subring_differentialOperator R P.divX _ hdiv hprev)

/-- Any bounded-log solution of an integral constant-coefficient equation has
its coefficients cleared by the same pivot power. This includes arbitrary
right-hand sides and makes no integrality assumption on the solution. -/
theorem polynomialDifferentialEquation_pivot_clearing
    (R : Subring K) (P f : Polynomial K) (hP : ∀ j,P.coeff j∈R)
    (h0 : P.coeff 0≠0) (d : ℕ) (hf : f.natDegree≤d)
    (hforced : ∀ j,(polynomialDifferentialOperator P f).coeff j∈R) :
    ∀ j,((P.coeff 0)^(d+1) • f).coeff j∈R := by
  have hdegree : (polynomialDifferentialOperator P f).natDegree<d+1 :=
    ((polynomialDifferentialOperator_natDegree_le P f).trans hf).trans_lt (Nat.lt_succ_self d)
  have he : polynomialDifferentialOperatorInverseAux P (d+1)
      (polynomialDifferentialOperator P f)=f := by
    apply polynomialDifferentialOperator_injective P h0
    exact polynomialDifferentialOperatorInverseAux_rightInverse P h0 _ _
      (Polynomial.iterate_derivative_eq_zero hdegree)
  have h := polynomialDifferentialInverseAux_pivot_clearing R P hP h0 (d+1)
    (polynomialDifferentialOperator P f) hforced
  rwa [he] at h

/-- Specialization to algebraic integrality; the exponent is exactly d+1. -/
theorem polynomialDifferentialEquation_integral_pivot_power
    (P f : Polynomial K) (hP : ∀ j,IsIntegral ℤ (P.coeff j))
    (h0 : P.coeff 0≠0) (d : ℕ) (hf : f.natDegree≤d)
    (hforced : ∀ j,IsIntegral ℤ ((polynomialDifferentialOperator P f).coeff j)) :
    ∀ j,IsIntegral ℤ ((P.coeff 0)^(d+1)*f.coeff j) := by
  have h := polynomialDifferentialEquation_pivot_clearing (integralClosure ℤ K).toSubring
    P f hP h0 d hf hforced
  simpa only [Polynomial.coeff_smul,smul_eq_mul] using h

end StrictEUnit
end
