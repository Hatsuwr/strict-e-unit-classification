import GeneralizedLogLaplaceFieldMap

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem polynomialShiftInverse_C (c : K) (hc : c≠0) (a : K) :
    polynomialShiftInverse c (Polynomial.C a)=Polynomial.C (c⁻¹*a) := by
  apply shiftedPolynomialDerivative_injective c hc
  rw [polynomialShiftInverse_rightInverse c hc]
  simp only [shiftedPolynomialDerivative_apply,Polynomial.derivative_C,zero_add,
    Polynomial.smul_eq_C_mul,← map_mul]
  rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul]

theorem logMixingForward_zero_C (n : ℕ) (a : K) :
    logMixingForward 0 n (Polynomial.C a)=Polynomial.C ((n.factorial:K)⁻¹*a) := by
  induction n with
  | zero =>simp [logMixingForward]
  | succ n ih =>
    rw [logMixingForward,ih,polynomialShiftInverse_C _ (by simpa only [zero_add] using (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n+1:ℕ):K)≠0))]
    simp only [zero_add,Nat.factorial_succ,Nat.cast_mul,mul_inv_rev]
    congr 1
    ring

/-- Exact positive-mode factorial normalization for the log-free part only.
General logarithmic coefficients still require the full mixing operator. -/
theorem generalizedLogLaplaceSeries_zero_logfree_coefficient
    (u : LaurentSeries (Polynomial K)) (n : ℕ) (a : K)
    (hu : u.coeff ((n:ℤ)+1)=Polynomial.C a) :
    (generalizedLogLaplaceSeries 0 logMixing_zero_forward_nonzero u).coeff (n:ℤ)=
      Polynomial.C (((-1:K)^n)*((n.factorial:K)⁻¹*a)) := by
  rw [generalizedLogLaplaceSeries_coeff,hu]
  change ((-1:K)^(n:ℤ)) • logMixingForward 0 n (Polynomial.C a)=_
  rw [logMixingForward_zero_C]
  simp only [zpow_natCast,Polynomial.smul_eq_C_mul,← map_mul]

/-- Recover the source coefficient from the normalized target without an
implicit factorial convention or sign change. -/
theorem generalizedLogLaplaceSeries_zero_logfree_factorial_recovery
    (u : LaurentSeries (Polynomial K)) (n : ℕ) (a : K)
    (hu : u.coeff ((n:ℤ)+1)=Polynomial.C a) :
    (n.factorial:K)*(((generalizedLogLaplaceSeries 0 logMixing_zero_forward_nonzero u).coeff (n:ℤ)).coeff 0)=
      (-1:K)^n*a := by
  rw [generalizedLogLaplaceSeries_zero_logfree_coefficient u n a hu,Polynomial.coeff_C_zero]
  have hn : (n.factorial:K)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- Factorial-normalized mixing still acts on the whole log polynomial. -/
def factorialLogMixing (rho : K) (n : ℕ) (p : Polynomial K) : Polynomial K :=
  (n.factorial:K) • logMixingForward rho n p

theorem factorialLogMixing_recurrence (rho : K) (n : ℕ)
    (hc : rho+(n+1:ℕ)≠0) (p : Polynomial K) :
    shiftedPolynomialDerivative (rho+(n+1:ℕ)) (factorialLogMixing rho (n+1) p)=
      ((n+1:ℕ):K) • factorialLogMixing rho n p := by
  unfold factorialLogMixing
  rw [map_smul,logMixingForward_recurrence rho n hc,Nat.factorial_succ,Nat.cast_mul,mul_smul]

theorem generalizedLogLaplaceSeries_factorial_log_coefficient (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0) (u : LaurentSeries (Polynomial K)) (n : ℕ) :
    (n.factorial:K) • (generalizedLogLaplaceSeries rho h u).coeff (n:ℤ)=
      (-1:K)^n • factorialLogMixing rho n (u.coeff ((n:ℤ)+1)) := by
  rw [generalizedLogLaplaceSeries_coeff]
  change (n.factorial:K) • (((-1:K)^(n:ℤ)) • logMixingForward rho n (u.coeff ((n:ℤ)+1)))=_
  simp only [factorialLogMixing,zpow_natCast,smul_smul,mul_comm]

end StrictEUnit
end
