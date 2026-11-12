import LogMixingIntegerModes

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem shiftedPolynomialDerivative_commute (a b : K) (p : Polynomial K) :
    shiftedPolynomialDerivative a (shiftedPolynomialDerivative b p)=
      shiftedPolynomialDerivative b (shiftedPolynomialDerivative a p) := by
  simp only [shiftedPolynomialDerivative_apply,Polynomial.derivative_add,
    Polynomial.derivative_smul,smul_add,smul_smul,Polynomial.smul_eq_C_mul]
  simp only [Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,mul_zero,zero_add,add_zero]
  ring

theorem polynomialShiftInverse_commute_shift (a b : K) (ha : a≠0) (p : Polynomial K) :
    polynomialShiftInverse a (shiftedPolynomialDerivative b p)=
      shiftedPolynomialDerivative b (polynomialShiftInverse a p) := by
  apply shiftedPolynomialDerivative_injective a ha
  rw [polynomialShiftInverse_rightInverse a ha,shiftedPolynomialDerivative_commute,
    polynomialShiftInverse_rightInverse a ha]

theorem logMixingMode_commute_shift (rho b : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℤ) (p : Polynomial K) :
    logMixingMode rho n (shiftedPolynomialDerivative b p)=
      shiftedPolynomialDerivative b (logMixingMode rho n p) := by
  have hf (n : ℕ) : logMixingForward rho n (shiftedPolynomialDerivative b p)=
      shiftedPolynomialDerivative b (logMixingForward rho n p) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [logMixingForward,ih,polynomialShiftInverse_commute_shift _ b (h n)]
      rfl
  have hb (n : ℕ) : logMixingBackward rho n (shiftedPolynomialDerivative b p)=
      shiftedPolynomialDerivative b (logMixingBackward rho n p) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [logMixingBackward,ih,shiftedPolynomialDerivative_commute]
      rfl
  cases n with
  | ofNat n => exact hf n
  | negSucc n => exact hb (n+1)

/-- Exact mode relation required by the reciprocal-derivative generator.
Together with the forward recurrence it accounts for BOTH Weyl generators,
but no full Laurent-series transform is asserted by this mode theorem. -/
theorem logMixingMode_recurrence_right (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℤ) (p : Polynomial K) :
    logMixingMode rho (n+1) (shiftedPolynomialDerivative (rho+(n : K)+1) p)=
      logMixingMode rho n p := by
  rw [logMixingMode_commute_shift rho _ h,logMixingMode_recurrence rho h]

variable [CharZero K]
theorem logMixing_zero_forward_nonzero (n : ℕ) : (0 : K)+(n+1 : ℕ)≠0 := by
  simp only [zero_add]
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)

theorem logMixing_noninteger_forward_nonzero (rho : K)
    (h : ∀ z : ℤ,rho≠(z : K)) (n : ℕ) : rho+(n+1 : ℕ)≠0 := by
  intro he
  apply h (-(n+1 : ℕ) : ℤ)
  push_cast
  simpa only [Nat.cast_add,Nat.cast_one] using eq_neg_of_add_eq_zero_left he

end StrictEUnit
end
