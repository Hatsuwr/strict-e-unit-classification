import GeneralizedLogLaplaceDerivativeIdentity

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem logMixingForward_eq_zero_iff (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0) (n : ℕ) (p : Polynomial K) :
    logMixingForward rho n p=0 ↔ p=0 := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    constructor
    · intro hz
      apply ih.mp
      have he := logMixingForward_recurrence rho n (h n) p
      rw [hz,map_zero] at he
      exact he.symm
    · rintro rfl
      exact logMixingMode_zero rho h (n+1)

/-- Exactly one zero diagonal is encountered in the zero-class backward
chain. All other factors are injective, leaving only constant log polynomials. -/
theorem logMixingBackward_zero_kernel (n : ℕ) (p : Polynomial K) :
    logMixingBackward (0 : K) (n+1) p=0 ↔ p.derivative=0 := by
  induction n with
  | zero => rw [logMixingBackward_zero_first]
  | succ n ih =>
    have hc : (0 : K)-(n+1 : ℕ)≠0 := by
      simpa only [zero_sub,neg_ne_zero] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n+1 : ℕ) : K)≠0)
    change shiftedPolynomialDerivative ((0 : K)-(n+1 : ℕ)) (logMixingBackward (0 : K) (n+1) p)=0 ↔ _
    constructor
    · intro hz
      exact ih.mp ((shiftedPolynomialDerivative_injective _ hc)
        (hz.trans (map_zero _).symm))
    · intro hz
      rw [ih.mpr hz,map_zero]

/-- Noninteger classes have no kernel at any backward index. -/
theorem logMixingBackward_noninteger_kernel (rho : K)
    (h : ∀ z : ℤ,rho≠(z : K)) (n : ℕ) (p : Polynomial K) :
    logMixingBackward rho n p=0 ↔ p=0 := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    have hc : rho-(n : K)≠0 := sub_ne_zero.mpr (by simpa only [Int.cast_natCast] using h (n : ℤ))
    change shiftedPolynomialDerivative (rho-(n : K)) (logMixingBackward rho n p)=0 ↔ _
    constructor
    · intro hz
      exact ih.mp ((shiftedPolynomialDerivative_injective _ hc)
        (hz.trans (map_zero _).symm))
    · intro hz
      rw [ih.mpr hz,map_zero]

end StrictEUnit
end
