import FiniteLogMixingDenominatorTransfer
import DiagonalCompositeLogNormalization

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem shifted_descPochhammer_rising_succ (rho : K) (n : ℕ) :
    (descPochhammer K (n+1)).comp (Polynomial.X+Polynomial.C (rho+(n+1:ℕ)))=
      (descPochhammer K n).comp (Polynomial.X+Polynomial.C (rho+(n:K))) *
        (Polynomial.X+Polynomial.C (rho+(n+1:ℕ))) := by
  rw [descPochhammer_succ_left,Polynomial.mul_comp,Polynomial.X_comp,Polynomial.comp_assoc]
  have he : (Polynomial.X-1:Polynomial K).comp
      (Polynomial.X+Polynomial.C (rho+(n+1:ℕ)))=Polynomial.X+Polynomial.C (rho+(n:K)) := by
    simp only [Polynomial.sub_comp,Polynomial.X_comp,Polynomial.one_comp,Nat.cast_add,Nat.cast_one]
    simp only [Polynomial.C_add,Polynomial.C_1]
    ring
  rw [he,mul_comm]

theorem shifted_descPochhammer_operator_succ (rho : K) (n : ℕ) :
    shiftedPolynomialDifferentialOperator (rho+(n+1:ℕ)) (descPochhammer K (n+1))=
      shiftedPolynomialDifferentialOperator (rho+(n:K)) (descPochhammer K n) *
        shiftedPolynomialDerivative (rho+(n+1:ℕ)) := by
  rw [shiftedPolynomialDifferentialOperator_eq,shifted_descPochhammer_rising_succ,
    shiftedPolynomialDifferentialOperator_eq]
  unfold polynomialDifferentialOperator
  rw [map_mul]
  congr 1
  simp only [map_add,Polynomial.aeval_X,Polynomial.aeval_C,Module.algebraMap_end_eq_smul_id]
  simp only [shiftedPolynomialDerivative,add_smul]

theorem logMixingForward_falling_inverse (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0) (n : ℕ) (p : Polynomial K) :
    shiftedPolynomialDifferentialOperator (rho+(n:K)) (descPochhammer K n)
      (logMixingForward rho n p)=p := by
  induction n with
  | zero => simp [shiftedPolynomialDifferentialOperator,logMixingForward]
  | succ n ih =>
    rw [shifted_descPochhammer_operator_succ,Module.End.mul_apply,
      logMixingForward_recurrence rho n (h n),ih]

/-- The normalized mixing is the EXACT inverse of the diagonal falling
operator, with no factorial or logarithmic term omitted. -/
theorem factorialLogMixing_falling_inverse (rho : K)
    (h : ∀ n : ℕ,rho+(n+1:ℕ)≠0) (n : ℕ) (p : Polynomial K) :
    shiftedPolynomialDifferentialOperator (rho+(n:K)) (normalizedFallingSymbol n)
      (factorialLogMixing rho n p)=p := by
  unfold shiftedPolynomialDifferentialOperator normalizedFallingSymbol factorialLogMixing
  rw [map_mul,Polynomial.aeval_C,Module.End.mul_apply,Module.algebraMap_end_apply,map_smul,
    ← shiftedPolynomialDifferentialOperator,logMixingForward_falling_inverse rho h n p,
    smul_smul,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),one_smul]
end StrictEUnit
end
