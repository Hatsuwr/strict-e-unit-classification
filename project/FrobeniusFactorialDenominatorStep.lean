import FourierRetainedDenominatorSteps

/-! Preserve the factorial normalization before estimating denominators.
The falling-factorial numerators remain explicit in the exact recurrence. -/
noncomputable section
open scoped NumberField BigOperators Classical
namespace StrictEUnit

variable {K : Type*} [Field K] [CharZero K]

theorem polynomialLogFrobeniusCoefficient_factorial_recurrence
    (B : ℕ → Polynomial K) (rho : K) (u0 : Polynomial K) (hP : B 0≠0)
    (n : ℕ) (hn : n≠0) :
    shiftedPolynomialDifferentialOperator (rho+(n : K)) (B 0)
      ((n.factorial : K) • polynomialLogFrobeniusCoefficient B rho u0 n) =
      -(∑ s : Fin n,(n.descFactorial (n-s.val) : K) •
        shiftedPolynomialDifferentialOperator (rho+(s.val : K)) (B (n-s.val))
          ((s.val.factorial : K) • polynomialLogFrobeniusCoefficient B rho u0 s.val)) := by
  rw [map_smul,polynomialLogFrobeniusCoefficient_recurrence B rho u0 hP n hn,
    smul_neg,polynomialLogLowerSum,Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul,smul_smul]
  have h := Nat.factorial_mul_descFactorial (show n-s.val≤n by omega)
  rw [Nat.sub_sub_self (le_of_lt s.isLt)] at h
  have he : (n.factorial : K) = (n.descFactorial (n-s.val) : K)*(s.val.factorial : K) := by
    rw [mul_comm]
    exact_mod_cast h.symm
  rw [he]

/-- An exact integer propagation rule for raw coefficients also applies to
factorial-normalized coefficients, without imposing any factorial denominator. -/
theorem integral_denominator_step_factorial_normalization
    (x : ℕ → ℕ → AlgebraicComplex) (n : ℕ) (hn : 0<n) (q : ℕ)
    (hstep : ∀ D : AlgebraicComplex,
      (∀ (s : Fin n) (j : ℕ),IsIntegral ℤ (D*x s.val j)) →
      ∀ j,IsIntegral ℤ ((q : AlgebraicComplex)*D*x n j))
    (D : AlgebraicComplex)
    (hprev : ∀ (s : Fin n) (j : ℕ),IsIntegral ℤ (D*((s.val.factorial : AlgebraicComplex)*x s.val j))) :
    ∀ j,IsIntegral ℤ ((q : AlgebraicComplex)*D*((n.factorial : AlgebraicComplex)*x n j)) := by
  have hint (k : ℕ) : IsIntegral ℤ (k : AlgebraicComplex) := by
    exact_mod_cast (isIntegral_algebraMap (R:=ℤ) (A:=AlgebraicComplex) (x:=(k : ℤ)))
  have hp : ∀ (s : Fin n) (j : ℕ),IsIntegral ℤ
      ((D*((n-1).factorial : AlgebraicComplex))*x s.val j) := by
    intro s j
    have hs : s.val≤n-1 := by omega
    have hfac := Nat.factorial_mul_descFactorial (show n-1-s.val≤n-1 by omega)
    rw [Nat.sub_sub_self hs] at hfac
    have he : ((n-1).factorial : AlgebraicComplex) =
        (s.val.factorial : AlgebraicComplex)*((n-1).descFactorial (n-1-s.val) : AlgebraicComplex) := by
      exact_mod_cast hfac.symm
    have h := (hprev s j).mul (hint ((n-1).descFactorial (n-1-s.val)))
    convert h using 1
    rw [he]
    ring
  intro j
  have h := (hstep (D*((n-1).factorial : AlgebraicComplex)) hp j).mul (hint n)
  have hfac : n.factorial=n*(n-1).factorial := by
    have he : n=(n-1)+1 := by omega
    conv_lhs => rw [he,Nat.factorial_succ]
    rw [← he]
  convert h using 1
  rw [hfac,Nat.cast_mul]
  ring

end StrictEUnit
end
