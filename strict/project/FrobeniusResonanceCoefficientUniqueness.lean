import PolynomialLogFrobeniusRecurrence

/-!
# Finite resonant coefficient data determine every formal solution

This concerns arbitrary polynomial-valued formal coefficient sequences, not
only the constructed amplitudes. At each index, the difference of two solutions
with identical preceding coefficients lies in the exact indicial kernel. Its
low logarithmic coefficients are therefore the only new freedom. There are
only finitely many such coordinates by the existing resonance budget.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem polynomialLogEulerCoefficient_add (B : ℕ → Polynomial K) (rho : K)
    (u v : ℕ → Polynomial K) (n : ℕ) :
    polynomialLogEulerCoefficient B rho (u+v) n =
      polynomialLogEulerCoefficient B rho u n + polynomialLogEulerCoefficient B rho v n := by
  simp only [polynomialLogEulerCoefficient,Pi.add_apply,map_add,Finset.sum_add_distrib]

theorem polynomialLogEulerCoefficient_sub (B : ℕ → Polynomial K) (rho : K)
    (u v : ℕ → Polynomial K) (n : ℕ) :
    polynomialLogEulerCoefficient B rho (u-v) n =
      polynomialLogEulerCoefficient B rho u n - polynomialLogEulerCoefficient B rho v n := by
  simp only [polynomialLogEulerCoefficient,Pi.sub_apply,map_sub,Finset.sum_sub_distrib]

theorem polynomialLogEulerCoefficient_smul (B : ℕ → Polynomial K) (rho c : K)
    (u : ℕ → Polynomial K) (n : ℕ) :
    polynomialLogEulerCoefficient B rho (c • u) n =
      c • polynomialLogEulerCoefficient B rho u n := by
  simp only [polynomialLogEulerCoefficient,Pi.smul_apply,map_smul,Finset.smul_sum]

variable [CharZero K]

/-- If every resonant low-log coordinate vanishes, so does the whole formal
solution. No log-degree or convergence bound on that solution is supplied. -/
theorem polynomialLogSolution_eq_zero_of_resonance_coefficients
    (B : ℕ → Polynomial K) (rho : K) (hP : B 0 ≠ 0)
    (u : ℕ → Polynomial K)
    (hu : ∀ n,polynomialLogEulerCoefficient B rho u n = 0)
    (hjet : ∀ n j,j < polynomialResonanceMultiplicity rho (B 0) n → (u n).coeff j = 0) :
    u = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hlower : polynomialLogLowerSum B rho n (fun s => u s.val) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      dsimp only
      rw [ih s.val s.isLt]
      exact map_zero _
    have hdiag := hu n
    rw [polynomialLogEulerCoefficient_split,hlower,zero_add] at hdiag
    have hdeg := (shiftedPolynomialDifferentialOperator_kernel_iff
      (rho+(n:K)) (B 0) (u n) hP).mp hdiag
    apply Polynomial.ext
    intro j
    change (u n).coeff j = 0
    by_cases hj : j < polynomialResonanceMultiplicity rho (B 0) n
    · exact hjet n j hj
    · apply Polynomial.coeff_eq_zero_of_degree_lt
      apply hdeg.trans_le
      exact_mod_cast (Nat.le_of_not_gt hj)

/-- Equality is determined by only the low-log coordinates below each exact
resonance multiplicity. Nonresonant indices contribute no coordinates. -/
theorem polynomialLogSolution_unique_of_resonance_coefficients
    (B : ℕ → Polynomial K) (rho : K) (hP : B 0 ≠ 0)
    (u v : ℕ → Polynomial K)
    (hu : ∀ n,polynomialLogEulerCoefficient B rho u n = 0)
    (hv : ∀ n,polynomialLogEulerCoefficient B rho v n = 0)
    (hjet : ∀ n j,j < polynomialResonanceMultiplicity rho (B 0) n →
      (u n).coeff j = (v n).coeff j) : u = v := by
  apply sub_eq_zero.mp
  apply polynomialLogSolution_eq_zero_of_resonance_coefficients B rho hP (u-v)
  · intro n
    rw [polynomialLogEulerCoefficient_sub,hu n,hv n,sub_self]
  · intro n j hj
    simp only [Pi.sub_apply,Polynomial.coeff_sub,hjet n j hj,sub_self]

end StrictEUnit
end

#print axioms StrictEUnit.polynomialLogEulerCoefficient_add
#print axioms StrictEUnit.polynomialLogEulerCoefficient_sub
#print axioms StrictEUnit.polynomialLogEulerCoefficient_smul
#print axioms StrictEUnit.polynomialLogSolution_eq_zero_of_resonance_coefficients
#print axioms StrictEUnit.polynomialLogSolution_unique_of_resonance_coefficients
