import FrobeniusIntegerShiftIndependence

/-!
# Literal equation transport inside an integral resonance class

Multiplying by the genuine Laurent monomial z^s conjugates the twisted Euler
operator from rho+s to rho. This is proved on all double coefficients and
iterated for the SAME scalar operator, with no normalization or new family.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Literal scalar compatibility for the algebra action used by the twisted
operator, stated separately from the coefficientwise module instance. -/
theorem frobenius_logScalar_double_coeff (c : K)
    (p : Polynomial (LaurentSeries K)) (j : ℕ) (n : ℤ) :
    ((c • p).coeff j).coeff n = c * (p.coeff j).coeff n := by
  rw [Algebra.smul_def,Polynomial.algebraMap_apply,Polynomial.coeff_C_mul,
    LaurentSeries.algebraMap_apply,HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul]

theorem twistedLogPolynomialEuler_double_coeff (rho : K)
    (p : Polynomial (LaurentSeries K)) (j : ℕ) (n : ℤ) :
    ((twistedLogPolynomialEuler rho p).coeff j).coeff n =
      (rho + (n : K)) * (p.coeff j).coeff n +
        (p.coeff (j+1)).coeff n * (j+1 : K) := by
  rw [twistedLogPolynomialEuler,Polynomial.coeff_add,HahnSeries.coeff_add,
    logPolynomialEuler_double_coeff,frobenius_logScalar_double_coeff]
  ring

/-- Conjugation by z^s changes only the external twist; the actual operator
and Laurent-log ring are unchanged. -/
theorem frobeniusIntegerShift_twistedEuler (rho : K) (s : ℤ)
    (p : Polynomial (LaurentSeries K)) :
    twistedLogPolynomialEuler rho (frobeniusIntegerShift s p) =
      frobeniusIntegerShift s (twistedLogPolynomialEuler (rho + (s : K)) p) := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  simp only [twistedLogPolynomialEuler_double_coeff,frobeniusIntegerShift_coeff,Int.cast_sub]
  ring

theorem frobeniusIntegerShift_twistedEuler_iterate (rho : K) (s : ℤ)
    (p : Polynomial (LaurentSeries K)) (k : ℕ) :
    (twistedLogPolynomialEuler rho)^[k] (frobeniusIntegerShift s p) =
      frobeniusIntegerShift s ((twistedLogPolynomialEuler (rho + (s : K)))^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,frobeniusIntegerShift_twistedEuler,
      Function.iterate_succ_apply']

/-- Exact equation transport for every supplied coefficient tuple. The
unnormalized Fourier lift is one instance of this identity. -/
theorem frobeniusIntegerShift_scalarTwistedLogOperator
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (rho : K) (s : ℤ)
    (p : Polynomial (LaurentSeries K)) :
    scalarTwistedLogOperator r b rho (frobeniusIntegerShift s p) =
      frobeniusIntegerShift s (scalarTwistedLogOperator r b (rho + (s : K)) p) := by
  classical
  unfold scalarTwistedLogOperator
  simp_rw [frobeniusIntegerShift_twistedEuler_iterate]
  simp only [frobeniusIntegerShift,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [CharZero K]

/-- Every retained amplitude in this resonance class solves one common
literal twisted Fourier equation after its actual integer Laurent shift. -/
theorem sameFourierTwistedAmplitude_resonance_equation
    {μ ν : ℕ} (A : Fin (μ+1) → Fin (ν+1) → K)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last μ) (Fin.last ν) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (ξ : K) (s : ℤ) (hs : frobeniusRootSeedExponent _ i = ξ + (s : K)) :
    scalarTwistedLogOperator ν (fun k => (stage61_fourierLift A hf).coeff k.val)
      ξ (frobeniusIntegerShift s (sameFourierTwistedAmplitude A hf i)) = 0 := by
  rw [frobeniusIntegerShift_scalarTwistedLogOperator,← hs]
  have heq := sameFourierTwistedAmplitude_equation A hf hc i
  change scalarTwistedLogOperator ν (fun k => (stage61_fourierLift A hf).coeff k.val)
    (frobeniusRootSeedExponent _ i) (sameFourierTwistedAmplitude A hf i) = 0 at heq
  rw [heq,frobeniusIntegerShift,mul_zero]

end StrictEUnit
end

#print axioms StrictEUnit.frobenius_logScalar_double_coeff
#print axioms StrictEUnit.twistedLogPolynomialEuler_double_coeff
#print axioms StrictEUnit.frobeniusIntegerShift_twistedEuler
#print axioms StrictEUnit.frobeniusIntegerShift_twistedEuler_iterate
#print axioms StrictEUnit.frobeniusIntegerShift_scalarTwistedLogOperator
#print axioms StrictEUnit.sameFourierTwistedAmplitude_resonance_equation
