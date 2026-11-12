import ActualFourierCoefficientODE

noncomputable section
namespace StrictEUnit

/-- The unchanged retained coefficient's entire factorial sum is a genuine
strict E-function. The ordinary ODE is derived, not an input premise. -/
theorem sameFourierTwistedAmplitude_coefficient_isStrictEFunction {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu)≠0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) (j : ℕ)
    (ha : HasStrictEArithmetic (fun n =>logAmplitudeFactorialCoefficient
      (sameFourierTwistedAmplitude A hf i) j n)) :
    IsStrictEFunction (stage41_strictSeriesFunction (fun n =>
      logAmplitudeFactorialCoefficient (sameFourierTwistedAmplitude A hf i) j n)) := by
  refine ⟨_,stage41_strictSeries_differentiable ha,stage41_strictSeries_hasSum ha,?_,ha⟩
  exact sameFourierTwistedAmplitude_actual_ODE A hf i j ha
    (sameFourierTwistedAmplitude_coefficient_polynomialODE A hf hc i j)

/-- A retained arithmetic packet now supplies genuine strict E-functions for
ALL log coefficients of the exact retained family. -/
theorem fourierRetainedArithmeticData_coefficient_isStrictEFunction {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu)≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu →AlgebraicComplex) (p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i)) :
    ∀ i j,IsStrictEFunction (stage41_strictSeriesFunction
      (fun n =>logAmplitudeFactorialCoefficient (p i) j n)) := by
  have har := fourierRetainedArithmeticData_strictEArithmetic A ha hf e rho p hrho hp
  intro i j
  have hi := har i j
  rw [hp i] at hi ⊢
  exact sameFourierTwistedAmplitude_coefficient_isStrictEFunction A hf hc (e.symm i) j hi
end StrictEUnit
end
