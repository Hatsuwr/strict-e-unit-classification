import RetainedCoefficientTaylorSupport

noncomputable section
namespace StrictEUnit
/-- For the actual retained amplitude, support is proved, not assumed. Only
its yet-to-be-instantiated scalar Laurent ODE remains an explicit premise. -/
theorem sameFourierTwistedAmplitude_actual_ODE {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) (j : ℕ)
    (ha : HasStrictEArithmetic (fun n =>logAmplitudeFactorialCoefficient
      (sameFourierTwistedAmplitude A hf i) j n))
    (ho : HasPolynomialScalarDifferentialRelation (k:=AlgebraicComplex)
      stage14_laurentAlgebraDerivation ((sameFourierTwistedAmplitude A hf i).coeff j)) :
    HasAlgebraicPolynomialODE (stage41_strictSeriesFunction (fun n =>
      logAmplitudeFactorialCoefficient (sameFourierTwistedAmplitude A hf i) j n)) :=
  logAmplitudeFactorial_actual_ODE _ j ha
    (sameFourierTwistedAmplitude_coefficient_embedding A hf i j) ho
end StrictEUnit
end
