import StrictENaturalMonomialTransport
import FourierNaturalResonanceBasis
import ActualResonanceAmplitudeFactorization

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- The log-free row of every natural resonance block consists of actual
entire strict E-functions, including its required natural integer shifts. -/
theorem fourierRetainedArithmeticData_natural_logFree_row {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu)≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu →AlgebraicComplex) (p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i))
    (xi : AlgebraicComplex) :
    ∃ F : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0) →
        subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      (∀ i,IsStrictEFunction (F i).val.val) ∧
      ∀ i,stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield (F i)=
        (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi i).coeff 0 := by
  have har := fourierRetainedArithmeticData_strictEArithmetic A ha hf e rho p hrho hp
  have hstrict := fourierRetainedArithmeticData_coefficient_isStrictEFunction A ha hf hc e rho p hrho hp
  have hex (i : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0)) :
      ∃ F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
        IsStrictEFunction F.val.val ∧
        stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield F=
          (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi i).coeff 0 := by
    obtain ⟨j,hj,he⟩ := naturalResonanceFrobeniusAmplitude_retained_fourier_index A hf hc e rho p hrho hp xi i
    let G := stage41_strictSeriesRealization (fun n =>logAmplitudeFactorialCoefficient (p j) 0 n) (har j 0)
    refine ⟨naturalShiftEntire i.1.val G,naturalShiftEntire_strict _ G (hstrict j 0),?_⟩
    rw [naturalShiftEntire_laurent,he,frobeniusIntegerShift,Polynomial.coeff_C_mul]
    have hG : stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield G=(p j).coeff 0 := by
      rw [stage14_subfieldEntireLaurentAlgHom_apply,
        (logAmplitudeFactorial_actual_realization (p j) 0 (har j 0)).2.2,hp j]
      exact sameFourierTwistedAmplitude_coefficient_embedding A hf (e.symm j) 0
    rw [hG]
    rfl
  choose F hs he using hex
  exact ⟨F,hs,he⟩
end StrictEUnit
end
