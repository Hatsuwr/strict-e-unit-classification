import ActualRamifiedBlockRow
import ActualGlobalBaseUnit
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem actualFourier_ramified_analytic_block {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (xi : AlgebraicComplex) (N : ℕ) (hN : N ≠ 0) (m : ℤ) :
    ∃ F : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0) →
      subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      (∀ i, IsStrictEFunction (F i).val.val) ∧
      ∀ j, Polynomial.C (HahnSeries.single m (1 : AlgebraicComplex)) *
        stage38_logRamification N hN
          (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi j) =
        ∑ i, Polynomial.C (show LaurentSeries AlgebraicComplex from stage14_subfieldEntireLaurentAlgHom
          (algebraicClosure ℚ ℂ).toSubfield
          (stage17_arithmeticPowerPullback (algebraicClosure ℚ ℂ).toSubfield N hN (F i))) *
          laurentLogToSeriesPolynomial
            ((fixedExponentBaseUnit m (actualNaturalLogMatrix A hf hc xi)
              (actualNaturalLogMatrix_nilpotent A hf hc xi)).val i j) := by
  obtain ⟨F,hs,he⟩ := fourierRetainedArithmeticData_analytic_square_block
    A ha hf hc e rho p hrho hp xi
  refine ⟨F,hs,?_⟩
  intro j
  have h := fixedExponentBaseUnit_series_row N hN
    (fun i => Polynomial.C (show LaurentSeries AlgebraicComplex from stage14_subfieldEntireLaurentAlgHom
      (algebraicClosure ℚ ℂ).toSubfield (F i)))
    (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi j)
    m (actualNaturalLogMatrix A hf hc xi)
    (actualNaturalLogMatrix_nilpotent A hf hc xi) j (he j)
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x => x * _)
  exact ramified_analytic_log_image (algebraicClosure ℚ ℂ).toSubfield N hN (F i)
end StrictEUnit
end
