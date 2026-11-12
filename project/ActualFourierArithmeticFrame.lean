import ActualFourierLeadingMonomial
import Stage33ScalarNormalFormFrame
noncomputable section
namespace StrictEUnit

theorem actualFourier_arithmeticFrame {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0) (hnu : 0 < nu)
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      BinomialPrefixDenominators x) :
    ∃ F : Stage27ArithmeticFrame (algebraicClosure ℚ ℂ).toSubfield (Fin nu),
      F.B = stage28_laurentCompanion (algebraicClosure ℚ ℂ).toSubfield
        nu mu (stage61_fourierCorner A) (stage53_fourierCoeff A) := by
  obtain ⟨S⟩ := actualFourier_scalarNormalForm_of_arithmetic A ha hf hc hroot
  exact ⟨stage33_arithmeticFrame_of_scalarNormalForm nu mu (stage61_fourierCorner A)
    (stage53_fourierCoeff A) (stage61_fourierCorner_ne_zero A hc)
    (actualFourier_leading_monomial A hf) hnu S, rfl⟩
end StrictEUnit
end
