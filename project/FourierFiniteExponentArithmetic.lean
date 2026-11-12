import FourierFiniteTwistedAmplitudes
import IndicialBinomialRootTransfer

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The EXISTING counted formal twisted family, strengthened only by actual
binomial prefix arithmetic of its exponents. This is not amplitude arithmetic
or a represented independent solution basis. -/
def FourierFiniteTwistedAmplitudeExponentArithmeticData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) : Prop :=
  ∃ hf : Stage56FiniteFuchs A,
    (sameFourierEulerCoefficientSymbols A hf 0).natDegree=ν ∧
    ∃ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
    ∃ rho : Fin ν → K,∃ p : Fin ν → Polynomial (LaurentSeries K),
      (∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j)) ∧
      (∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j)) ∧
      Function.Injective (fun j => (rho j,p j)) ∧
      (∀ j,p j ≠ 0) ∧
      (∀ j,(sameFourierEulerCoefficientSymbols A hf 0).eval (rho j)=0) ∧
      (∀ j,∑ k : Fin (ν+1),Polynomial.C (((stage61_fourierLift A hf).coeff k.val):LaurentSeries K)*
        (fun q : Polynomial (LaurentSeries K) => logPolynomialEuler (1:K) q+rho j • q)^[k.val] (p j)=0) ∧
      (∀ j m,(polynomialLogFrobeniusCoefficient (sameFourierEulerCoefficientSymbols A hf)
        (rho j) (frobeniusRootSeedPolynomial _ (e.symm j)) m).natDegree ≤
          frobeniusRootSeedOrder _ (e.symm j)+ν) ∧
      ∀ j,BinomialPrefixDenominators (rho j)

/-- Destruct and retain the SAME actual hf/e/rho/p witnesses. No new family
is selected to satisfy the arithmetic clause. -/
theorem fourierFiniteTwistedAmplitudeData_with_exponent_arithmetic {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hdata : FourierFiniteTwistedAmplitudeData A)
    (hAll : ∀ hf : Stage56FiniteFuchs A,∀ ξ : K,
      (sameFourierEulerCoefficientSymbols A hf 0).eval ξ=0 → BinomialPrefixDenominators ξ) :
    FourierFiniteTwistedAmplitudeExponentArithmeticData A := by
  obtain ⟨hf,hdeg,e,rho,p,hrho,hp,hinj,hne,hroots,heq,hlog⟩ := hdata
  exact ⟨hf,hdeg,e,rho,p,hrho,hp,hinj,hne,hroots,heq,hlog,
    fun j => hAll hf (rho j) (hroots j)⟩

end StrictEUnit
end
