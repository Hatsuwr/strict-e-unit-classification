import FourierIndicialTwistedAmplitudes
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Counted exponent-amplitude data for the literal SAME Fourier Euler lift.
The exponent remains external. No rationality, actual z^rho, linear independence,
arithmetic amplitude or convergence is asserted by this intermediate packet. -/
def FourierFiniteTwistedAmplitudeData {μ ν : ℕ}
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
      ∀ j m,(polynomialLogFrobeniusCoefficient (sameFourierEulerCoefficientSymbols A hf)
        (rho j) (frobeniusRootSeedPolynomial _ (e.symm j)) m).natDegree ≤
          frobeniusRootSeedOrder _ (e.symm j)+ν

theorem exists_fourierFiniteTwistedAmplitudeData {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν) ≠ 0) : FourierFiniteTwistedAmplitudeData A := by
  classical
  let e := Fintype.equivFinOfCardEq (sameFourierTwistedAmplitude_index_card A hf hc)
  let rho : Fin ν → K := fun j => frobeniusRootSeedExponent _ (e.symm j)
  let p : Fin ν → Polynomial (LaurentSeries K) := fun j => sameFourierTwistedAmplitude A hf (e.symm j)
  refine ⟨hf,sameFourierEulerIndicial_natDegree A hf hc,e,rho,p,
    fun j => rfl,fun j => rfl,?_,?_,?_,?_,?_⟩
  · exact (sameFourierTwistedAmplitude_pair_injective A hf).comp e.symm.injective
  · intro j
    exact sameFourierTwistedAmplitude_nonzero A hf (e.symm j)
  · intro j
    exact frobeniusRootSeedExponent_isRoot _ (e.symm j)
  · intro j
    exact sameFourierTwistedAmplitude_equation A hf hc (e.symm j)
  · intro j m
    exact sameFourierTwistedAmplitude_uniform_log_degree A hf hc (e.symm j) m

end StrictEUnit
end
