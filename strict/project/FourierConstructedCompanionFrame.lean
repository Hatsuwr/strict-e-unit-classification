import ScalarEulerCompanionLogJets
import LogFrameFilteredDenominators

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The retained Fourier companion, using its actual Fourier order and
literal regular lift. This is not identified with the original source companion. -/
def sameFourierPowerSeriesCompanion {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A) :
    Matrix (Fin ν) (Fin ν) (PowerSeries K) :=
  scalarEulerPowerSeriesCompanion ν (fun k =>(stage61_fourierLift A hf).coeff k.val)

/-- Every exact retained indexing has a genuinely nonzero companion-jet
Wronskian. No external z^rho needs to be adjoined to state this amplitude matrix. -/
theorem sameFourierTwistedAmplitude_jet_det_ne_zero [IsAlgClosed K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j)) :
    (Matrix.of (fun i j : Fin ν =>(twistedLogPolynomialEuler (rho j))^[i.val] (p j))).det≠0 := by
  have he : (Matrix.of (fun i j : Fin ν =>(twistedLogPolynomialEuler (rho j))^[i.val] (p j)))=
      frobeniusActualJetMatrix (sameFourierEulerCoefficientSymbols A hf) e := by
    funext i j
    simp only [hrho,hp,frobeniusActualJetMatrix,sameFourierTwistedAmplitude,Matrix.of_apply]
  rw [he]
  exact frobeniusActualJetMatrix_det_ne_zero _ (IsAlgClosed.splits _) e

/-- The same actual indexed columns solve the Fourier companion, including
repeated indicial roots and resonant logarithms. -/
theorem sameFourierTwistedAmplitude_jet_solution {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν)≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j)) :
    ∀ j i,twistedLogPolynomialEuler (rho j) ((twistedLogPolynomialEuler (rho j))^[i.val] (p j))=
      ∑ l,logPowerSeriesEmbedding (sameFourierPowerSeriesCompanion A hf i l)*
        (twistedLogPolynomialEuler (rho j))^[l.val] (p j) := by
  intro j i
  apply scalarTwistedEulerJet_solution ν (fun k =>(stage61_fourierLift A hf).coeff k.val) ?_ _ _ ?_ i
  · simpa only [Fin.val_last,stage61_fourierLift_top,PowerSeries.constantCoeff_C] using
      stage61_fourierCorner_ne_zero A hc
  · rw [hrho,hp]
    exact sameFourierTwistedAmplitude_equation A hf hc (e.symm j)

/-- The original exact amplitudes now supply the inverse and its pole bound.
No determinant, completeness or right-inverse hypothesis is supplied. -/
theorem sameFourierTwistedAmplitude_jet_inverse [IsAlgClosed K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last μ) (Fin.last ν)≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j)) :
    ∃ J : Matrix (Fin ν) (Fin ν) (LaurentSeries (Polynomial K)),∃ W : ℕ,
      (Matrix.of (fun i j : Fin ν =>logPolynomialToCoefficientSeries
        ((twistedLogPolynomialEuler (rho j))^[i.val] (p j))))*J=1 ∧
      J*(Matrix.of (fun i j : Fin ν =>logPolynomialToCoefficientSeries
        ((twistedLogPolynomialEuler (rho j))^[i.val] (p j))))=1 ∧
      (∀ i j a,a< -(W : ℤ) →(J i j).coeff a=0) :=
  logFrame_exists_inverse_with_fixed_pole_bound (sameFourierPowerSeriesCompanion A hf) rho
    (Matrix.of (fun i j : Fin ν =>(twistedLogPolynomialEuler (rho j))^[i.val] (p j)))
    (sameFourierTwistedAmplitude_jet_solution A hf hc e rho p hrho hp)
    (sameFourierTwistedAmplitude_jet_det_ne_zero A hf e rho p hrho hp)

end StrictEUnit
end
