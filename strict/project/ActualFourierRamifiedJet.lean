import RamifiedJetDeterminant
import FourierConstructedCompanionFrame
noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
theorem actualFourier_ramified_jet_det_ne_zero {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → K) (p : Fin nu → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (N : ℕ) (hN : N ≠ 0) (m : Fin nu → ℤ)
    (hm : ∀ j, (m j : K) / (N : K) = rho j) :
    (Matrix.of (fun i j : Fin nu => (stage38_sourceEuler N)^[i.val]
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j)))).det ≠ 0 := by
  exact ramified_external_power_jet_det_ne_zero N hN m rho hm p
    (sameFourierTwistedAmplitude_jet_det_ne_zero A hf e rho p hrho hp)
end StrictEUnit
end
