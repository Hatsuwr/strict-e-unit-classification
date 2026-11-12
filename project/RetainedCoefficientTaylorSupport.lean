import RetainedCoefficientODETransfer
import FourierIndicialTwistedAmplitudes

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem polynomialLogFrobeniusAmplitude_coefficient_embedding
    (B : ℕ → Polynomial K) (rho : K) (u : Polynomial K) (j : ℕ) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk (fun n =>
      ((polynomialLogFrobeniusAmplitude B rho u).coeff j).coeff (n:ℤ)))=
      (polynomialLogFrobeniusAmplitude B rho u).coeff j := by
  apply HahnSeries.ext
  funext n
  change ((PowerSeries.mk (fun m =>((polynomialLogFrobeniusAmplitude B rho u).coeff j).coeff (m:ℤ)) : PowerSeries K) : LaurentSeries K).coeff n = _
  rw [PowerSeries.coeff_coe]
  split_ifs with hn
  · unfold polynomialLogFrobeniusAmplitude
    rw [finiteLogLaurentTranspose_double_coeff _ _ (uniformLogBound_powerSeries_mk _ _
      (polynomialLogFrobeniusCoefficient_coeff_eq_zero B rho u))]
    rw [PowerSeries.coeff_coe,if_pos hn,Polynomial.coeff_zero]
  · rw [PowerSeries.coeff_mk,Int.natAbs_of_nonneg (by omega)]

theorem sameFourierTwistedAmplitude_coefficient_embedding {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →K) (hf : Stage56FiniteFuchs A)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) (j : ℕ) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk (fun n =>
      ((sameFourierTwistedAmplitude A hf i).coeff j).coeff (n:ℤ)))=
      (sameFourierTwistedAmplitude A hf i).coeff j :=
  polynomialLogFrobeniusAmplitude_coefficient_embedding _ _ _ j
end StrictEUnit
end
