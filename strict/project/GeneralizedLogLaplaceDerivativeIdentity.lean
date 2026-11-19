import GeneralizedLogLaplaceZIdentity

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def twistedLogCoefficientEuler (rho : K) (s : LaurentSeries (Polynomial K)) :
    LaurentSeries (Polynomial K) where
  coeff n := shiftedPolynomialDerivative (rho+(n : K)) (s.coeff n)
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn
    change s.coeff n≠0
    intro hz
    apply hn
    simp only [hz,map_zero])

def reciprocalLogSeriesDerivative (rho : K) (s : LaurentSeries (Polynomial K)) :
    LaurentSeries (Polynomial K) :=
  -(HahnSeries.single (1 : ℤ) (1 : Polynomial K)*twistedLogCoefficientEuler rho s)

/-- Exact reciprocal derivative generator, including all logarithmic and
negative-index boundary contributions; no extra forcing is postulated. -/
theorem generalizedLogLaplaceSeries_Dz_coeff (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) (n : ℤ) :
    (generalizedLogLaplaceSeries rho h (reciprocalLogSeriesDerivative rho s)).coeff n=
      (generalizedLogLaplaceSeries rho h s).coeff (n-1) := by
  rw [generalizedLogLaplaceSeries_coeff,generalizedLogLaplaceSeries_coeff]
  have hc : (reciprocalLogSeriesDerivative rho s).coeff (n+1)=
      -shiftedPolynomialDerivative (rho+(n : K)) (s.coeff n) := by
    rw [reciprocalLogSeriesDerivative,HahnSeries.coeff_neg,HahnSeries.coeff_single_mul_add,one_mul]
    rfl
  rw [hc]
  have hn : n-1+1=n := by omega
  have hk : rho+((n-1 : ℤ) : K)+1=rho+(n : K) := by push_cast;ring
  have hr := logMixingMode_recurrence_right rho h (n-1) (s.coeff n)
  rw [hn,hk] at hr
  have hneg : logMixingMode rho n (-shiftedPolynomialDerivative (rho+(n : K)) (s.coeff n))=
      -logMixingMode rho (n-1) (s.coeff n) := by
    simpa only [neg_one_smul,hr] using
      logMixingMode_smul rho (-1) h n (shiftedPolynomialDerivative (rho+(n : K)) (s.coeff n))
  rw [hneg,hn,smul_neg]
  have hp : (-1 : K)^n = -((-1 : K)^(n-1)) := by
    conv_lhs => rw [← hn]
    rw [zpow_add₀ (neg_ne_zero.mpr one_ne_zero),zpow_one,mul_neg_one]
  rw [hp,neg_smul,neg_neg]

end StrictEUnit
end
