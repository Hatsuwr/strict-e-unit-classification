import GeneralizedLogLaplaceTransform

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Exact multiplication-by-reciprocal-variable generator identity on full
polynomial-valued Laurent series. All negative modes are retained. -/
theorem generalizedLogLaplaceSeries_z_coeff (rho : K)
    (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (s : LaurentSeries (Polynomial K)) (n : ℤ) :
    (generalizedLogLaplaceSeries rho h (HahnSeries.single (-1 : ℤ) (1 : Polynomial K)*s)).coeff n=
      -shiftedPolynomialDerivative (rho+(n : K)+1)
        ((generalizedLogLaplaceSeries rho h s).coeff (n+1)) := by
  rw [generalizedLogLaplaceSeries_coeff,generalizedLogLaplaceSeries_coeff,map_smul,
    logMixingMode_recurrence rho h]
  have hi : n+1=(n+2)+(-1) := by omega
  have hc : (HahnSeries.single (-1 : ℤ) (1 : Polynomial K)*s).coeff (n+1)=s.coeff (n+2) := by
    rw [hi,HahnSeries.coeff_single_mul_add,one_mul]
  rw [hc]
  have hp : (-1 : K)^(n+1) = -((-1 : K)^n) := by
    rw [zpow_add₀ (neg_ne_zero.mpr one_ne_zero),zpow_one,mul_neg_one]
  rw [hp,neg_smul,neg_neg]
  congr 2
  congr 1
  omega

end StrictEUnit
end
