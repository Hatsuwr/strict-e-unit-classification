import LogMixingLaurentAssembly

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Actual finite-log Laurent transform, not merely a list of modes. -/
def generalizedLogLaplace (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (f : Polynomial (LaurentSeries K)) : Polynomial (LaurentSeries K) :=
  finiteLogLaurentTranspose (f.natDegree+1)
    (generalizedLogLaplaceSeries rho h (logPolynomialToCoefficientSeries f))

theorem generalizedLogLaplace_uniform_bound (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (f : Polynomial (LaurentSeries K)) :
    HasUniformLogBound (generalizedLogLaplaceSeries rho h
      (logPolynomialToCoefficientSeries f)) (f.natDegree+1) := by
  intro n j hj
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt (generalizedLogLaplaceSeries_degree_bound rho h _ f.natDegree
    (logCoefficient_natDegree_le f) n) (by omega)

theorem generalizedLogLaplace_double_coeff (rho : K) (h : ∀ n : ℕ,rho+(n+1 : ℕ)≠0)
    (f : Polynomial (LaurentSeries K)) (j : ℕ) (n : ℤ) :
    ((generalizedLogLaplace rho h f).coeff j).coeff n=
      (((-1 : K)^n) • logMixingMode rho n
        ((logPolynomialToCoefficientSeries f).coeff (n+1))).coeff j := by
  rw [generalizedLogLaplace,finiteLogLaurentTranspose_double_coeff _ _
    (generalizedLogLaplace_uniform_bound rho h f),generalizedLogLaplaceSeries_coeff]

end StrictEUnit
end
