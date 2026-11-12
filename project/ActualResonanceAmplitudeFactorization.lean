import ResonanceFiniteLogFactorization

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem naturalResonanceFrobeniusAmplitude_double_coeff
    (B : ℕ →Polynomial K) (rho : K)
    (j : polynomialLogResonanceCoordinateIndex rho (B 0)) (d : ℕ) (m : ℤ) :
    ((naturalResonanceFrobeniusAmplitude B rho j).coeff d).coeff m=
      if m<0 then 0 else (naturalResonanceFrobeniusCoefficients B rho j m.natAbs).coeff d := by
  rw [← logPolynomialToCoefficientSeries_double_coeff,
    naturalResonanceFrobeniusAmplitude_representation,PowerSeries.coeff_coe]
  split_ifs
  · exact Polynomial.coeff_zero d
  · rw [PowerSeries.coeff_mk]

/-- Full actual Laurent-log amplitudes, not only individual coefficients,
factor through the SAME square finite exponential unit and their log-free row. -/
theorem naturalResonanceFrobeniusAmplitude_square_factorization
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (j : polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    let N := naturalResonanceLogMatrix r b rho hP
    naturalResonanceFrobeniusAmplitude B rho j=
      ∑ i,Polynomial.C ((naturalResonanceFrobeniusAmplitude B rho i).coeff 0)*
        Polynomial.map (algebraMap K (LaurentSeries K))
          ((finiteLogMatrixUnit N (naturalResonanceLogMatrix_isNilpotent r b rho hP)).val i j) := by
  dsimp only
  apply Polynomial.ext
  intro d
  apply HahnSeries.ext
  funext m
  simp only [Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_map,
    HahnSeries.coeff_sum,LaurentSeries.algebraMap_apply,HahnSeries.C_apply,
    HahnSeries.coeff_mul_single_zero,naturalResonanceFrobeniusAmplitude_double_coeff]
  by_cases hm : m<0
  · simp only [hm,if_true,zero_mul,Finset.sum_const_zero]
  · simp only [hm,if_false]
    have he := congrArg (fun q : Polynomial K =>q.coeff d)
      (naturalResonanceFrobenius_finiteLog_factorization r b rho hP j m.natAbs)
    simpa only [Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul] using he
end StrictEUnit
end
