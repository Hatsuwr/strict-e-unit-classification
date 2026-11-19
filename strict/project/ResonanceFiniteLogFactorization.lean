import FiniteLogMatrixExponential

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Each actual coefficient polynomial is the log-free row times the
constructed square unit. All factorials and index orientations are literal. -/
theorem naturalResonanceFrobenius_finiteLog_factorization
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (j : polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) (m : ℕ) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    let N := naturalResonanceLogMatrix r b rho hP
    naturalResonanceFrobeniusCoefficients B rho j m=
      ∑ i,Polynomial.C ((naturalResonanceFrobeniusCoefficients B rho i m).coeff 0)*
        (finiteLogMatrixUnit N (naturalResonanceLogMatrix_isNilpotent r b rho hP)).val i j := by
  dsimp only
  apply Polynomial.ext
  intro d
  rw [naturalResonanceLogMatrix_coefficients r b rho hP d j m]
  simp only [Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul,
    finiteLogMatrixUnit_val,finiteLogMatrixExponential_coeff _
      (naturalResonanceLogMatrix_isNilpotent r b rho hP),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end StrictEUnit
end
