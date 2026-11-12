import NaturalResonanceLogMatrix

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Every log coefficient is recovered from the log-free row and powers of
the actual square nilpotent matrix, with the literal factorial normalization. -/
theorem naturalResonanceLogMatrix_factorial_coefficients
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (d : ℕ) (j : polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) (m : ℕ) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    (d.factorial:K)*(naturalResonanceFrobeniusCoefficients B rho j m).coeff d=
      ∑ i,((naturalResonanceLogMatrix r b rho hP)^d) i j *
        (naturalResonanceFrobeniusCoefficients B rho i m).coeff 0 := by
  have he := congrArg (fun p : Polynomial K =>p.coeff 0)
    (naturalResonanceLogMatrix_power_equation r b rho hP d j m)
  simpa only [Polynomial.coeff_iterate_derivative,zero_add,Nat.descFactorial_self,
    nsmul_eq_mul,Polynomial.finset_sum_coeff,Polynomial.coeff_smul,smul_eq_mul] using he

/-- The power formula is an actual coefficient equality; no formal exponential
or base-unit existence hypothesis is introduced. -/
theorem naturalResonanceLogMatrix_coefficients
    (r : ℕ) (b : Fin (r+1) →PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (d : ℕ) (j : polynomialLogResonanceCoordinateIndex rho
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0)) (m : ℕ) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    (naturalResonanceFrobeniusCoefficients B rho j m).coeff d=
      (d.factorial:K)⁻¹ * (∑ i,((naturalResonanceLogMatrix r b rho hP)^d) i j *
        (naturalResonanceFrobeniusCoefficients B rho i m).coeff 0) := by
  dsimp only
  rw [← naturalResonanceLogMatrix_factorial_coefficients r b rho hP d j m,
    ← mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)),one_mul]
end StrictEUnit
end
