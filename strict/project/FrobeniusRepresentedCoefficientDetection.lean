import FrobeniusFormalSolutionDimension
import PolynomialLogFrobeniusRingEquation

/-!
# Finite-coordinate detection for literal power-series-supported amplitudes

The exact power-series representation is retained in both directions of the
operator equivalence. The statement is about actual polynomial-log elements,
not a newly defined span. Negative Laurent tails and external base exponents
are not silently discarded.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

theorem logPolynomial_nat_coeff_of_representation
    (p : Polynomial (LaurentSeries K)) (u : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)))
    (n j : ℕ) : (p.coeff j).coeff (n : ℤ) = (u n).coeff j := by
  rw [← logPolynomialToCoefficientSeries_double_coeff,hp,PowerSeries.coeff_coe]
  simp [show ¬ (n : ℤ) < 0 from not_lt.mpr (Int.natCast_nonneg n)]

/-- Exact equivalence of the literal ring equation and every actual
coefficient equation. This includes the converse needed for completeness. -/
theorem scalarTwistedLogOperator_eq_zero_iff_coefficients
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (rho : K)
    (p : Polynomial (LaurentSeries K)) (u : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K))) :
    scalarTwistedLogOperator r b rho p = 0 ↔
      ∀ n,polynomialLogEulerCoefficient
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) rho u n = 0 := by
  constructor
  · intro hz n
    have h := logPolynomialToCoefficientSeries_scalarTwistedLogOperator r b rho p u hp
    rw [hz,map_zero] at h
    have hc := congrArg (fun s : LaurentSeries (Polynomial K) => s.coeff (n : ℤ)) h
    simpa [PowerSeries.coeff_coe,polynomialLogPowerSeriesOperator_coeff] using hc.symm
  · exact scalarTwistedLogOperator_eq_zero_of_coefficients r b rho p u hp

variable [CharZero K]

/-- Two literal represented solutions are equal if their finitely many
resonant low-log coordinates agree. No solution-space dimension is assumed. -/
theorem representedLogSolutions_unique_of_resonance_coefficients
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (rho : K)
    (hP : scalarEulerCoefficientSymbol r
      (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (p q : Polynomial (LaurentSeries K)) (u v : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)))
    (hq : logPolynomialToCoefficientSeries q =
      ((PowerSeries.mk v : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)))
    (hep : scalarTwistedLogOperator r b rho p = 0)
    (heq : scalarTwistedLogOperator r b rho q = 0)
    (hjet : ∀ n j,j < polynomialResonanceMultiplicity rho
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) n →
      (p.coeff j).coeff (n : ℤ) = (q.coeff j).coeff (n : ℤ)) : p = q := by
  have hu := (scalarTwistedLogOperator_eq_zero_iff_coefficients r b rho p u hp).mp hep
  have hv := (scalarTwistedLogOperator_eq_zero_iff_coefficients r b rho q v hq).mp heq
  have huv : u = v := by
    apply polynomialLogSolution_unique_of_resonance_coefficients _ rho hP u v hu hv
    intro n j hj
    simpa only [logPolynomial_nat_coeff_of_representation p u hp,
      logPolynomial_nat_coeff_of_representation q v hq] using hjet n j hj
  apply logPolynomialToCoefficientSeries_injective
  rw [hp,hq,huv]

end StrictEUnit
end

#print axioms StrictEUnit.logPolynomial_nat_coeff_of_representation
#print axioms StrictEUnit.scalarTwistedLogOperator_eq_zero_iff_coefficients
#print axioms StrictEUnit.representedLogSolutions_unique_of_resonance_coefficients
