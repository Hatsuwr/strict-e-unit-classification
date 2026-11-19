import FrobeniusNaturalResonanceBasis

/-!
# Uniform log bounds and exact realization of every coefficient solution

No uniform bound or representation hypothesis is supplied. The proved finite
basis expansion supplies a common cutoff, twice the indicial degree. The exact
transpose then gives the unique literal polynomial-log solution.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem naturalResonanceFrobeniusCoefficients_uniform_log_bound
    (B : ℕ → Polynomial K) (ξ : K)
    (i : polynomialLogResonanceCoordinateIndex ξ (B 0)) (n j : ℕ)
    (hj : 2 * (B 0).natDegree ≤ j) :
    (naturalResonanceFrobeniusCoefficients B ξ i n).coeff j = 0 := by
  have hm : polynomialResonanceMultiplicity ξ (B 0) i.1.1 ≤ (B 0).natDegree := by
    simpa using polynomialResonanceMultiplicity_sum_le ξ (B 0) {i.1.1}
  have hi := i.2.isLt
  unfold naturalResonanceFrobeniusCoefficients naturalCoefficientShift
  split_ifs
  · apply polynomialLogFrobeniusCoefficient_coeff_eq_zero
    simp only [Polynomial.natDegree_X_pow]
    omega
  · exact Polynomial.coeff_zero j

/-- All solutions of the full coefficient equation have the same explicit
logarithmic cutoff. This is deduced from the proved basis, not assumed. -/
theorem polynomialLogFormalSolution_uniform_log_bound
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (u : ℕ → Polynomial K)
    (hu : ∀ m,polynomialLogEulerCoefficient
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ u m = 0) :
    ∀ n j,2 * (scalarEulerCoefficientSymbol r
      (fun i k => PowerSeries.coeff K k (b i)) 0).natDegree ≤ j → (u n).coeff j = 0 := by
  obtain ⟨c,hc,-⟩ := polynomialLogFormalSolution_existsUnique_expansion r b ξ hP u hu
  intro n j hj
  rw [hc]
  simp only [Finset.sum_apply,Pi.smul_apply,Polynomial.finset_sum_coeff,Polynomial.coeff_smul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [naturalResonanceFrobeniusCoefficients_uniform_log_bound _ ξ i n j hj,smul_zero]

/-- Every coefficient solution is represented by exactly one literal
polynomial-log element, and that element satisfies the actual ring equation. -/
theorem polynomialLogFormalSolution_existsUnique_realization
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (u : ℕ → Polynomial K)
    (hu : ∀ m,polynomialLogEulerCoefficient
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ u m = 0) :
    ∃! p : Polynomial (LaurentSeries K),
      logPolynomialToCoefficientSeries p =
        ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) ∧
      scalarTwistedLogOperator r b ξ p = 0 := by
  let d := 2 * (scalarEulerCoefficientSymbol r
    (fun i k => PowerSeries.coeff K k (b i)) 0).natDegree
  let p := finiteLogLaurentTranspose d
    ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K))
  have hp := logPolynomialToCoefficientSeries_transpose_powerSeries_mk u d
    (polynomialLogFormalSolution_uniform_log_bound r b ξ hP u hu)
  refine ⟨p,⟨hp,(scalarTwistedLogOperator_eq_zero_iff_coefficients r b ξ p u hp).mpr hu⟩,?_⟩
  intro q hq
  exact logPolynomialToCoefficientSeries_injective (hq.1.trans hp.symm)

end StrictEUnit
end

#print axioms StrictEUnit.naturalResonanceFrobeniusCoefficients_uniform_log_bound
#print axioms StrictEUnit.polynomialLogFormalSolution_uniform_log_bound
#print axioms StrictEUnit.polynomialLogFormalSolution_existsUnique_realization
