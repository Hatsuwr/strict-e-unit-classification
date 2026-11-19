import FrobeniusLaurentCoefficientTransport

/-!
# Arbitrary Laurent tails: derived bounded logarithms and unique realization

Every polynomial-valued Laurent-series solution is normalized by its actual
integer order. Its power-series part satisfies the same operator at the
translated external twist, so the full coefficient basis theorem applies.
The input need not have a uniform log bound. Fractional/external exponents
are not adjoined, and no arithmetic or convergence is asserted.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

def laurentNormalizedCoefficients (s : LaurentSeries (Polynomial K)) : ℕ → Polynomial K :=
  fun n => PowerSeries.coeff (Polynomial K) n s.powerSeriesPart

theorem laurentNormalizedCoefficients_representation (s : LaurentSeries (Polynomial K)) :
    laurentCoefficientShift s.order
      ((PowerSeries.mk (laurentNormalizedCoefficients s) : PowerSeries (Polynomial K)) :
        LaurentSeries (Polynomial K)) = s := by
  have hp : PowerSeries.mk (laurentNormalizedCoefficients s) = s.powerSeriesPart := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_mk]
    rfl
  rw [hp,laurentCoefficientShift,LaurentSeries.single_order_mul_powerSeriesPart]

theorem laurentNormalizedCoefficients_solution
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (s : LaurentSeries (Polynomial K)) (hs : scalarTwistedCoefficientOperator r b ξ s = 0) :
    ∀ n,polynomialLogEulerCoefficient
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)))
      (ξ+(s.order : K)) (laurentNormalizedCoefficients s) n = 0 := by
  apply (scalarTwistedCoefficientOperator_powerSeries_eq_zero_iff r b _ _).mp
  apply laurentCoefficientShift_injective s.order
  rw [← laurentCoefficientShift_scalarTwistedCoefficientOperator,
    laurentNormalizedCoefficients_representation,hs,laurentCoefficientShift,mul_zero]

variable [CharZero K]

/-- Arbitrary negative Laurent tails are included. The finite-log condition
is a consequence of the differential equation, not a premise. -/
theorem polynomialLogLaurentSolution_uniform_log_bound
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (s : LaurentSeries (Polynomial K)) (hs : scalarTwistedCoefficientOperator r b ξ s = 0) :
    HasUniformLogBound s (2 * (scalarEulerCoefficientSymbol r
      (fun i k => PowerSeries.coeff K k (b i)) 0).natDegree) := by
  have hu := laurentNormalizedCoefficients_solution r b ξ s hs
  have hb := polynomialLogFormalSolution_uniform_log_bound r b (ξ+(s.order : K)) hP _ hu
  have hps := uniformLogBound_powerSeries_mk (laurentNormalizedCoefficients s) _ hb
  intro n j hj
  have he := laurentNormalizedCoefficients_representation s
  have hc := congrArg (fun v : LaurentSeries (Polynomial K) => (v.coeff n).coeff j) he
  dsimp only at hc
  rw [laurentCoefficientShift_coeff] at hc
  rw [← hc]
  exact hps (n-s.order) j hj

/-- Every actual Laurent coefficient solution has a UNIQUE literal
polynomial-log realization satisfying the SAME operator equation. -/
theorem polynomialLogLaurentSolution_existsUnique_realization
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (s : LaurentSeries (Polynomial K)) (hs : scalarTwistedCoefficientOperator r b ξ s = 0) :
    ∃! p : Polynomial (LaurentSeries K),
      logPolynomialToCoefficientSeries p = s ∧ scalarTwistedLogOperator r b ξ p = 0 := by
  let d := 2 * (scalarEulerCoefficientSymbol r
    (fun i k => PowerSeries.coeff K k (b i)) 0).natDegree
  let p := finiteLogLaurentTranspose d s
  have hp := logPolynomialToCoefficientSeries_finiteLogLaurentTranspose d s
    (polynomialLogLaurentSolution_uniform_log_bound r b ξ hP s hs)
  refine ⟨p,⟨hp,?_⟩,?_⟩
  · apply logPolynomialToCoefficientSeries_injective
    rw [map_zero,logPolynomialToCoefficientSeries_scalarTwistedCoefficientOperator,hp,hs]
  · intro q hq
    exact logPolynomialToCoefficientSeries_injective (hq.1.trans hp.symm)

/-- A canonical integer normalization gives every Laurent solution a UNIQUE
finite expansion in the already constructed natural-resonance coefficients.
The shift is s.order and the external twist is exactly xi+s.order. -/
theorem polynomialLogLaurentSolution_existsUnique_normalized_expansion
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (s : LaurentSeries (Polynomial K)) (hs : scalarTwistedCoefficientOperator r b ξ s = 0) :
    ∃! c : polynomialLogResonanceCoordinateIndex (ξ+(s.order : K))
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) → K,
      laurentNormalizedCoefficients s = ∑ i,c i • naturalResonanceFrobeniusCoefficients
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)))
        (ξ+(s.order : K)) i :=
  polynomialLogFormalSolution_existsUnique_expansion r b (ξ+(s.order : K)) hP _
    (laurentNormalizedCoefficients_solution r b ξ s hs)

end StrictEUnit
end

#print axioms StrictEUnit.laurentNormalizedCoefficients_representation
#print axioms StrictEUnit.laurentNormalizedCoefficients_solution
#print axioms StrictEUnit.polynomialLogLaurentSolution_uniform_log_bound
#print axioms StrictEUnit.polynomialLogLaurentSolution_existsUnique_realization
#print axioms StrictEUnit.polynomialLogLaurentSolution_existsUnique_normalized_expansion
