import LaurentLogOperatorBridge
import PolynomialLogFrobeniusRecurrence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The actual twisted Laurent-log equation for the constructed amplitude

SOURCE-ONLY DRAFT. Neither this file nor LaurentLogOperatorBridge has been
compiled or checked. PolynomialLogFrobeniusRecurrence is also source-only at
the time of preparation; the intended frozen source has SHA256
46a7356a4cbbd0073cbe49e39376a9271392f40cb79b75333e69bf41a06244fd.

The conclusion is a literal sum of products in Polynomial (LaurentSeries K),
with coefficients b_i in PowerSeries K and the actual shifted log Euler
operator. Only the convolution calculation is performed in PowerSeries.
The amplitude is the same finiteLogLaurentTranspose constructed by the
recurrence. The formal exponent z^rho remains outside the ring. No full basis,
normalized Stage43 equation, ramification, or arithmetic bounds are asserted.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The actual left scalar differential operator on the Laurent-log ring. -/
def scalarTwistedLogOperator (r : ℕ) (b : Fin (r + 1) → PowerSeries K)
    (rho : K) (p : Polynomial (LaurentSeries K)) :
    Polynomial (LaurentSeries K) :=
  ∑ i : Fin (r + 1), Polynomial.C (b i : LaurentSeries K) *
    (twistedLogPolynomialEuler rho)^[i.val] p

/-- The genuine power-series expression to which the ring operator transports. -/
def polynomialLogPowerSeriesOperator (r : ℕ)
    (b : Fin (r + 1) → PowerSeries K) (rho : K) (u : ℕ → Polynomial K) :
    PowerSeries (Polynomial K) :=
  ∑ i : Fin (r + 1),
    PowerSeries.map (Polynomial.C : K →+* Polynomial K) (b i) *
      PowerSeries.mk (fun n =>
        (shiftedPolynomialDerivative (rho + (n : K)))^[i.val] (u n))

/-- The only product-coefficient calculation uses ordinary power series.
The right index s is retained so its Euler shift is rho+s in the application. -/
theorem polynomialLogPowerSeries_product_coeff
    (b : PowerSeries K) (v : ℕ → Polynomial K) (n : ℕ) :
    PowerSeries.coeff (Polynomial K) n
      (PowerSeries.map (Polynomial.C : K →+* Polynomial K) b * PowerSeries.mk v) =
      ∑ s : Fin (n + 1), PowerSeries.coeff K (n - s.val) b • v s.val := by
  classical
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [← Finset.Nat.sum_antidiagonal_swap
    (f := fun z : ℕ × ℕ => Polynomial.C (PowerSeries.coeff K z.1 b) * v z.2)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ s ∈ Finset.range (n + 1),
    Polynomial.C (PowerSeries.coeff K (n - s) b) * v s) = _
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Polynomial.smul_eq_C_mul]

/-- All of the previously defined recurrence convolution is now the exact
coefficient of a product of actual power series. -/
theorem polynomialLogPowerSeriesOperator_coeff
    (r : ℕ) (b : Fin (r + 1) → PowerSeries K) (rho : K)
    (u : ℕ → Polynomial K) (n : ℕ) :
    PowerSeries.coeff (Polynomial K) n
      (polynomialLogPowerSeriesOperator r b rho u) =
      polynomialLogEulerCoefficient
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)))
        rho u n := by
  classical
  simp only [polynomialLogPowerSeriesOperator, map_sum,
    polynomialLogPowerSeries_product_coeff]
  rw [Finset.sum_comm]
  exact (polynomialLogEulerCoefficient_scalar_formula r
    (fun i k => PowerSeries.coeff K k (b i)) rho u n).symm

/-- Ring homomorphism laws transport multiplication before coefficient
extraction. No general Hahn support-antidiagonal calculation is needed. -/
theorem logPolynomialToCoefficientSeries_scalarTwistedLogOperator
    (r : ℕ) (b : Fin (r + 1) → PowerSeries K) (rho : K)
    (p : Polynomial (LaurentSeries K)) (u : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) :
        LaurentSeries (Polynomial K))) :
    logPolynomialToCoefficientSeries (scalarTwistedLogOperator r b rho p) =
      (polynomialLogPowerSeriesOperator r b rho u : LaurentSeries (Polynomial K)) := by
  classical
  unfold scalarTwistedLogOperator polynomialLogPowerSeriesOperator
  change logPolynomialToCoefficientSeries
    (∑ i : Fin (r + 1), Polynomial.C (b i : LaurentSeries K) *
      (twistedLogPolynomialEuler rho)^[i.val] p) =
    (HahnSeries.ofPowerSeries ℤ (Polynomial K))
      (∑ i : Fin (r + 1), PowerSeries.map Polynomial.C (b i) *
        PowerSeries.mk (fun n =>
          (shiftedPolynomialDerivative (rho + (n : K)))^[i.val] (u n)))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, logPolynomialToCoefficientSeries_C,
    logLaurentCoefficientMap_powerSeries,
    logPolynomialToCoefficientSeries_twistedEuler_iterate_powerSeries rho p u hp]
  exact (PowerSeries.coe_mul _ _).symm

/-- General implication from exact represented coefficients to the actual
ring equation. The representation premise includes all integer exponents. -/
theorem scalarTwistedLogOperator_eq_zero_of_coefficients
    (r : ℕ) (b : Fin (r + 1) → PowerSeries K) (rho : K)
    (p : Polynomial (LaurentSeries K)) (u : ℕ → Polynomial K)
    (hp : logPolynomialToCoefficientSeries p =
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) :
        LaurentSeries (Polynomial K)))
    (hu : ∀ n, polynomialLogEulerCoefficient
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)))
      rho u n = 0) :
    scalarTwistedLogOperator r b rho p = 0 := by
  have hQ : polynomialLogPowerSeriesOperator r b rho u = 0 := by
    apply PowerSeries.ext
    intro n
    rw [polynomialLogPowerSeriesOperator_coeff, hu n, map_zero]
  apply logPolynomialToCoefficientSeries_injective
  rw [map_zero,
    logPolynomialToCoefficientSeries_scalarTwistedLogOperator r b rho p u hp,
    hQ, PowerSeries.coe_zero]

/-- The checked transpose supplies the complete representation premise;
neither negative support nor the operator equation is assumed separately. -/
theorem finiteLogLaurentTranspose_scalarTwistedLogOperator_eq_zero
    (r : ℕ) (b : Fin (r + 1) → PowerSeries K) (rho : K)
    (u : ℕ → Polynomial K) (d : ℕ)
    (hbound : ∀ n j, d ≤ j → (u n).coeff j = 0)
    (hu : ∀ n, polynomialLogEulerCoefficient
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)))
      rho u n = 0) :
    scalarTwistedLogOperator r b rho
      (finiteLogLaurentTranspose d
        ((PowerSeries.mk u : PowerSeries (Polynomial K)) :
          LaurentSeries (Polynomial K))) = 0 :=
  scalarTwistedLogOperator_eq_zero_of_coefficients r b rho _ u
    (logPolynomialToCoefficientSeries_transpose_powerSeries_mk u d hbound) hu

section CharZero
variable [CharZero K]

/-- The SAME constructed Frobenius amplitude solves the literal shifted
Laurent-log differential equation. No nonresonance assumption is used. -/
theorem polynomialLogFrobeniusAmplitude_ring_equation
    (r : ℕ) (b : Fin (r + 1) → PowerSeries K) (rho : K) (u0 : Polynomial K)
    (hP : scalarEulerCoefficientSymbol r
      (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (hu0 : shiftedPolynomialDifferentialOperator rho
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)
      u0 = 0) :
    ∑ i : Fin (r + 1), Polynomial.C (b i : LaurentSeries K) *
      (fun p : Polynomial (LaurentSeries K) =>
        logPolynomialEuler (1 : K) p + rho • p)^[i.val]
          (polynomialLogFrobeniusAmplitude
            (scalarEulerCoefficientSymbol r
              (fun i k => PowerSeries.coeff K k (b i))) rho u0) = 0 := by
  let B := scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))
  change scalarTwistedLogOperator r b rho (polynomialLogFrobeniusAmplitude B rho u0) = 0
  unfold polynomialLogFrobeniusAmplitude
  apply finiteLogLaurentTranspose_scalarTwistedLogOperator_eq_zero
  · exact polynomialLogFrobeniusCoefficient_coeff_eq_zero B rho u0
  · exact polynomialLogFrobeniusCoefficient_equation B rho u0 hP hu0

end CharZero
end StrictEUnit

#print axioms StrictEUnit.scalarTwistedLogOperator
#print axioms StrictEUnit.polynomialLogPowerSeriesOperator
#print axioms StrictEUnit.polynomialLogPowerSeries_product_coeff
#print axioms StrictEUnit.polynomialLogPowerSeriesOperator_coeff
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_scalarTwistedLogOperator
#print axioms StrictEUnit.scalarTwistedLogOperator_eq_zero_of_coefficients
#print axioms StrictEUnit.finiteLogLaurentTranspose_scalarTwistedLogOperator_eq_zero
#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_ring_equation
