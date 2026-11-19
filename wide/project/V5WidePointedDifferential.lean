import Stage14LaurentPolynomialODEClosure
import V5LaurentBaseDerivation
import V5WidePointedFundamental
import V5LaurentDerivationAgreement

noncomputable section
attribute [-instance] HahnSeries.instModule
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Centering the original coordinate at 1 preserves ordinary differentiation. -/
theorem v5WidePointedLaurentBase_differential (b : LaurentPolynomial K) :
    laurentOrdinaryDerivation (v5WidePointedLaurentBase K b) =
      v5WidePointedLaurentBase K (v5LaurentBaseDerivation b) := by
  let φ := v5WidePointedLaurentBase K
  let d := (v5LaurentBaseDerivation : Derivation K (LaurentPolynomial K) _)
  let D := (stage14_laurentAlgebraDerivation : Derivation K (LaurentSeries K) _)
  have hpos : D (φ (LaurentPolynomial.T 1)) = φ (d (LaurentPolynomial.T 1)) := by
    change laurentOrdinaryDerivation (HahnSeries.ofPowerSeries ℤ K
      (v5WidePointedBase K (LaurentPolynomial.T 1))) = _
    rw [v5WidePointedBase_T, zpow_one, v5WidePointedParameter_val,
      laurentOrdinaryDerivation_ofPowerSeries]
    simp only [map_add, (PowerSeries.derivative K).map_one_eq_zero, PowerSeries.derivative_X, zero_add, map_one]
    change 1 = φ (v5LaurentBaseDerivation (LaurentPolynomial.T 1))
    simp only [v5LaurentBaseDerivation_T, Int.cast_one, sub_self,
      map_one, LaurentPolynomial.T_zero, one_mul, map_one]
  have hm : (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) : LaurentPolynomial K) = 1 := by
    rw [← LaurentPolynomial.T_add]; norm_num
  have hneg : D (φ (LaurentPolynomial.T (-1))) = φ (d (LaurentPolynomial.T (-1))) := by
    have h1 := D.leibniz (φ (LaurentPolynomial.T 1)) (φ (LaurentPolynomial.T (-1)))
    have h2 := congrArg φ (d.leibniz (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))
    simp only [← map_mul, hm, map_one, D.map_one_eq_zero, smul_eq_mul] at h1
    simp only [hm, d.map_one_eq_zero, map_zero, smul_eq_mul, map_add, map_mul] at h2
    rw [hpos] at h1
    have hh := h1.symm.trans h2
    have hc : φ (LaurentPolynomial.T 1) * D (φ (LaurentPolynomial.T (-1))) =
        φ (LaurentPolynomial.T 1) * φ (d (LaurentPolynomial.T (-1))) := add_right_cancel hh
    exact ((LaurentPolynomial.isUnit_T (R := K) 1).map φ).mul_left_cancel hc
  exact v5_laurent_derivation_agrees φ d D hpos hneg b

end StrictEUnit
#print axioms StrictEUnit.v5WidePointedLaurentBase_differential
