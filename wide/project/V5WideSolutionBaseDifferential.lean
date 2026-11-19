import V5LaurentDerivationAgreement
import V5LaurentBaseDerivation
import V5WideSolutionFlat

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

@[simp] private theorem v5WideSolutionBase_T_one :
    v5WideSolutionBase f (LaurentPolynomial.T 1) = v5WideSolutionParameter f true := by
  change LaurentPolynomial.eval₂ _ (v5WideSolutionCoordinate f) _ = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

@[simp] private theorem v5WideSolutionBase_T_neg_one :
    v5WideSolutionBase f (LaurentPolynomial.T (-1)) = v5WideSolutionParameter f false := by
  change LaurentPolynomial.eval₂ _ (v5WideSolutionCoordinate f) _ = _
  rw [LaurentPolynomial.eval₂_T, zpow_neg_one]
  rfl

/-- Literal punctured differentiation restricts to the ordinary Laurent
derivation on the actual embedded base. -/
theorem v5WideSolution_base_compatible (b : V5LaurentBase) :
    v5WideSolutionDerivation f A hA (v5WideSolutionBase f b) =
      v5WideSolutionBase f (v5LaurentBaseDerivation b) := by
  apply v5_laurent_derivation_agrees
  · rw [v5WideSolutionBase_T_one, v5WideSolutionDerivation_coordinate, v5LaurentBaseDerivation_T]
    simp only [Int.cast_one, sub_self, LaurentPolynomial.T_zero, mul_one, map_one]
  · have hT : (LaurentPolynomial.T (-1 - 1) : V5LaurentBase) =
        LaurentPolynomial.T (-1) * LaurentPolynomial.T (-1) := by
      rw [sub_eq_add_neg, LaurentPolynomial.T_add]
    rw [v5WideSolutionBase_T_neg_one, v5WideSolutionDerivation_inverse_coordinate,
      v5LaurentBaseDerivation_T, hT]
    simp only [Int.cast_neg, Int.cast_one, map_neg, map_one, neg_one_mul, map_mul,
      v5WideSolutionBase_T_neg_one]

end StrictEUnit
#print axioms StrictEUnit.v5WideSolution_base_compatible
