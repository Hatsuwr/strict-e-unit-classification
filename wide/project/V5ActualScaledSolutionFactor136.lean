import V5ReverseSolutionKummerDifferential136
import V5SubalgebraScaledData136
noncomputable section
open scoped TensorProduct
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
attribute [local instance 6000] solutionRing136 solutionAddGroup136 solutionAddMonoid136
  solutionCoefficientAlgebra136 solutionLaurentAlgebra136 solutionLaurentModule136
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra) (A : Matrix ι ι V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
/-- The solution factor in the common (q*T1)-scaled data is exactly q times
its checked Euler derivation. -/
theorem v5ActualScaledSolutionFactor136 (q : ℕ) (s : v5WideSolutionAlgebra f) :
    v5CoordinateEuler136 ((q : V5LaurentBase) * LaurentPolynomial.T 1)
      (v5WideSolutionDerivation f A hA) s = q • v5ActualSolutionEuler f A hA s := by
  have ht : algebraMap V5LaurentBase (v5WideSolutionAlgebra f) (LaurentPolynomial.T 1) =
      v5WideSolutionParameter f true := by
    change LaurentPolynomial.eval₂ _ (v5WideSolutionCoordinate f) _ = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]
    rfl
  exact v5CoordinateEuler_scaled_value136 (k := AlgebraicComplex) (B := V5LaurentBase)
    (U := v5WideSolutionAlgebra f) (LaurentPolynomial.T 1)
    (v5WideSolutionDerivation f A hA) q (v5WideSolutionParameter f true) ht
    (v5ActualSolutionEuler f A hA) (fun _ => rfl) s
/-- Product-form alias matching the coefficient tensor constructor's rule. -/
theorem v5ActualScaledSolutionFactor_mul136 (q : ℕ) (s : v5WideSolutionAlgebra f) :
    algebraMap V5LaurentBase (v5WideSolutionAlgebra f)
      ((q : V5LaurentBase) * LaurentPolynomial.T 1) * v5WideSolutionDerivation f A hA s =
        q • v5ActualSolutionEuler f A hA s :=
  v5ActualScaledSolutionFactor136 f A hA q s
end StrictEUnit
#print axioms StrictEUnit.v5ActualScaledSolutionFactor136
#print axioms StrictEUnit.v5ActualScaledSolutionFactor_mul136
