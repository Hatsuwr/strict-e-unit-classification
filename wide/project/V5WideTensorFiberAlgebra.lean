import V5LaurentPointOneAlgebra
import V5WideSolutionRelativeBase

open scoped TensorProduct
noncomputable section
namespace StrictEUnit
set_option maxHeartbeats 400000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule

/-- The base tensor fiber is exactly the already verified quotient by z−1. -/
def v5WideTensorFiberAlgEquiv {ι : Type} (f : ι → entireFunctionAlgebra) := by
  letI : Algebra V5LaurentBase AlgebraicComplex :=
    (v5LaurentPointOne (k := AlgebraicComplex)).toRingHom.toAlgebra
  have hz : algebraMap V5LaurentBase (v5WideSolutionAlgebra f) (LaurentPolynomial.T 1) =
      v5WideSolutionParameter f true := by
    change LaurentPolynomial.eval₂ _ (v5WideSolutionCoordinate f) (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]
    rfl
  have hi : v5WideSolutionIdeal f =
      Ideal.span {algebraMap V5LaurentBase (v5WideSolutionAlgebra f) (LaurentPolynomial.T 1) - 1} := by
    rw [hz]
    rfl
  exact v5LaurentQuotientAtIdealAlg (k := AlgebraicComplex) (S := v5WideSolutionAlgebra f) (v5WideSolutionIdeal f) hi

@[simp] theorem v5WideTensorFiberAlgEquiv_mk {ι : Type}
    (f : ι → entireFunctionAlgebra) (s : v5WideSolutionAlgebra f) :
    letI : Algebra V5LaurentBase AlgebraicComplex :=
      (v5LaurentPointOne (k := AlgebraicComplex)).toRingHom.toAlgebra
    v5WideTensorFiberAlgEquiv f (Ideal.Quotient.mk (v5WideSolutionIdeal f) s) =
      (1 : AlgebraicComplex) ⊗ₜ[V5LaurentBase] s := by
  simp only [v5WideTensorFiberAlgEquiv, v5LaurentQuotientAtIdealAlg_mk]
end StrictEUnit
#print axioms StrictEUnit.v5WideTensorFiberAlgEquiv

#print axioms StrictEUnit.v5WideTensorFiberAlgEquiv_mk
