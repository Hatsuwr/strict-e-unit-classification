import V5ActualMixedMarkData136
import V5PointedTensorMark136
import V5ConstantsMarkInclusion136
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 30000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
local instance : Algebra V5LaurentBase AlgebraicComplex :=
  (v5LaurentPointOne (k := AlgebraicComplex)).toRingHom.toAlgebra
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
  (A : Matrix (Fin r) (Fin r) V5LaurentBase)
  (hf : ∀ i, V5IsBroadEFunction (f i).val)
  (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
    ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
/-- Tensor evaluation and the original exact-fiber evaluation agree on mixed constants. -/
def v5ActualMixedTensorMark136_constant := by
  letI : Algebra AlgebraicComplex (V5WideFieldCandidate A) :=
    ((V5WideFieldCandidate A).restrictScalars AlgebraicComplex).algebra
  letI := v5WideFieldCandidate_marked_baseTower A
  exact v5PointedTensorMark136 (k := AlgebraicComplex) (B := V5LaurentBase)
    (R := V5WideFieldCandidate A) (S := v5WideSolutionAlgebra f) (C := ℂ)
    (D := V5WideActualMixedConstants104 f A hA)
    (v5WideActualMixedComparison f A hA)
    (v5WideTensorFiberAlgEquiv f) (v5WideSolutionFiberEvaluation f A hf hA)
    (v5MixedConstantsMarkInclusion136 (k := AlgebraicComplex) (B := V5LaurentBase)
      (R := V5WideFieldCandidate A) (S := v5WideSolutionAlgebra f)
      (v5WideActualMixedDerivation104 f A hA))
    (v5MixedConstantMultiplication_constant136 (v5WideActualMixedDerivation104 f A hA))
def v5ActualMixedTensorMark136_unit_value (i j : Fin r)
    (hij : (f i).val 1 * (f j).val 1 = 1) :=
  ((v5ActualMixedTensorMark136_constant f A hf hA)
    (v5WideMixedConstantUnit f A hf hA i j hij).val).trans
      (v5WideMixedConstantUnit_value f A hf hA i j hij)
def v5ActualMixedTensorMark136_unit_inverse_value (i j : Fin r)
    (hij : (f i).val 1 * (f j).val 1 = 1) :=
  ((v5ActualMixedTensorMark136_constant f A hf hA)
    (v5WideMixedConstantUnit f A hf hA i j hij).inv).trans
      (v5WideMixedConstantUnit_inverse_value f A hf hA i j hij)
end StrictEUnit
#print axioms StrictEUnit.v5ActualMixedTensorMark136_constant
#print axioms StrictEUnit.v5ActualMixedTensorMark136_unit_value
#print axioms StrictEUnit.v5ActualMixedTensorMark136_unit_inverse_value
