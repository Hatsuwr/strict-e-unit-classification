import V5WideActualMixedComparison
import V5WideFieldCandidateMark
import V5MixedPointedFiber
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 120000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
    (A : Matrix (Fin r) (Fin r) V5LaurentBase)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
def v5WideActualPointedFiber := by
  letI : Algebra V5LaurentBase AlgebraicComplex :=
    (v5LaurentPointOne (k := AlgebraicComplex)).toRingHom.toAlgebra
  letI := v5WideFieldCandidate_marked_baseTower A
  exact v5MixedPointedFiber (v5WideActualMixedComparison f A hA)
end StrictEUnit
#print axioms StrictEUnit.v5WideActualPointedFiber

