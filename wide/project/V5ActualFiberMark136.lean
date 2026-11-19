import V5PointedMarkBridge136
import V5MixedMarkComparison136
import V5WideMixedConstantUnit
import V5WideActualMixedScalars
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
def v5ActualFiberTensorMark136 :=
  v5TransportEvaluation (v5WideTensorFiberAlgEquiv f).symm
    (v5WideSolutionFiberEvaluation f A hf hA)
@[simp] theorem v5ActualFiberTensorMark136_tmul
    (a : AlgebraicComplex) (s : v5WideSolutionAlgebra f) :
    v5ActualFiberTensorMark136 f A hf hA (a ⊗ₜ[V5LaurentBase] s) =
      algebraMap AlgebraicComplex ℂ a * v5WideSolutionEvaluation f s := by
  have h1 : v5ActualFiberTensorMark136 f A hf hA
      ((1 : AlgebraicComplex) ⊗ₜ[V5LaurentBase] s) = v5WideSolutionEvaluation f s := by
    change v5WideSolutionFiberEvaluation f A hf hA
      ((v5WideTensorFiberAlgEquiv f).symm ((1 : AlgebraicComplex) ⊗ₜ[V5LaurentBase] s)) = _
    rw [← v5WideTensorFiberAlgEquiv_mk, AlgEquiv.symm_apply_apply]
    rfl
  rw [v5FiberTensorMark_tmul136, h1]
end StrictEUnit
#print axioms StrictEUnit.v5ActualFiberTensorMark136
#print axioms StrictEUnit.v5ActualFiberTensorMark136_tmul
