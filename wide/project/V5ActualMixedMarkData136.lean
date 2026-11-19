import V5ActualFiberMark136
import V5PointedMarkMap136
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
def v5ActualMixedTensorMark136 := by
  letI : Algebra AlgebraicComplex (V5WideFieldCandidate A) :=
    ((V5WideFieldCandidate A).restrictScalars AlgebraicComplex).algebra
  letI := v5WideFieldCandidate_marked_baseTower A
  exact v5PointedMarkMap136 (k := AlgebraicComplex) (B := V5LaurentBase)
    (R := V5WideFieldCandidate A) (S := v5WideSolutionAlgebra f)
    (v5ActualFiberTensorMark136 f A hf hA)
@[simp] theorem v5ActualMixedTensorMark136_tmul
    (a : V5WideFieldCandidate A) (s : v5WideSolutionAlgebra f) :
    v5ActualMixedTensorMark136 f A hf hA (a ⊗ₜ[V5LaurentBase] s) =
      algebraMap AlgebraicComplex ℂ (v5WideFieldCandidatePoint A a) *
        v5WideSolutionEvaluation f s := by
  letI := v5WideFieldCandidate_marked_baseTower A
  exact (v5PointedMarkMap136_tmul (k := AlgebraicComplex)
    (R := V5WideFieldCandidate A) (v5ActualFiberTensorMark136 f A hf hA) a s).trans
    (v5ActualFiberTensorMark136_tmul f A hf hA (v5WideFieldCandidatePoint A a) s)
end StrictEUnit
#print axioms StrictEUnit.v5ActualMixedTensorMark136
#print axioms StrictEUnit.v5ActualMixedTensorMark136_tmul
