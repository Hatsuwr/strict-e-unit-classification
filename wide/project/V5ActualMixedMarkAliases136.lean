import V5ActualMixedMarkData136
import V5MarkedTensorUniqueness136
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 30000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
  (A : Matrix (Fin r) (Fin r) V5LaurentBase)
  (hf : ∀ i, V5IsBroadEFunction (f i).val)
  (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
    ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
def v5ActualMixedMarkBaseCompatibility136 := by
  letI : Algebra AlgebraicComplex (V5WideFieldCandidate A) :=
    ((V5WideFieldCandidate A).restrictScalars AlgebraicComplex).algebra
  exact v5MarkedTensorBaseCompatibility136
    (v5WideFieldCandidatePoint A) (v5WideSolutionEvaluation f)
    (v5ActualMixedTensorMark136 f A hf hA) (v5ActualMixedTensorMark136_tmul f A hf hA)
def v5ActualMixedMarkEq135136 := by
  letI : Algebra AlgebraicComplex (V5WideFieldCandidate A) :=
    ((V5WideFieldCandidate A).restrictScalars AlgebraicComplex).algebra
  exact v5MarkedTensorEq135136
    (v5WideFieldCandidatePoint A) (v5WideSolutionEvaluation f)
    (v5ActualMixedTensorMark136 f A hf hA) (v5ActualMixedTensorMark136_tmul f A hf hA)
end StrictEUnit
#print axioms StrictEUnit.v5ActualMixedMarkBaseCompatibility136
#print axioms StrictEUnit.v5ActualMixedMarkEq135136
