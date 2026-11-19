import V5ActualSourceInjective128
import V5TargetDictionary129
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 150000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

def v5ActualTargetAlgebra129 := by
  letI : AddCommGroup (V5WideFieldCandidate A) :=
    (V5WideFieldCandidate A).toCommRing.toAddCommGroup
  letI : AddCommMonoid (V5WideFieldCandidate A) :=
    (V5WideFieldCandidate A).toCommRing.toAddCommMonoid
  exact v5TargetAlgebra129 (R := V5WideFieldCandidate A) (V5WideOwnConstants A)
end StrictEUnit
#print axioms StrictEUnit.v5ActualTargetAlgebra129
