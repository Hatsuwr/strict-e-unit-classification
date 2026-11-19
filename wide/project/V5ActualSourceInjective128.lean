import V5ActualSource128
import V5WideOwnTensorEmbedding
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

def v5ActualCoverSourceInclusion128_injective := by
  letI : AddCommGroup (V5WideFieldCandidate A) :=
    (V5WideFieldCandidate A).toCommRing.toAddCommGroup
  letI := v5WideOwnCandidate_faithfullyFlat A
  exact v5SubalgebraSourceInclusion128_injective (v5ActualCover126 A)
end StrictEUnit
#print axioms StrictEUnit.v5ActualCoverSourceInclusion128_injective
