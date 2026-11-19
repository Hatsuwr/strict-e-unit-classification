import V5ActualCoverType126
import V5SubalgebraSource128
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

def V5ActualCoverSource128 := V5SubalgebraSource128 (v5ActualCover126 A)
def v5ActualCoverSourceRing128 := v5SubalgebraSourceRing128 (v5ActualCover126 A)
def v5ActualCoverSourceAlgebra128 := v5SubalgebraSourceAlgebra128 (v5ActualCover126 A)
def v5ActualCoverSourceInclusion128 := v5SubalgebraSourceInclusion128 (v5ActualCover126 A)
end StrictEUnit
#print axioms StrictEUnit.V5ActualCoverSource128
#print axioms StrictEUnit.v5ActualCoverSourceRing128
#print axioms StrictEUnit.v5ActualCoverSourceAlgebra128
#print axioms StrictEUnit.v5ActualCoverSourceInclusion128
