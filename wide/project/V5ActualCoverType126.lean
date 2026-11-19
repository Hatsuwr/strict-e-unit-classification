import V5GenericFixedEquiv123
import V5ComponentCoverFromOwnChart
import V5WideFieldCandidateMark
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

def v5ActualCoaction126 := v5WideOwnCoaction A

def v5ActualCover126 :=
  v5CanonicalComponentCover (B := LaurentPolynomial K) (k := K)
    (R := V5WideFieldCandidate A) (H := V5WideOwnConstants A)
    (v5ActualCoaction126 A) (v5GenericOwnIdentity123 A)

def v5ActualCoverMark126 :=
  v5CanonicalComponentCoverMark (B := LaurentPolynomial K) (k := K)
    (R := V5WideFieldCandidate A) (H := V5WideOwnConstants A)
    (v5ActualCoaction126 A) (v5GenericOwnIdentity123 A) (v5WideFieldCandidatePoint A)

end StrictEUnit
#print axioms StrictEUnit.v5ActualCoaction126
#print axioms StrictEUnit.v5ActualCover126
#print axioms StrictEUnit.v5ActualCoverMark126
