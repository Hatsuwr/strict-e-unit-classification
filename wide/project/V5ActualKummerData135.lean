import V5ActualFiniteKummer128
import V5ActualCoverProperties131
import V5AlgebraicMarkedKummer135
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Algebra K ℂ] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))
def v5ActualAlgebraicMarkedKummer135 :=
  v5AlgebraicMarkedKummer135 (algebraMap K ℂ) (algebraMap K ℂ).injective
    (fun t : v5ActualCover125 A => v5WideFieldCandidatePoint A (t : V5WideFieldCandidate A))
    (v5ActualFiniteKummer128 A (v5ActualCoverFinite131 A))
end StrictEUnit
#print axioms StrictEUnit.v5ActualAlgebraicMarkedKummer135
