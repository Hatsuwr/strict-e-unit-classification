import V5ActualCoverMark125
import V5CoverDifferential126

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

theorem v5ActualCover_differential126 (x : v5ActualCover125 A) :
    v5WideOwnDerivation A x.val ∈ v5ActualCover125 A :=
  v5ComponentCover_differential126 (v5WideOwnCoaction A)
    (Ideal.Quotient.mkₐ K (v5GenericOwnIdentity123 A))
    (v5WideOwnDerivation A) (v5WideOwnCoaction_differential A) x

def v5ActualCoverDerivation126 :=
  v5ComponentCoverDerivation126 (v5WideOwnCoaction A)
    (Ideal.Quotient.mkₐ K (v5GenericOwnIdentity123 A))
    (v5WideOwnDerivation A) (v5WideOwnCoaction_differential A)

theorem v5ActualCoverDerivation126_base (b : LaurentPolynomial K) :
    v5ActualCoverDerivation126 A (algebraMap (LaurentPolynomial K) (v5ActualCover125 A) b) =
      algebraMap (LaurentPolynomial K) (v5ActualCover125 A) (v5LaurentBaseDerivation b) :=
  Subtype.ext (v5WideOwnDerivation_base A b)

end StrictEUnit
#print axioms StrictEUnit.v5ActualCover_differential126
#print axioms StrictEUnit.v5ActualCoverDerivation126
#print axioms StrictEUnit.v5ActualCoverDerivation126_base
