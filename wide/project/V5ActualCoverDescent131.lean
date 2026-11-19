import V5ExplicitCoverDescent131
import V5ActualActionMaps130
import V5WideOwnPVAction
import V5ActualTarget129
import V5MiddleDictionary129
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))
def v5ActualCoverDescent131 := by
  letI := v5WideOwnCandidate_faithfullyFlat A
  letI := v5ActualPrimeIndexFinite130 A
  exact v5ExplicitCoverDescent131
    (k := K) (B := LaurentPolynomial K)
    (R := V5WideFieldCandidate A) (H := V5WideOwnConstants A)
    (J := ↥(minimalPrimes (V5WideOwnConstants A)))
    (v5WideOwnMultiplicationEquiv A) (v5GenericOwnIdentity123 A)
    (v5WideOwnCoaction A) (v5WideOwnComultiplication A)
    (by intro r s; exact v5_ownChart_tmul_smul (v5WideOwnMultiplicationEquiv A) r s)
    (v5WideOwnCoaction_coassoc A) (v5GenericOwnFixed123 A)
end StrictEUnit
#print axioms StrictEUnit.v5ActualCoverDescent131
