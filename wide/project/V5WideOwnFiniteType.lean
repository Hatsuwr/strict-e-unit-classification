import V5PointedConstantsFiniteType
import V5WideOwnPVAction
import V5WideFieldCandidateMark

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule
attribute [-instance] HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit
variable {k : Type*} [Field k] [CharZero k] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial k))

local instance : Algebra (LaurentPolynomial k) k :=
  (v5LaurentPointOne (k := k)).toRingHom.toAlgebra

/-- The actual own-PV constants algebra is of finite type over k.
Finite generation of the matrix candidate and the normalized algebraic
mark supply all hypotheses; finite type of H is not assumed. -/
theorem v5WideOwnConstants_finiteType : Algebra.FiniteType k (V5WideOwnConstants A) := by
  letI := v5WideFieldCandidate_marked_baseTower A
  exact v5_pointedConstants_finiteType (v5WideOwnMultiplicationEquiv A)

end StrictEUnit
#print axioms StrictEUnit.v5WideOwnConstants_finiteType
