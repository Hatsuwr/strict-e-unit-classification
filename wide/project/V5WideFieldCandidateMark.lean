import V5WidePointedFieldCandidate
import V5LaurentPointOne

noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 70000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
attribute [-instance] HahnSeries.instSMul
namespace StrictEUnit
variable {k : Type*} [Field k] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial k))

local instance : Algebra (LaurentPolynomial k) k :=
  (v5LaurentPointOne (k := k)).toRingHom.toAlgebra

/-- Turn the transported actual k-point into an algebra structure on k. -/
instance v5WideFieldCandidate_marked : Algebra (V5WideFieldCandidate A) k :=
  (v5WideFieldCandidatePoint A).toRingHom.toAlgebra

instance v5WideFieldCandidate_marked_constantTower :
    IsScalarTower k (V5WideFieldCandidate A) k :=
  IsScalarTower.of_algebraMap_eq' (v5WideFieldCandidatePoint A).comp_algebraMap.symm

/-- The mark on the candidate really lies over the designated point at z=1. -/
theorem v5WideFieldCandidate_marked_baseTower :
    IsScalarTower (LaurentPolynomial k) (V5WideFieldCandidate A) k := by
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (v5WideFieldCandidatePoint_base A b).symm

end StrictEUnit
#print axioms StrictEUnit.v5WideFieldCandidate_marked_baseTower
