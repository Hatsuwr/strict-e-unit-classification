import V5WideOwnPVComparison
import CandidateActionCoassociativity

/-! The actual centered candidate's own constants bialgebra and coassociative
action. This is separate from a mixed horizontal-algebra action and does not
assert a fiber unit lifts. -/
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

abbrev V5WideOwnConstants :=
  pvConstantAlgebra v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)

def v5WideOwnComultiplication :=
  pvConstantComultiplication v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)
    (v5WideOwnMultiplication_bijective A) (v5WideOwnDerivation_constants A)

/-- Coassociativity of the actual multiplication-chart coaction. -/
theorem v5WideOwnCoaction_coassoc (x : V5WideFieldCandidate A) :
    Algebra.TensorProduct.assoc k (V5WideFieldCandidate A) (V5WideOwnConstants A)
      (V5WideOwnConstants A)
      (Algebra.TensorProduct.map ((v5WideOwnCoaction A).restrictScalars k)
        (AlgHom.id k (V5WideOwnConstants A)) (v5WideOwnCoaction A x)) =
    Algebra.TensorProduct.map (AlgHom.id (V5WideFieldCandidate A) (V5WideFieldCandidate A))
      (v5WideOwnComultiplication A) (v5WideOwnCoaction A x) :=
  inverseMultiplicationCoaction_coassoc v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)
    (v5WideOwnMultiplication_bijective A) (v5WideOwnDerivation_constants A) x

end StrictEUnit
#print axioms StrictEUnit.v5WideOwnCoaction_coassoc
