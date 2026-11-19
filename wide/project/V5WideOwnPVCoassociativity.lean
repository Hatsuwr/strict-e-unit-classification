import V5WideOwnPVAction
import PVConstantBialgebra

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

theorem v5WideOwnComultiplication_coassoc (h : V5WideOwnConstants A) :
    Algebra.TensorProduct.assoc k (V5WideOwnConstants A) (V5WideOwnConstants A)
      (V5WideOwnConstants A)
      (Algebra.TensorProduct.map (v5WideOwnComultiplication A)
        (AlgHom.id k (V5WideOwnConstants A)) (v5WideOwnComultiplication A h)) =
    Algebra.TensorProduct.map (AlgHom.id k (V5WideOwnConstants A))
      (v5WideOwnComultiplication A) (v5WideOwnComultiplication A h) :=
  pvConstantComultiplication_coassoc v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)
    (v5WideOwnMultiplication_bijective A) (v5WideOwnDerivation_constants A) h

/-- A proved bialgebra structure, with no assumed coalgebra/action laws. -/
def v5WideOwnBialgebra : Bialgebra k (V5WideOwnConstants A) :=
  pvConstantBialgebra v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)
    (v5WideOwnMultiplication_bijective A) (v5WideOwnDerivation_constants A)

end StrictEUnit
#print axioms StrictEUnit.v5WideOwnCoaction_coassoc
#print axioms StrictEUnit.v5WideOwnComultiplication_coassoc
#print axioms StrictEUnit.v5WideOwnBialgebra
