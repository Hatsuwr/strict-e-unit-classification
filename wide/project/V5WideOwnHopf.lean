import PVConstantHopfAlgebra
import V5WideOwnPVCoassociativity

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

/-- The actual own-PV antipode is the tensor flip restricted to constants. -/
def v5WideOwnAntipode :=
  pvConstantFlip v5LaurentBaseDerivation (v5WideOwnDerivation A)
    (v5WideOwnDerivation_base A)

/-- All Hopf laws for the actual centered candidate, with no action,
antipode, exact-constants or flatness hypotheses left to supply. -/
def v5WideOwnHopfAlgebra : HopfAlgebra k (V5WideOwnConstants A) :=
  pvConstantHopfAlgebra v5LaurentBaseDerivation
    (v5WideOwnDerivation A) (v5WideOwnDerivation_base A)
    (v5WideOwnMultiplication_bijective A) (v5WideOwnDerivation_constants A)

theorem v5WideOwnHopfAlgebra_bialgebra :
    (v5WideOwnHopfAlgebra A).toBialgebra = v5WideOwnBialgebra A := rfl

theorem v5WideOwnHopfAlgebra_antipode :
    (v5WideOwnHopfAlgebra A).antipode = (v5WideOwnAntipode A).toLinearMap := rfl

end StrictEUnit
#print axioms StrictEUnit.v5WideOwnAntipode
#print axioms StrictEUnit.v5WideOwnHopfAlgebra
#print axioms StrictEUnit.v5WideOwnHopfAlgebra_bialgebra
#print axioms StrictEUnit.v5WideOwnHopfAlgebra_antipode
