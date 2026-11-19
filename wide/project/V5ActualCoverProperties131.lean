import V5ActualCoverDescent131
noncomputable section
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
/-- Preserve the elaborated module dictionaries of the checked actual descent. -/
def v5ActualCoverFinite131 := (v5ActualCoverDescent131 A).1
def v5ActualCoverFlat131 := (v5ActualCoverDescent131 A).2.1
def v5ActualCoverUnramified131 := (v5ActualCoverDescent131 A).2.2
def v5ActualCoverFormallyUnramified131 :=
  (v5ActualCoverDescent131 A).2.2.formallyUnramified
end StrictEUnit
#print axioms StrictEUnit.v5ActualCoverFinite131
#print axioms StrictEUnit.v5ActualCoverFlat131
#print axioms StrictEUnit.v5ActualCoverUnramified131
#print axioms StrictEUnit.v5ActualCoverFormallyUnramified131
