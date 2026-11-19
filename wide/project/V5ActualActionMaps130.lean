import V5ActualSplitMaps130
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 300000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

def v5ActualRestrictedAction130 :=
  v5ComponentOwnAction (v5WideOwnCoaction A) (v5ActualQuotient130 A)
#print axioms v5ActualRestrictedAction130

def v5ActualTrivialAction130 :=
  v5ComponentOwnTrivial (B := LaurentPolynomial K) (k := K)
    (R := V5WideFieldCandidate A) (N := V5WideOwnConstants A ⧸ v5GenericOwnIdentity123 A)
#print axioms v5ActualTrivialAction130

def v5ActualPrimeIndexFinite130 := by
  letI : Algebra.FiniteType K (V5WideOwnConstants A) := v5WideOwnConstants_finiteType A
  exact v5FinitePrimeIndex130 K (V5WideOwnConstants A)
#print axioms v5ActualPrimeIndexFinite130
end StrictEUnit
