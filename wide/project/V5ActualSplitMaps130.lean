import V5ActualCoverType126
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

def v5QuotientMap130 {k H : Type*} [CommRing k] [CommRing H] [Algebra k H]
    (I : Ideal H) := Ideal.Quotient.mkₐ k I

def v5QuotientDelta130 {k H : Type*} [CommRing k] [CommRing H] [Algebra k H]
    (I : Ideal H) (Δ : H →ₐ[k] H ⊗[k] H) :=
  (Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp Δ

def v5FinitePrimeIndex130 (k H : Type*) [Field k] [CommRing H] [Algebra k H]
    [Algebra.FiniteType k H] : Finite ↥(minimalPrimes H) := by
  letI := Algebra.FiniteType.isNoetherianRing k H
  exact (minimalPrimes.finite_of_isNoetherianRing H).to_subtype

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

def v5ActualQuotient130 :=
  v5QuotientMap130 (k := K) (H := V5WideOwnConstants A) (v5GenericOwnIdentity123 A)
#print axioms v5ActualQuotient130

def v5ActualQuotientDelta130 :=
  v5QuotientDelta130 (v5GenericOwnIdentity123 A) (v5WideOwnComultiplication A)
#print axioms v5ActualQuotientDelta130

end StrictEUnit
