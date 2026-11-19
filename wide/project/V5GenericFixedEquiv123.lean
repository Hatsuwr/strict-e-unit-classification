import V5GenericOwnFixed123
import V5HopfComponentInvariants
import V5WideOwnReduced
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

def v5GenericOwnFixed123 := by
  letI := v5WideOwnHopfAlgebra A
  letI : Algebra.FiniteType K (V5WideOwnConstants A) := v5WideOwnConstants_finiteType A
  letI := v5WideOwnConstants_isReduced A
  have spec := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).1
  have uniq := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).2
  exact v5HopfCanonicalComponentFixedEquiv (k := K) (H := V5WideOwnConstants A)
    (v5WideOwnAntipode A).toAlgHom rfl (v5GenericOwnIdentity123 A)
    (fun P hP hPε => uniq P ⟨hP, hPε⟩)
    (Ideal.minimalPrimes_isPrime spec.1) spec.2
end StrictEUnit
#print axioms StrictEUnit.v5GenericOwnFixed123
