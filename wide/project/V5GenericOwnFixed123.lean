import V5WideOwnHopf
import V5WideOwnFiniteType
import V5HopfTranslation
import V5ComponentPointTransport
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 150000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 15000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
theorem v5UniqueIdentityHelper123 {K H : Type*} [Field K] [IsAlgClosed K]
    [CommRing H] [HopfAlgebra K H] [Algebra.FiniteType K H]
    (s : H →ₐ[K] H) (hs : s.toLinearMap = HopfAlgebra.antipode) :
    ∃! I : Ideal H, I ∈ minimalPrimes H ∧ I ≤ RingHom.ker (Bialgebra.counitAlgHom K H).toRingHom := by
  letI := Algebra.FiniteType.isNoetherianRing K H
  apply v5_unique_minimalPrime_of_point_transitive (Bialgebra.counitAlgHom K H)
    (minimalPrimes.finite_of_isNoetherianRing H)
  intro p
  exact ⟨v5HopfTranslation s hs p, v5HopfTranslation_at_counit s hs p⟩

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ}
  (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

def v5GenericOwnUniqueIdentity123 := by
  letI : Algebra.FiniteType K (V5WideOwnConstants A) := v5WideOwnConstants_finiteType A
  letI := v5WideOwnHopfAlgebra A
  exact v5UniqueIdentityHelper123 (K := K) (H := V5WideOwnConstants A)
    (v5WideOwnAntipode A) rfl

def v5GenericOwnIdentity123 := Classical.choose (v5GenericOwnUniqueIdentity123 A)

end StrictEUnit
#print axioms StrictEUnit.v5GenericOwnUniqueIdentity123
#print axioms StrictEUnit.v5GenericOwnIdentity123
