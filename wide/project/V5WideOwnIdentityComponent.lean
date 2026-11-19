import V5WideOwnHopf
import V5WideOwnFiniteType
import V5ComponentPointTransport
import V5HopfTranslation
import V5ComponentCoproduct
import V5PrimeQuotientTensorDomain
import V5WideActualMixedCoaction
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
section Generic
variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

theorem v5_unique_hopf_identityPrime [IsAlgClosed k] [Algebra.FiniteType k H]
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode) :
    ∃! I : Ideal H, I ∈ minimalPrimes H ∧ I ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom := by
  letI := Algebra.FiniteType.isNoetherianRing k H
  apply v5_unique_minimalPrime_of_point_transitive (Bialgebra.counitAlgHom k H)
    (minimalPrimes.finite_of_isNoetherianRing H)
  intro p
  exact ⟨v5HopfTranslation s hs p, v5HopfTranslation_at_counit s hs p⟩

theorem v5_hopfComponent_doubleCounit (x : H) :
    v5CounitPairing (Bialgebra.counitAlgHom k H) (Bialgebra.comulAlgHom k H x) =
      Bialgebra.counitAlgHom k H x := by
  apply v5CounitPairing_of_right_counit
  intro y
  change TensorProduct.rid k H ((Coalgebra.counit (R := k)).lTensor _ (Coalgebra.comul y)) = y
  rw [Coalgebra.lTensor_counit_comul]
  simp
end Generic

local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) V5LaurentBase)

theorem v5WideOwnUniqueIdentityPrime :
    ∃! I : Ideal (V5WideOwnConstants A), I ∈ minimalPrimes (V5WideOwnConstants A) ∧
      I ≤ RingHom.ker (v5WideMixedActionCounit A).toRingHom := by
  letI : Algebra.FiniteType AlgebraicComplex (V5WideOwnConstants A) := v5WideOwnConstants_finiteType A
  letI := v5WideOwnHopfAlgebra A
  exact v5_unique_hopf_identityPrime (v5WideOwnAntipode A) rfl

def v5WideOwnIdentityPrime : Ideal (V5WideOwnConstants A) :=
  Classical.choose (v5WideOwnUniqueIdentityPrime A)

theorem v5WideOwnIdentityPrime_spec :
    v5WideOwnIdentityPrime A ∈ minimalPrimes (V5WideOwnConstants A) ∧
      v5WideOwnIdentityPrime A ≤ RingHom.ker (v5WideMixedActionCounit A).toRingHom :=
  (Classical.choose_spec (v5WideOwnUniqueIdentityPrime A)).1

theorem v5WideOwnIdentityPrime_unique (I : Ideal (V5WideOwnConstants A))
    (hI : I ∈ minimalPrimes (V5WideOwnConstants A))
    (hIε : I ≤ RingHom.ker (v5WideMixedActionCounit A).toRingHom) :
    I = v5WideOwnIdentityPrime A :=
  (Classical.choose_spec (v5WideOwnUniqueIdentityPrime A)).2 I ⟨hI, hIε⟩

theorem v5WideOwnIdentityPrime_isPrime : (v5WideOwnIdentityPrime A).IsPrime :=
  Ideal.minimalPrimes_isPrime (v5WideOwnIdentityPrime_spec A).1

abbrev V5WideOwnIdentityComponent := V5WideOwnConstants A ⧸ v5WideOwnIdentityPrime A

def v5WideOwnIdentityCoproduct : V5WideOwnIdentityComponent A →ₐ[AlgebraicComplex]
    V5WideOwnIdentityComponent A ⊗[AlgebraicComplex] V5WideOwnIdentityComponent A := by
  let I := v5WideOwnIdentityPrime A
  letI : Algebra.FiniteType AlgebraicComplex (V5WideOwnConstants A) := v5WideOwnConstants_finiteType A
  letI : I.IsPrime := v5WideOwnIdentityPrime_isPrime A
  letI := v5_primeQuotient_tensorSquare_isDomain (k := AlgebraicComplex) I
  letI := v5WideOwnHopfAlgebra A
  exact v5ComponentCoproduct I (v5WideMixedActionCounit A) (v5WideOwnIdentityPrime_spec A).2
    (v5WideOwnIdentityPrime_unique A) (v5WideOwnComultiplication A)
    (v5_hopfComponent_doubleCounit (k := AlgebraicComplex))

end StrictEUnit
#print axioms StrictEUnit.v5WideOwnUniqueIdentityPrime
#print axioms StrictEUnit.v5WideOwnIdentityPrime
#print axioms StrictEUnit.v5WideOwnIdentityPrime_isPrime
#print axioms StrictEUnit.v5WideOwnIdentityCoproduct

#print axioms StrictEUnit.v5_unique_hopf_identityPrime
