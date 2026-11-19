import V5QuotientUnitCharacter
import V5WideOwnIdentityComponent
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k C H : Type*} [Field k] [IsAlgClosed k]
  [CommRing C] [IsDomain C] [Algebra k C]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
/-- The quotient character uses the designated minimal identity ideal directly.
The quotient counit and coproduct are constructed internally. -/
def v5HopfQuotientCharacter135
    (δ : C →ₐ[k] C ⊗[k] H)
    (I : Ideal H) (hmin : I ∈ minimalPrimes H)
    (hI : I ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom)
    (hu : ∀ P ∈ minimalPrimes H,
      P ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom → P = I)
    (hc : ∀ c, v5_horizontalCounit (Bialgebra.counitAlgHom k H) (δ c) = c)
    (ha : ∀ c, Algebra.TensorProduct.assoc k C H H
      (Algebra.TensorProduct.map δ (AlgHom.id k H) (δ c)) =
      Algebra.TensorProduct.map (AlgHom.id k C) (Bialgebra.comulAlgHom k H) (δ c)) := by
  letI : I.IsPrime := Ideal.minimalPrimes_isPrime hmin
  letI := v5_primeQuotient_tensorSquare_isDomain (k := k) I
  let Δ := v5ComponentCoproduct I (Bialgebra.counitAlgHom k H) hI hu
    (Bialgebra.comulAlgHom k H) (v5_hopfComponent_doubleCounit (k := k))
  exact v5QuotientUnitCharacter_of_laws δ I (Bialgebra.counitAlgHom k H) hI
    (Bialgebra.comulAlgHom k H) Δ (fun _ => rfl) hc ha
end StrictEUnit
#print axioms StrictEUnit.v5HopfQuotientCharacter135
