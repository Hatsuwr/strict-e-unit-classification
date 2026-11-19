import V5MixedPointedFiber
import Mathlib.RingTheory.FiniteStability

noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 70000

variable {k B R S C : Type*} [CommRing k] [CommRing B] [CommRing R]
  [CommRing S] [CommRing C]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k C]
  [Algebra R k] [IsScalarTower k R k] [Algebra B k] [IsScalarTower B R k]

/-- A marked comparison transfers finite type from the actual B-algebra S
to its horizontal factor C via the genuine specialized fiber equivalence. -/
theorem v5_pointedConstants_finiteType [Algebra.FiniteType B S]
    (e : R ⊗[k] C ≃ₐ[R] R ⊗[B] S) : Algebra.FiniteType k C :=
  Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType k (k ⊗[B] S))
    (v5MixedPointedFiber e).symm

end StrictEUnit
#print axioms StrictEUnit.v5_pointedConstants_finiteType
