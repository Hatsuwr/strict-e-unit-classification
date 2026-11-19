import V5PointedMarkBridge136
import V5UnitTransport
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S D Q C : Type*}
  [CommRing k] [CommRing B] [CommRing R] [CommRing S] [CommRing D] [CommRing Q] [CommRing C]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [Algebra k D] [Algebra k Q] [Algebra k C]
  [Algebra R k] [IsScalarTower k R k] [Algebra B k] [IsScalarTower B R k]
theorem v5PointedTensorMark136
    (e : R ⊗[k] D ≃ₐ[R] R ⊗[B] S) (g : Q ≃ₐ[k] k ⊗[B] S)
    (ev : Q →ₐ[k] C) (η : D →ₐ[k] R ⊗[B] S)
    (hη : ∀ d, e ((1 : R) ⊗ₜ[k] d) = η d) :
    ∀ d, ((v5TransportEvaluation g.symm ev).comp
      (v5MarkedTensorSpecialization136 (k := k) (B := B) (R := R) (S := S))) (η d) =
      v5TransportEvaluation ((v5MixedPointedFiber e).trans g.symm) ev d := by
  intro d
  rw [← hη]
  change ev (g.symm (v5MarkedTensorSpecialization136 (e ((1 : R) ⊗ₜ[k] d)))) =
    ev (g.symm (v5MixedPointedFiber e d))
  rw [v5MarkedTensorSpecialization136_pointed]
end StrictEUnit
#print axioms StrictEUnit.v5PointedTensorMark136
