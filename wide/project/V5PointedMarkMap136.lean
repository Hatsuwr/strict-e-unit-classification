import V5PointedMarkBridge136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S C : Type*}
  [CommRing k] [CommRing B] [CommRing R] [CommRing S] [CommRing C]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k C]
  [Algebra R k] [IsScalarTower k R k] [Algebra B k] [IsScalarTower B R k]
def v5PointedMarkMap136 (q : k ⊗[B] S →ₐ[k] C) : R ⊗[B] S →ₐ[k] C :=
  q.comp (v5MarkedTensorSpecialization136 (k := k) (B := B) (R := R) (S := S))
theorem v5PointedMarkMap136_tmul (q : k ⊗[B] S →ₐ[k] C) (r : R) (s : S) :
    v5PointedMarkMap136 (R := R) q (r ⊗ₜ[B] s) = q (algebraMap R k r ⊗ₜ[B] s) := by
  change q (v5MarkedTensorSpecialization136 (r ⊗ₜ[B] s)) = _
  rw [v5MarkedTensorSpecialization136_tmul]
end StrictEUnit
#print axioms StrictEUnit.v5PointedMarkMap136
#print axioms StrictEUnit.v5PointedMarkMap136_tmul
