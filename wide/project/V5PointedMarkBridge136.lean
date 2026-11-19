import V5MixedPointedFiber
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
def v5MarkedTensorSpecialization136 : R ⊗[B] S →ₐ[k] k ⊗[B] S :=
  (v5PointedCancelBaseChange (B := B) (R := R) (K := k) (S := S)).toAlgHom.comp
    ((Algebra.TensorProduct.includeRight : R ⊗[B] S →ₐ[R] k ⊗[R] (R ⊗[B] S)).restrictScalars k)
@[simp] theorem v5MarkedTensorSpecialization136_tmul (r : R) (s : S) :
    v5MarkedTensorSpecialization136 (r ⊗ₜ[B] s) = algebraMap R k r ⊗ₜ[B] s := by
  change (r • (1 : k)) ⊗ₜ[B] s = _
  simp only [Algebra.smul_def, mul_one]
theorem v5MarkedTensorSpecialization136_pointed
    {D : Type*} [CommRing D] [Algebra k D]
    (e : R ⊗[k] D ≃ₐ[R] R ⊗[B] S) (d : D) :
    v5MarkedTensorSpecialization136 (e ((1 : R) ⊗ₜ[k] d)) =
      v5MixedPointedFiber e d := by
  rw [v5MixedPointedFiber_apply]
  rfl
theorem v5FiberTensorMark_tmul136 (p : k ⊗[B] S →ₐ[k] C) (a : k) (s : S) :
    p (a ⊗ₜ[B] s) = algebraMap k C a * p ((1 : k) ⊗ₜ[B] s) := by
  rw [show a ⊗ₜ[B] s = (a ⊗ₜ[B] (1 : S)) * ((1 : k) ⊗ₜ[B] s) by simp,
    map_mul]
  congr 1
  exact p.commutes a
end StrictEUnit
#print axioms StrictEUnit.v5MarkedTensorSpecialization136
#print axioms StrictEUnit.v5MarkedTensorSpecialization136_tmul
#print axioms StrictEUnit.v5MarkedTensorSpecialization136_pointed

#print axioms StrictEUnit.v5FiberTensorMark_tmul136
