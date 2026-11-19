import TensorDerivation
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R N : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing N]
  [Algebra k B] [Algebra k R] [Algebra k N] [Algebra B R] [IsScalarTower k B R]
theorem v5_tensorDerivation_scale136 (d : Derivation k R R) (c : R) (x : R ⊗[k] N) :
    tensorDerivation (c • d) x = (c ⊗ₜ[k] (1 : N)) * tensorDerivation d x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul r n =>
    change (c * d r) ⊗ₜ[k] n = (c ⊗ₜ[k] (1 : N)) * (d r ⊗ₜ[k] n)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem v5_scaled_coaction_differential136
    (ρ : R →ₐ[B] R ⊗[k] N) (d : Derivation k R R)
    (hd : ∀ r, tensorDerivation d (ρ r) = ρ (d r))
    (c : R) (hc : ρ c = c ⊗ₜ[k] (1 : N)) (r : R) :
    tensorDerivation (c • d) (ρ r) = ρ ((c • d) r) := by
  rw [v5_tensorDerivation_scale136, hd]
  change (c ⊗ₜ[k] (1 : N)) * ρ (d r) = ρ (c * d r)
  rw [map_mul, hc]

theorem v5_tensorDerivation_nsmul136 (q : ℕ) (d : Derivation k R R) (x : R ⊗[k] N) :
    tensorDerivation (q • d) x = q • tensorDerivation d x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul r n =>
    change (q • d r) ⊗ₜ[k] n = q • (d r ⊗ₜ[k] n)
    rw [TensorProduct.smul_tmul']

theorem v5_nsmul_coaction_differential136
    (ρ : R →ₐ[B] R ⊗[k] N) (d : Derivation k R R)
    (hd : ∀ r, tensorDerivation d (ρ r) = ρ (d r)) (q : ℕ) (r : R) :
    tensorDerivation (q • d) (ρ r) = ρ ((q • d) r) := by
  rw [v5_tensorDerivation_nsmul136, hd]
  change q • ρ (d r) = ρ (q • d r)
  rw [map_nsmul]
end StrictEUnit
#print axioms StrictEUnit.v5_tensorDerivation_scale136
#print axioms StrictEUnit.v5_scaled_coaction_differential136
#print axioms StrictEUnit.v5_tensorDerivation_nsmul136
#print axioms StrictEUnit.v5_nsmul_coaction_differential136
