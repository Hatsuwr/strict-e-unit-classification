import V5CanonicalPIDUnit135
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit

theorem v5_explicit_inverse_character135
    {k H : Type*} [Field k] [CommRing H] [Algebra k H]
    (Δ : H →ₐ[k] H ⊗[k] H) (ε : H →ₐ[k] k)
    (χ : Hˣ) (hχ : Δ (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hε : ε (χ : H) = 1) :
    Δ (↑χ⁻¹ : H) = (↑χ⁻¹ : H) ⊗ₜ[k] (↑χ⁻¹ : H) ∧ ε (↑χ⁻¹ : H) = 1 := by
  constructor
  · apply (χ.isUnit.map Δ).mul_left_cancel
    rw [← map_mul, Units.mul_inv, map_one, hχ, Algebra.TensorProduct.tmul_mul_tmul,
      Units.mul_inv]
    rfl
  · have h := congrArg ε (Units.mul_inv χ)
    simpa only [map_mul, hε, map_one, one_mul] using h

attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B S H : Type*} [Field k] [CommRing B] [IsDomain B]
  [IsPrincipalIdealRing B] [Algebra k B]
  [CommRing S] [Nontrivial S] [Algebra B S] [Algebra k S]
  [IsScalarTower k B S] [Module.FaithfullyFlat B S]
  [CommRing H] [Algebra k H]
theorem v5_pid_opposite_weight_unit_of_canonical_chart135
    (Δ : H →ₐ[k] H ⊗[k] H) (ε : H →ₐ[k] k)
    (hleft : ∀ h, v5ComponentLeftScalar ε (Δ h) = h)
    (ρ : S →ₐ[B] S ⊗[k] H)
    (e : S ⊗[B] S ≃ₐ[S] S ⊗[k] H)
    (he : ∀ a b, e (a ⊗ₜ[B] b) = a • ρ b)
    (hcoassoc : ∀ s, Algebra.TensorProduct.assoc k S H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ s)) =
      Algebra.TensorProduct.map (AlgHom.id S S) Δ (ρ s))
    (χ : Hˣ) (hχ : Δ (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hε : ε (χ : H) = 1) :
    ∃ v : S, ρ v = v ⊗ₜ[k] (↑χ⁻¹ : H) ∧ IsUnit v := by
  obtain ⟨hχi,hεi⟩ := v5_explicit_inverse_character135 Δ ε χ hχ hε
  exact v5_pid_weight_unit_of_canonical_chart135 Δ ε hleft ρ e he hcoassoc χ⁻¹ hχi hεi
end StrictEUnit
#print axioms StrictEUnit.v5_explicit_inverse_character135
#print axioms StrictEUnit.v5_pid_opposite_weight_unit_of_canonical_chart135
