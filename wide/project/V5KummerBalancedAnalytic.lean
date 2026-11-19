import V5ScaledBalancedTensor
import V5PuncturedTensorDifferential

noncomputable section
open scoped TensorProduct
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit

/-- The chosen Kummer map Γ gives the exact scaled compatibility needed by
the balanced construction, without a separate tensor-balance premise. -/
theorem v5_kummer_map_scaled_compatibility129
    {k B D : Type*} [CommRing k] [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] [Algebra B D]
    (δ : Derivation k B B) (dD : Derivation k D D) (q : ℕ)
    (Γ : B →+* D) (hΓ : ∀ b, algebraMap B D b = Γ b)
    (hdΓ : ∀ b, dD (Γ b) = (q : D) * Γ (δ b)) :
    ∀ b, dD (algebraMap B D b) = q • algebraMap B D (δ b) := by
  intro b
  rw [hΓ, hdΓ, hΓ, nsmul_eq_mul]

/-- Construct the balanced Kummer derivation and simultaneously transport it
to the actual punctured analytic Euler derivative. -/
theorem v5_kummer_balanced_analytic129
    {k B S D : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing D]
    [Algebra k B] [Algebra k S] [Algebra k D] [Algebra B S] [Algebra B D]
    [Algebra k (S ⊗[B] D)]
    (δ : Derivation k B B) (dS : Derivation k S S) (dD : Derivation k D D) (q : ℕ)
    (hS : ∀ b, dS (algebraMap B S b) = algebraMap B S (δ b))
    (Γ : B →+* D) (hΓ : ∀ b, algebraMap B D b = Γ b)
    (hdΓ : ∀ b, dD (Γ b) = (q : D) * Γ (δ b))
    (hscalar : ∀ a : k, algebraMap k (S ⊗[B] D) a =
      (algebraMap k S a) ⊗ₜ[B] (1 : D))
    (β : S →+* V5PuncturedFunctions) (ω : D →+* V5PuncturedFunctions)
    (η : S ⊗[B] D →+* V5PuncturedFunctions)
    (hη : ∀ s d z, η (s ⊗ₜ[B] d) z = β s (z^q) * ω d z)
    (hβ : ∀ s, V5HasPuncturedEuler (β s) (β (dS s)))
    (hω : ∀ d, V5HasPuncturedEuler (ω d) (ω (dD d))) :
    ∃ Δ : Derivation k (S ⊗[B] D) (S ⊗[B] D),
      (∀ s d, Δ (s ⊗ₜ[B] d) = (q • dS s) ⊗ₜ[B] d + s ⊗ₜ[B] dD d) ∧
      ∀ x, V5HasPuncturedEuler (η x) (η (Δ x)) := by
  let hD := v5_kummer_map_scaled_compatibility129 δ dD q Γ hΓ hdΓ
  let Δ := v5ScaledBalancedTensorDerivation129 δ dS dD q hS hD hscalar
  have ht s d : Δ (s ⊗ₜ[B] d) = (q • dS s) ⊗ₜ[B] d + s ⊗ₜ[B] dD d :=
    v5ScaledBalancedTensorDerivation129_tmul δ dS dD q hS hD hscalar s d
  exact ⟨Δ, ht, v5_kummer_punctured_tensor_euler_transport q β ω η
    dS.toAddMonoidHom dD.toAddMonoidHom Δ.toAddMonoidHom hη ht hβ hω⟩

end StrictEUnit
#print axioms StrictEUnit.v5_kummer_map_scaled_compatibility129
#print axioms StrictEUnit.v5_kummer_balanced_analytic129
