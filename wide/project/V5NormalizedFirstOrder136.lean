import V5CorrectedFirstOrder136
import V5MarkedWeightNormalization
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k S N : Type*} [Field k] [CommRing S] [CommRing N] [Algebra k S] [Algebra k N]
theorem v5NormalizedEigenweight136
    (p : S →ₐ[k] k) (ρ : S →ₐ[k] S ⊗[k] N) (χ : N) (v : Sˣ)
    (hv : ρ (v : S) = (v : S) ⊗ₜ[k] χ) :
    ρ (v5NormalizeMarkedUnit p v : S) = (v5NormalizeMarkedUnit p v : S) ⊗ₜ[k] χ := by
  have hw : ρ (v : S) =
      (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] N) (v : S) * ((1 : S) ⊗ₜ[k] χ) := by
    rw [hv]
    simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
  have h := v5NormalizeMarkedUnit_weight p ρ Algebra.TensorProduct.includeLeft
    ((1 : S) ⊗ₜ[k] χ) v hw
  simpa only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul] using h

variable {L W M : Type*} [CommRing L] [CommRing W] [CommRing M]
  [Algebra k L] [Algebra k W] [Algebra k M]
  [Algebra L S] [Algebra L W] [Algebra L M] [IsScalarTower k L S]
theorem v5NormalizedCorrectedFirstOrder136 [Module.FaithfullyFlat L S]
    (ρ : S →ₐ[L] S ⊗[k] N) (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b)
    (γ : S →ₐ[L] M) (φ : W →ₐ[L] M) (hφ : Function.Injective φ)
    (dS : Derivation k S S) (dW : Derivation k W W) (dM : Derivation k M M)
    (hρd : ∀ s, ρ (dS s) = tensorDerivation dS (ρ s))
    (hγd : ∀ s, dM (γ s) = γ (dS s))
    (hφd : ∀ w, dM (φ w) = φ (dW w))
    (p : S →ₐ[k] k) (χ : Nˣ) (v : Sˣ) (hv : ρ (v : S) = (v : S) ⊗ₜ[k] (χ : N))
    (u : M) (hu : dM u = 0) (b : W)
    (hb : φ b = u * γ (v5NormalizeMarkedUnit p v : S)) :
    ∃ a : L, dW b = algebraMap L W a * b :=
  v5_corrected_first_order_from_natural136 ρ e he γ φ hφ dS dW dM hρd hγd hφd
    χ (v5NormalizeMarkedUnit p v)
    (v5NormalizedEigenweight136 p (ρ.restrictScalars k) χ v hv) u hu b hb
end StrictEUnit
#print axioms StrictEUnit.v5NormalizedEigenweight136
#print axioms StrictEUnit.v5NormalizedCorrectedFirstOrder136
