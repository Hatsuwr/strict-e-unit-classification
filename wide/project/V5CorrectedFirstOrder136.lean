import V5NaturalFirstOrder136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k L S W M : Type*} [Field k] [CommRing L] [CommRing S] [CommRing W] [CommRing M]
  [Algebra k L] [Algebra k S] [Algebra k W] [Algebra k M]
  [Algebra L S] [Algebra L W] [Algebra L M]
/-- A horizontal mixed factor does not change the correcting factor's
first-order coefficient; injectivity descends the equation to the solution algebra. -/
theorem v5_corrected_first_order136
    (γ : S →ₐ[L] M) (φ : W →ₐ[L] M) (hφ : Function.Injective φ)
    (dS : Derivation k S S) (dW : Derivation k W W) (dM : Derivation k M M)
    (hγd : ∀ s, dM (γ s) = γ (dS s))
    (hφd : ∀ w, dM (φ w) = φ (dW w))
    (u : M) (hu : dM u = 0) (v : S) (b : W)
    (hb : φ b = u * γ v) (a : L)
    (hv : dS v = algebraMap L S a * v) :
    dW b = algebraMap L W a * b := by
  apply hφ
  calc
    φ (dW b) = dM (φ b) := (hφd b).symm
    _ = dM (u * γ v) := by rw [hb]
    _ = algebraMap L M a * (u * γ v) := by
      rw [dM.leibniz, hu, smul_zero, add_zero, hγd, hv, map_mul, γ.commutes]
      simp only [smul_eq_mul]
      ring
    _ = φ (algebraMap L W a * b) := by rw [map_mul, φ.commutes, hb]

variable {N : Type*} [CommRing N] [Algebra k N] [IsScalarTower k L S]
/-- Combined first-order bridge for an actual marked correction. The only
new geometric input is differential compatibility of the natural coaction. -/
theorem v5_corrected_first_order_from_natural136 [Module.FaithfullyFlat L S]
    (ρ : S →ₐ[L] S ⊗[k] N) (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b)
    (γ : S →ₐ[L] M) (φ : W →ₐ[L] M) (hφ : Function.Injective φ)
    (dS : Derivation k S S) (dW : Derivation k W W) (dM : Derivation k M M)
    (hρd : ∀ s, ρ (dS s) = tensorDerivation dS (ρ s))
    (hγd : ∀ s, dM (γ s) = γ (dS s))
    (hφd : ∀ w, dM (φ w) = φ (dW w))
    (χ : Nˣ) (v : Sˣ) (hv : ρ (v : S) = (v : S) ⊗ₜ[k] (χ : N))
    (u : M) (hu : dM u = 0) (b : W) (hb : φ b = u * γ (v : S)) :
    ∃ a : L, dW b = algebraMap L W a * b := by
  obtain ⟨a,ha⟩ := v5_natural_eigenunit_first_order136 ρ e he dS hρd χ v hv
  exact ⟨a, v5_corrected_first_order136 γ φ hφ dS dW dM hγd hφd u hu v b hb a ha⟩
end StrictEUnit
#print axioms StrictEUnit.v5_corrected_first_order136
#print axioms StrictEUnit.v5_corrected_first_order_from_natural136
