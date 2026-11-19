import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k M N : Type*} [Field k] [CommRing M] [CommRing N]
  [Algebra k M] [Algebra k N]
theorem v5ApplyAmbientCharacter136
    {δ : M →ₐ[k] M ⊗[k] N} {Δ : N →ₐ[k] N ⊗[k] N} {ε : N →ₐ[k] k}
    {u : Mˣ} {P : Nˣ → Prop}
    (hlift : ∀ (χ : Nˣ), Δ (χ : N) = (χ : N) ⊗ₜ[k] (χ : N) → ε (χ : N) = 1 →
      δ (u : M) = (u : M) ⊗ₜ[k] (χ : N) → P χ)
    (hchar : ∃ χ : Nˣ, δ (u : M) = (u : M) ⊗ₜ[k] (χ : N) ∧
      ε (χ : N) = 1 ∧ Δ (χ : N) = (χ : N) ⊗ₜ[k] (χ : N)) :
    ∃ χ : Nˣ, P χ := by
  obtain ⟨χ,hw,hε,hχ⟩ := hchar
  exact ⟨χ,hlift χ hχ hε hw⟩
end StrictEUnit
#print axioms StrictEUnit.v5ApplyAmbientCharacter136
