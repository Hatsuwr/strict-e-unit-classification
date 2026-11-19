import V5MixedWeightTransfer136
import V5QuotientUnitCharacter
import V5CoverRestrictedCoaction135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S C H : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [CommRing S] [CommRing C] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k C] [Algebra k H]
/-- Transfer the entire quotient-character statement through the checked
horizontal square, keeping the quotient-restricted own action literal. -/
def v5AmbientCharacterTransfer136
    (dR : Derivation k R R) (dM : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (hc : ∀ r : R, dR r = 0 → ∃ a : k, algebraMap k R a = r)
    (e : R ⊗[k] C ≃ₐ[k] R ⊗[B] S)
    (he : ∀ x, dM (e x) = e (tensorDerivation dR x))
    (ρ : R →ₐ[B] R ⊗[k] H)
    (hρ : ∀ x, tensorDerivation dM (v5MixedRelativeCoaction ρ x) =
      v5MixedRelativeCoaction ρ (dM x))
    (I : Ideal H) (ε : H →ₐ[k] k) (hI : I ≤ RingHom.ker ε.toRingHom)
    (ΔI : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I))
    (character : V5QuotientUnitCharacter
      (v5_mixedHorizontalMap dR dM hc e he (v5MixedRelativeCoaction ρ) hρ) I ε hI ΔI) :
    ∀ u : Cˣ, ∃ χ : (H ⧸ I)ˣ,
      v5MixedRelativeCoaction ((v5CoverRestrictedCoaction135 ρ I).restrictScalars B)
        (e ((1 : R) ⊗ₜ[k] (u : C))) =
        e ((1 : R) ⊗ₜ[k] (u : C)) ⊗ₜ[k] (χ : H ⧸ I) ∧
      v5ComponentCounit I ε hI (χ : H ⧸ I) = 1 ∧
      ΔI (χ : H ⧸ I) = (χ : H ⧸ I) ⊗ₜ[k] (χ : H ⧸ I) := by
  intro u
  obtain ⟨χ, hw, hε, hΔ⟩ := character u
  exact ⟨χ, v5MixedHorizontalOwnWeight136 dR dM hc e he ρ hρ
    (Ideal.Quotient.mkₐ k I) u χ hw, hε, hΔ⟩
end StrictEUnit
#print axioms StrictEUnit.v5AmbientCharacterTransfer136
