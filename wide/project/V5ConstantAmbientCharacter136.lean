import V5AmbientCharacterTransfer136
import V5MixedMarkComparison136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S H : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k H]
/-- For actual derivation constants, the comparison-chart inclusion is the
literal subtype inclusion. Quotient characters therefore give ambient weights
without a remaining comparison-chart identification. -/
def v5ConstantAmbientCharacter136
    (dR : Derivation k R R) (dM : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (hc : ∀ r : R, dR r = 0 → ∃ a : k, algebraMap k R a = r)
    (hd : Function.Bijective (v5MixedConstantMultiplication dM))
    (he : ∀ x, dM (v5MixedComparisonK dM hd x) =
      v5MixedComparisonK dM hd (tensorDerivation dR x))
    (ρ : R →ₐ[B] R ⊗[k] H)
    (hρ : ∀ x, tensorDerivation dM (v5MixedRelativeCoaction ρ x) =
      v5MixedRelativeCoaction ρ (dM x))
    (I : Ideal H) (ε : H →ₐ[k] k) (hI : I ≤ RingHom.ker ε.toRingHom)
    (ΔI : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I))
    (character : V5QuotientUnitCharacter
      (v5_mixedHorizontalMap dR dM hc (v5MixedComparisonK dM hd) he
        (v5MixedRelativeCoaction ρ) hρ) I ε hI ΔI) :
    ∀ u : (derivationConstants dM)ˣ, ∃ χ : (H ⧸ I)ˣ,
      v5MixedRelativeCoaction ((v5CoverRestrictedCoaction135 ρ I).restrictScalars B)
        (u : derivationConstants dM).val =
        (u : derivationConstants dM).val ⊗ₜ[k] (χ : H ⧸ I) ∧
      v5ComponentCounit I ε hI (χ : H ⧸ I) = 1 ∧
      ΔI (χ : H ⧸ I) = (χ : H ⧸ I) ⊗ₜ[k] (χ : H ⧸ I) := by
  intro u
  obtain ⟨χ, hw, hε, hΔ⟩ := v5AmbientCharacterTransfer136 dR dM hc
    (v5MixedComparisonK dM hd) he ρ hρ I ε hI ΔI character u
  rw [v5MixedComparisonK_constant136] at hw
  exact ⟨χ, hw, hε, hΔ⟩
end StrictEUnit
#print axioms StrictEUnit.v5ConstantAmbientCharacter136
